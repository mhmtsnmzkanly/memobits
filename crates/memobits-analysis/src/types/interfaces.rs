//! Interface-selected receiver calls: qualified interface identity and applicable
//! extension candidate selection.
use super::*;

impl Checker {
    pub(super) fn interface_selected_call(
        &mut self,
        expr: &Expr,
        id: Option<ExprId>,
        callee: &Expr,
        arguments: &[Expr],
        interface: &Type,
    ) -> Ty {
        let interface_key = qualified_interface(&self.module, &self.imports, interface);
        let ExprKind::Field {
            base,
            name: method_name,
        } = &callee.kind
        else {
            self.error(
                7,
                expr.span,
                "interface selection requires a receiver method call",
            );
            return Ty::Error;
        };
        self.allow_array_value(base);
        let receiver = read_type(self.expr(base, None));
        let mut matching = self
            .extension_candidates
            .iter()
            .filter(|candidate| {
                candidate.target == receiver
                    && candidate.interface.as_deref() == Some(interface_key.as_str())
                    && candidate.methods.contains_key(method_name)
            })
            .cloned()
            .collect::<Vec<_>>();
        if let Some(evidence) = self.generic_evidence.iter().find(|evidence| {
            evidence.interface == interface_key && evidence.candidate.target == receiver
        }) {
            if evidence.candidate.methods.contains_key(method_name) {
                matching = vec![evidence.candidate.clone()];
            }
        }
        let applicable = matching
            .iter()
            .filter(|candidate| candidate.visible)
            .cloned()
            .collect::<Vec<_>>();
        if applicable.is_empty() && !matching.is_empty() {
            let locations = matching
                .iter()
                .map(|candidate| {
                    format!(
                        "{}:{}..{}",
                        candidate.module, candidate.span.start, candidate.span.end
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            self.error(
                7,
                expr.span,
                format!("matching extension is private or inactive: {locations}"),
            );
            return Ty::Error;
        }
        if applicable.is_empty() {
            self.error(
                7,
                expr.span,
                format!(
                    "no visible extension implements '{}::{}' for {}",
                    interface_key,
                    method_name,
                    name(&receiver)
                ),
            );
            return Ty::Error;
        }
        if applicable.len() > 1 {
            let locations = applicable
                .iter()
                .map(|candidate| {
                    format!(
                        "{}:{}..{}",
                        candidate.module, candidate.span.start, candidate.span.end
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            self.error(
                7,
                expr.span,
                format!("ambiguous extension selection; candidates: {locations}"),
            );
            return Ty::Error;
        }
        let candidate = &applicable[0];
        let (receiver_access, parameters, result, _method_span, function) =
            candidate.methods.get(method_name).cloned().unwrap();
        self.ensure(&receiver, &candidate.target, base.span);
        if receiver_access == Access::Owned {
            self.reject_extraction(base, &receiver);
        }
        if parameters.len() != arguments.len() {
            self.error(
                10,
                expr.span,
                format!(
                    "expected {} method arguments, found {}",
                    parameters.len(),
                    arguments.len()
                ),
            );
        }
        for (argument, parameter) in arguments.iter().zip(&parameters) {
            let actual = self.expr(argument, Some(&parameter.ty));
            self.ensure(&actual, &parameter.ty, argument.span);
        }
        if let (Some(facts), Some(expression)) = (self.facts.as_mut(), id) {
            let mut function_parameters = vec![FunctionParameter {
                access: ir_access(receiver_access),
                ty: candidate.target.clone(),
            }];
            function_parameters.extend(parameters.clone());
            let signature =
                match ir_type(&Ty::Function(function_parameters, Box::new(result.clone()))) {
                    Some(IrType::Function(signature)) => signature,
                    _ => {
                        self.error(
                            7,
                            expr.span,
                            "selected extension signature is outside the executable type subset",
                        );
                        return Ty::Error;
                    }
                };
            facts.selected_calls.push(SelectedCall {
                expression,
                function,
                receiver_access,
                signature,
            });
        }
        return result;
    }
}

pub(super) fn qualified_interface(
    module: &str,
    imports: &HashMap<String, String>,
    ty: &Type,
) -> String {
    let path = if ty.path.len() == 1 {
        imports
            .get(&ty.path[0])
            .cloned()
            .unwrap_or_else(|| format!("{module}::{}", ty.path[0]))
    } else if let Some(import) = imports.get(&ty.path[0]) {
        format!("{import}::{}", ty.path[1..].join("::"))
    } else {
        ty.path.join("::")
    };
    path.strip_prefix("self::").unwrap_or(&path).to_owned()
}
