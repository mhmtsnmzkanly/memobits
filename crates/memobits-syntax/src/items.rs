//! Top-level function, import, and type declaration parsing.
use super::{
    Access, AssociatedTypeBinding, Field, GenericParameter, GenericParameterKind, InterfaceMethod,
    Item, ItemKind, Node, PResult, Parameter, Parser, Type, TypeArgument, TypeDefinition,
    UseMember, Variant, WhereBound,
};

impl Parser {
    pub(super) fn item(&mut self) -> PResult<Item> {
        let start = self.current().span.start;
        let public = self.eat("pub");
        let mut item_span = None;
        let test_start = self.current().span;
        let test = self.at("test") && self.next_at("fn");
        if test {
            self.bump();
            if public {
                self.diagnostics.push(super::diagnostic(
                    2,
                    test_start,
                    "a test function cannot be `pub`; write `test fn name() { ... }`",
                ));
            }
        }
        let external = self.eat("extern");
        let kind = if self.eat("fn") {
            let name = self.name()?;
            let generic_parameters = self.generic_parameters()?;
            if test && !generic_parameters.is_empty() {
                self.diagnostics.push(super::diagnostic(
                    2,
                    generic_parameters[0].span,
                    format!("test function '{name}' cannot have generic parameters"),
                ));
            }
            self.expect("(")?;
            let mut parameters = Vec::new();
            while !self.at(")") && !self.eof() {
                let start = self.current().span.start;
                let mutable = self.eat("var");
                let name = self.name()?;
                self.expect(":")?;
                let access = self.access();
                let ty = self.ty()?;
                parameters.push(Parameter {
                    span: self.span(start),
                    mutable,
                    name,
                    access,
                    ty,
                });
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
            if test {
                if let Some(parameter) = parameters.first() {
                    self.diagnostics.push(super::diagnostic(
                        2,
                        parameter.span,
                        format!("test function '{name}' cannot take parameters"),
                    ));
                }
            }
            let result = if self.eat("->") {
                Some(self.ty()?)
            } else {
                None
            };
            if let (true, Some(result)) = (test, &result) {
                if result.path != ["Unit"] || !result.arguments.is_empty() {
                    self.diagnostics.push(super::diagnostic(
                        2,
                        result.span,
                        format!("test function '{name}' must not return a value; remove the result type"),
                    ));
                }
            }
            let bounds = self.where_bounds()?;
            let body = if external {
                self.expect(";")?;
                super::Block {
                    span: self.span(start),
                    statements: Vec::new(),
                    tail: None,
                }
            } else {
                self.block()?
            };
            ItemKind::Function {
                public,
                external,
                test,
                name,
                generic_parameters,
                bounds,
                parameters,
                result,
                body,
            }
        } else if self.eat("const") {
            let name = self.name()?;
            if !self.at(":") {
                return self.fail(format!(
                    "a const needs a type annotation: `const {name}: T = value;`"
                ));
            }
            self.bump();
            let ty = self.ty()?;
            self.expect("=")?;
            let value = self.expr(0)?;
            self.expect(";")?;
            ItemKind::Const {
                public,
                name,
                ty,
                value,
            }
        } else if self.eat("use") {
            let path = self.import_path()?;
            let (alias, group) = if self.eat("::") {
                self.expect("{")?;
                let mut members = Vec::new();
                while !self.at("}") && !self.eof() {
                    let name = self.name()?;
                    let alias = if self.eat("as") {
                        Some(self.name()?)
                    } else {
                        None
                    };
                    members.push(UseMember { name, alias });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("}")?;
                if members.is_empty() {
                    return self.fail("a grouped import must contain at least one symbol");
                }
                (None, members)
            } else {
                let alias = if self.eat("as") {
                    Some(self.name()?)
                } else {
                    None
                };
                (alias, Vec::new())
            };
            self.expect(";")?;
            ItemKind::Use {
                public,
                path,
                alias,
                group,
            }
        } else if self.eat("type") {
            let name = self.name()?;
            let generic_parameters = self.generic_parameters()?;
            let bounds = self.where_bounds()?;
            let base = if self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            if base.is_some() && !self.at("{") {
                return self.fail("a derived error type requires a field body");
            }
            let definition = if self.eat("=") {
                let ty = self.ty()?;
                self.expect(";")?;
                TypeDefinition::Alias(ty)
            } else if self.eat("{") {
                let mut fields = Vec::new();
                while !self.at("}") && !self.eof() {
                    let start = self.current().span.start;
                    let public = self.eat("pub");
                    let name = self.name()?;
                    self.expect(":")?;
                    let ty = self.ty()?;
                    fields.push(Field {
                        span: self.span(start),
                        public,
                        name,
                        ty,
                    });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("}")?;
                TypeDefinition::Struct(fields)
            } else if self.eat("[") {
                let mut variants = Vec::new();
                while !self.at("]") && !self.eof() {
                    let start = self.current().span.start;
                    let name = self.name()?;
                    let mut payload = Vec::new();
                    if self.eat("(") {
                        while !self.at(")") && !self.eof() {
                            payload.push(self.ty()?);
                            if !self.eat(",") {
                                break;
                            }
                        }
                        self.expect(")")?;
                    }
                    variants.push(Variant {
                        span: self.span(start),
                        name,
                        payload,
                    });
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("]")?;
                TypeDefinition::Enum(variants)
            } else if self.eat(";") {
                TypeDefinition::Bodyless
            } else {
                return self.fail("expected '=', '{', '[', or ';' after type name");
            };
            let declaration_span = self.span(start);
            if self.at("extend") && self.next_at("{") {
                if matches!(&definition, TypeDefinition::Alias(_)) {
                    return self.fail("inherent extensions require a nominal type declaration");
                }
                let extension_start = self.current().span.start;
                self.bump();
                let (associated_types, methods) = self.interface_methods(true)?;
                if !associated_types.is_empty() {
                    return self.fail("associated type bindings require an interface extension");
                }
                self.pending.push(Node {
                    span: self.span(extension_start),
                    kind: ItemKind::InherentExtension {
                        public,
                        target: Type {
                            span: declaration_span,
                            path: vec![name.clone()],
                            arguments: generic_parameters
                                .iter()
                                .map(|parameter| match &parameter.kind {
                                    GenericParameterKind::Type => TypeArgument::Type(Type {
                                        span: parameter.span,
                                        path: vec![parameter.name.clone()],
                                        arguments: Vec::new(),
                                    }),
                                    GenericParameterKind::Const(_) => {
                                        TypeArgument::Const(parameter.name.clone())
                                    }
                                })
                                .collect(),
                        },
                        generic_parameters: generic_parameters.clone(),
                        methods,
                    },
                });
            }
            item_span = Some(declaration_span);
            ItemKind::Type {
                public,
                name,
                generic_parameters,
                bounds,
                definition,
                base,
            }
        } else if self.eat("interface") {
            let name = self.name()?;
            let (associated_type_items, methods) = self.interface_methods(false)?;
            let associated_types = associated_type_items
                .into_iter()
                .map(|binding| binding.name)
                .collect();
            ItemKind::Interface {
                public,
                name,
                associated_types,
                methods,
            }
        } else if self.eat("extend") {
            let target = self.ty()?;
            if self.eat("of") {
                let interface = self.ty()?;
                let (associated_types, methods) = self.interface_methods(true)?;
                ItemKind::Extension {
                    public,
                    target,
                    interface,
                    associated_types,
                    methods,
                }
            } else {
                let (associated_types, methods) = self.interface_methods(true)?;
                if !associated_types.is_empty() {
                    return self.fail("associated type bindings require an interface extension");
                }
                ItemKind::InherentExtension {
                    public,
                    target,
                    generic_parameters: Vec::new(),
                    methods,
                }
            }
        } else {
            return self.fail("expected function, type, interface, extension, or use declaration");
        };
        Ok(Node {
            span: item_span.unwrap_or_else(|| self.span(start)),
            kind,
        })
    }

    fn generic_parameters(&mut self) -> PResult<Vec<GenericParameter>> {
        if !self.eat("<") {
            return Ok(Vec::new());
        }
        let mut parameters = Vec::new();
        while !self.at(">") && !self.eof() {
            let start = self.current().span.start;
            let is_const = self.eat("const");
            let name = self.name()?;
            let kind = if is_const {
                self.expect(":")?;
                GenericParameterKind::Const(self.ty()?)
            } else {
                GenericParameterKind::Type
            };
            parameters.push(GenericParameter {
                span: self.span(start),
                name,
                kind,
            });
            if !self.eat(",") {
                break;
            }
        }
        self.expect(">")?;
        Ok(parameters)
    }

    fn where_bounds(&mut self) -> PResult<Vec<WhereBound>> {
        if !self.eat("where") {
            return Ok(Vec::new());
        }
        let mut bounds = Vec::new();
        loop {
            let start = self.current().span.start;
            let parameter = self.name()?;
            self.expect(":")?;
            let interface = self.ty()?;
            bounds.push(WhereBound {
                span: self.span(start),
                parameter,
                interface,
            });
            if !self.eat(",") {
                break;
            }
        }
        Ok(bounds)
    }

    fn interface_methods(
        &mut self,
        implementation: bool,
    ) -> PResult<(Vec<AssociatedTypeBinding>, Vec<InterfaceMethod>)> {
        self.expect("{")?;
        let mut associated_types = Vec::new();
        let mut methods = Vec::new();
        while !self.at("}") && !self.eof() {
            let start = self.current().span.start;
            if self.eat("type") {
                let name = self.name()?;
                let ty = if implementation {
                    self.expect("=")?;
                    let ty = self.ty()?;
                    self.expect(";")?;
                    Some(ty)
                } else {
                    self.expect(";")?;
                    None
                };
                associated_types.push(AssociatedTypeBinding {
                    span: self.span(start),
                    name,
                    ty,
                });
                continue;
            }
            let public = self.eat("pub");
            self.expect("fn")?;
            let name = self.name()?;
            self.expect("(")?;
            let receiver = if self.eat("borrow") {
                Access::Borrow
            } else if self.eat("share") {
                Access::Share
            } else {
                Access::Owned
            };
            self.expect("self")?;
            let mut parameters = Vec::new();
            while self.eat(",") && !self.at(")") && !self.eof() {
                let parameter_start = self.current().span.start;
                let mutable = self.eat("var");
                let name = self.name()?;
                self.expect(":")?;
                let access = self.access();
                let ty = self.ty()?;
                parameters.push(Parameter {
                    span: self.span(parameter_start),
                    mutable,
                    name,
                    access,
                    ty,
                });
            }
            self.expect(")")?;
            let result = if self.eat("->") {
                Some(self.ty()?)
            } else {
                None
            };
            let body = if implementation {
                Some(self.block()?)
            } else {
                self.expect(";")?;
                None
            };
            methods.push(InterfaceMethod {
                span: self.span(start),
                public,
                name,
                receiver,
                parameters,
                result,
                body,
            });
        }
        self.expect("}")?;
        Ok((associated_types, methods))
    }
}
