use pom::parser::*;

use super::*;

pub(super) fn interface<'a>() -> Parser<'a, Token<'a>, Interface> {
    ((keyword("interface") * identifier())
        + extends_many().opt().map(|x| x.unwrap_or(Vec::new()))
        + punct("{") * interface_member().repeat(0..)
        - punct("}"))
    .map(|((name, extends), members)| Interface {
        name,
        extends,
        members,
    })
}

fn interface_member<'a>() -> Parser<'a, Token<'a>, InterfaceMember> {
    let member = type_() + identifier() + parameters();

    (member + (punct(";").map(|_| Option::None) | body().map(Option::Some))).map(
        |(((type_, name), parameters), body)| {
            match body {
                Some(body) => InterfaceMember::DefaultMethod(
                    Method {
                        is_static: false,
                        return_type: type_,
                        name,
                        params: parameters,
                        specification: Default::default(), // not yet implemented
                        body: body.into(),
                        info: SourcePos::UnknownPosition,
                    }
                    .into(),
                ),
                None => InterfaceMember::AbstractMethod(
                    AbstractMethod {
                        is_static: false,
                        return_type: type_,
                        name,
                        params: parameters,
                        specification: Default::default(), // not yet implemented
                    }
                    .into(),
                ),
            }
        },
    )
}

#[test]
fn parse_interface() {
    let file_content = "
    interface Animal extends Eater {
        void animalSound();
    }";

    let tokens = tokens(&file_content, 0).unwrap();
    dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (interface() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}
