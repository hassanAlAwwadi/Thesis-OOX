use pom::parser::*;

use super::*;

pub(super) fn interface<'a>() -> Parser<'a, Token<'a>, UnresolvedInterface> {
    ((keyword("interface") * identifier())
        + extends_many().opt().map(|x| x.unwrap_or(Vec::new()))
        + punct("{") * interface_member().repeat(0..)
        - punct("}"))
    .map(|((name, extends), members)| UnresolvedInterface {
        name,
        extends,
        members,
    })
}

fn interface_member<'a>() -> Parser<'a, Token<'a>, Rc<InterfaceMember>> {
    let member = type_() + identifier() + parameters();

    (member + (punct(";").map(|_| Option::None) | body().map(Option::Some)))
        .map(|(((type_, name), parameters), body)| {
            InterfaceMember::Method(InterfaceMethod {
                type_,
                name,
                parameters,
                body,
            })
        })
        .map(Rc::new)
}

#[test]
fn parse_interface() {
    let file_content = "
    interface Animal extends Eater {
        void animalSound();
    }";

    let tokens = tokens(&file_content);
    dbg!(&tokens);
    let as_ref = tokens.as_slice();
    // //dbg!(as_ref);
    let c = (interface() - end()).parse(&as_ref);
    // //dbg!(&c);
    c.unwrap(); // should not panic;
}
