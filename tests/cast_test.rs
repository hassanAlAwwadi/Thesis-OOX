use lib::{self, verify, Options, SymResult, SourcePos};

#[test]
fn instance_of() {
    let k = 50;
    let options = Options::default_with_k(k);

    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test1",
        options
    ), Ok(SymResult::Valid));

    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test1_invalid",
        options
    ), Ok(SymResult::Invalid(SourcePos::new(7, 27))));



    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test1b_invalid",
        options
    ), Ok(SymResult::Invalid(SourcePos::new(23, 20))));

    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test2",
        options
    ), Ok(SymResult::Valid));


    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test3_invalid",
        options
    ), Ok(SymResult::Invalid(SourcePos::new(51, 20))));


    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test3a",
        options
    ), Ok(SymResult::Valid));

    assert_eq!(verify(
        "./examples/casting/instanceof.oox",
        "A",
        "test3b",
        options
    ), Ok(SymResult::Valid));

    // not yet implemented:

    // assert_eq!(verify(
    //     "./examples/casting/instanceof.oox",
    //     "A",
    //     "test4",
    //     options
    // ), Ok(SymResult::Valid));

    // assert_eq!(verify(
    //     "./examples/casting/instanceof.oox",
    //     "A",
    //     "test4_invalid",
    //     options
    // ), Ok(SymResult::Valid));
}


#[test]
fn class_cast() {
    let k = 50;
    let options = Options::default_with_k(k);
    
    assert_eq!(verify(
        "./examples/casting/class_cast.oox",
        "X1",
        "test1",
        options
    ), Ok(SymResult::Valid));

    assert_eq!(verify(
        "./examples/casting/class_cast.oox",
        "X1",
        "test1_invalid",
        options
    ), Ok(SymResult::Invalid(SourcePos::new(29, 21))));
}