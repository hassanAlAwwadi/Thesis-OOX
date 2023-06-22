use lib::{self, verify, Options, SourcePos, SymResult};

#[test]
fn instance_of() {
    let k = 50;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test1",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test1_invalid",
            options
        ).unwrap().0,
        SymResult::Invalid(SourcePos::new(7, 27, 0))
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test1b_invalid",
            options
        ).unwrap().0,
        SymResult::Invalid(SourcePos::new(23, 20, 0))
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test2",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test3_invalid",
            options
        ).unwrap().0,
        SymResult::Invalid(SourcePos::new(51, 20, 0))
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test3a",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(
            &["./examples/casting/instanceof.oox"],
            "A",
            "test3b",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    // not yet implemented:

    // assert_eq!(verify(
    //     "./examples/casting/instanceof.oox"],
    //     "A",
    //     "test4",
    //     options
    // ), Ok(SymResult::Valid));

    // assert_eq!(verify(
    //     "./examples/casting/instanceof.oox"],
    //     "A",
    //     "test4_invalid",
    //     options
    // ), Ok(SymResult::Valid));
}

#[test]
fn class_cast() {
    let k = 50;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(
            &["./examples/casting/class_cast.oox"],
            "X1",
            "test1",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(
            &["./examples/casting/class_cast.oox"],
            "X1",
            "test1a",
            options
        ).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(
            &["./examples/casting/class_cast.oox"],
            "X1",
            "test1a_invalid",
            options
        ).unwrap().0,
        SymResult::Invalid(SourcePos::new(37, 21, 0))
    );

    assert_eq!(
        verify(
            &["./examples/casting/class_cast.oox"],
            "X1",
            "test1b_invalid",
            options
        ).unwrap().0,
        SymResult::Invalid(SourcePos::new(45, 21, 0))
    );
}
