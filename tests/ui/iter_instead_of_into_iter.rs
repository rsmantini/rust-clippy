#![warn(clippy::iter_instead_of_into_iter)]

fn main() {
    let v0: Vec<i32> = Vec::new();
    // Should trigger
    let _: Vec<_> = v0.iter().collect();

    let v1: Vec<i32> = Vec::new();
    for _ in 0..200 {
        // should not trigger
        let _: i32 = v1.iter().sum();
    }

    let v2: Vec<i32> = Vec::new();
    // should trigger
    aux(v2.iter().sum());

    let v3: Vec<i32> = Vec::new();
    let func = || -> i32 { v3.iter().sum() };
    // should not trigger
    let _: i32 = v3.iter().sum();
    let _ = func(); // v3 used inside the lambda

    let v4: Vec<i32> = Vec::new();
    // should trigger
    let mut v4_iter = v4.iter();
    let _ = v4_iter.next();
    let _ = v4_iter.next();

    let v5: Vec<i32> = Vec::new();
    // should not trigger
    let _: Vec<_> = v5.iter().collect();
    // should trigger
    let _: i32 = v5.iter().sum();

    let v6: Vec<i32> = Vec::new();
    // should not trigger
    foo(v6.iter());

    let v7: Vec<String> = vec!["a".into()];
    //should not trigger
    let _: Vec<&str> = v7.iter().map(|x| x.as_ref()).collect();

    let bar = Bar {};
    // should not trigger
    let _ = bar.iter();
}

fn aux(_: i32) {}

struct Bar;

impl Bar {
    fn iter(&self) -> bool {
        true
    }
}

fn foo<'a> (_iter: impl Iterator<Item = &'a i32>) {

}