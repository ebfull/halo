#[macro_use]
mod util;

mod curves;
mod fields;

pub use curves::*;
pub use fields::*;

// TODO: This should be upstreamed to subtle.
// See https://github.com/dalek-cryptography/subtle/pull/48
trait CtOptionExt<T> {
    /// Calls f() and either returns self if it contains a value,
    /// or returns the output of f() otherwise.
    fn or_else<F: FnOnce() -> subtle::CtOption<T>>(self, f: F) -> subtle::CtOption<T>;
}

impl<T: subtle::ConditionallySelectable> CtOptionExt<T> for subtle::CtOption<T> {
    fn or_else<F: FnOnce() -> subtle::CtOption<T>>(self, f: F) -> subtle::CtOption<T> {
        let is_none = self.is_none();
        let f = f();

        subtle::ConditionallySelectable::conditional_select(&self, &f, is_none)
    }
}
