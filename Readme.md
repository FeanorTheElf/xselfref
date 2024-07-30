# x-selfref

This basically a copy/fork of the MIT-licensed [selfref](https://docs.rs/selfref/latest/selfref/) library (by another author), with a few additions made by me.

# Introduction of selfref

An experimental approach to self-referential structs in Rust.

This crate provides an alternative approach to self-referential structs,
where instead of providing you with a macro or framework where you define
a self-referential struct and it handles all of the details for you, we try
to expose the abstractions and building blocks for making self-referential
structs work well in safe Rust.

For example, a [`Holder`] is a safe wrapper around a self-referential
struct, providing safe APIs for constructing and manipulating a
self-referential struct. However, and unlike other self-referential crates,
it does not dictate the backing storage of the struct. The [`Opaque`] trait
is used to identify a self-referential struct for use with a [`Holder`] -
since Rust does not support higher kinded types (HKTs), this crate uses
generic associated types (GATs) as a workaround.

To use the crate, first define a self-referential struct in plain Rust:

```rust
use std::cell::Cell;

// Your self-referential struct.
struct MySelfRefStruct<'this> {
    // Rust uses RAII-like struct construction, as a result this must be
    // somehow initialized after the struct. We can use an Option in a Cell
    // for this.
    this: Cell<Option<&'this MySelfRefStruct<'this>>>,
}
```

Then, define a type to implement the `Opaque`. This can be done
automatically with the `opaque` macro:

```rust
# use std::cell::Cell;
# // Your self-referential struct.
# struct MySelfRefStruct<'this> {
#     // Rust uses RAII-like struct construction, as a result this must be
#     // somehow initialized after the struct. We can use an Option in a Cell
#     // for this.
#     this: Cell<Option<&'this MySelfRefStruct<'this>>>,
# }

use xselfref::opaque;

// A "marker type" that implements `Opaque`.
// This follows the "type family" GAT pattern.
struct MySelfRefStructKey;

opaque! {
    impl Opaque for MySelfRefStructKey {
        type Kind<'this> = MySelfRefStruct<'this>;
    }
}

// Alternatively, it is possible to implement `Opaque` on, for example,
// `MySelfRefStruct<'static>`, but the added lifetime adds verbosity which
// may be considered unnecessary/undesired.
```

Now you can construct a `Holder` and pick a storage for it. For example,
in a `Box`:

```rust
# use std::cell::Cell;
# // Your self-referential struct.
# struct MySelfRefStruct<'this> {
#     // Rust uses RAII-like struct construction, as a result this must be
#     // somehow initialized after the struct. We can use an Option in a Cell
#     // for this.
#     this: Cell<Option<&'this MySelfRefStruct<'this>>>,
# }
# use xselfref::opaque;
# // A "marker type" that implements `Opaque`.
# // This follows the "type family" GAT pattern.
# struct MySelfRefStructKey;
# opaque! {
#     impl Opaque for MySelfRefStructKey {
#         type Kind<'this> = MySelfRefStruct<'this>;
#     }
# }
# // Alternatively, it is possible to implement `Opaque` on, for example,
# // `MySelfRefStruct<'static>`, but the added lifetime adds verbosity which
# // may be considered unnecessary/undesired.

use xselfref::Holder;

fn main() {
    // first, construct the struct
    let holder = Box::pin(Holder::<'_, MySelfRefStructKey>::new_with(
        |foo| foo.build({
            MySelfRefStruct {
                this: Cell::new(None)
            }
        })
    ));

    // then, build the self-reference
    holder.as_ref().operate_in(
        |this| {
            this.this.set(Some(this.get_ref()));
        }
    );
}
```

# Examples

This is a more complex example borrowing from an external lifetime:

```rust
use core::cell::Cell;
use core::marker::PhantomData;
use core::pin::Pin;

use xselfref::Holder;
use xselfref::opaque;

struct Foo<'a, 'b: 'a> {
    foo: Cell<Option<&'a Foo<'a, 'b>>>,
    t: &'b str,
}

struct FooKey<'b>(PhantomData<&'b str>);
opaque! {
    impl['b] Opaque for FooKey<'b> {
        type Kind<'a> = Foo<'a, 'b>;
    }
}

fn main() {
    // a non-'static &str
    let stack_array: [u8; 5] = *b"hello";
    let stack_str = core::str::from_utf8(&stack_array).unwrap();

    // construct the struct
    let holder = Box::pin(Holder::<'_, FooKey<'_>>::new_with(|foo| {
        foo.build(Foo {
            foo: Default::default(),
            t: stack_str,
        })
    }));

    holder.as_ref().operate_in(|foo| {
        foo.foo.set(Some(foo.get_ref()));
    });
}
```

# Features

Due to [PhantomData is unsound](https://github.com/rust-lang/rust/issues/102810)
we currently require the following features for `T: ?Sized` support in
`xselfref::opaque!`:

- `alloc` - `xselfref::opaque!` for `T: ?Sized` is provided by `Box`.
- `nightly` - `xselfref::opaque!` for `T: ?Sized` is provided by a *wrapper*
    around `PhantomData`, which works around the above issue. we call this
    "PhantomDrop".

When enabling both features, `nightly` takes over and we use the wrapper
always. This doesn't make a significant difference since the generated UB
check is dead code anyway, but `PhantomDrop` doesn't depend on `alloc` and
can be used in `no_std` environments.

If not using either feature, `T: ?Sized` support requires `unsafe`ly
implementing `Opaque`.

Note that we do **not** enable any features by default! We assume most
folks aren't coming to this crate for its `T: ?Sized` support, so these are
the best defaults for crates to depend on. If they do need the `?Sized`
support they can just enable one of these (probably `alloc`).
