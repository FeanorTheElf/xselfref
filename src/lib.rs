// The core of this code is taken from the `selfref` library, with the following copyright:
//
// SelfRef - Pain-free self-referential pinned types
// Copyright (C) 2022 Soni L.
// This software is made with love by a queer trans person.
// With help from quinedot
//
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_std]

//! An experimental approach to self-referential structs in Rust.
//!
//! This crate provides an alternative approach to self-referential structs,
//! where instead of providing you with a macro or framework where you define
//! a self-referential struct and it handles all of the details for you, we try
//! to expose the abstractions and building blocks for making self-referential
//! structs work well in safe Rust.
//!
//! For example, a [`Holder`] is a safe wrapper around a self-referential
//! struct, providing safe APIs for constructing and manipulating a
//! self-referential struct. However, and unlike other self-referential crates,
//! it does not dictate the backing storage of the struct. The [`Opaque`] trait
//! is used to identify a self-referential struct for use with a [`Holder`] -
//! since Rust does not support higher kinded types (HKTs), this crate uses
//! generic associated types (GATs) as a workaround.
//!
//! To use the crate, first define a self-referential struct in plain Rust:
//!
//! ```rust
//! use std::cell::Cell;
//!
//! // Your self-referential struct.
//! struct MySelfRefStruct<'this> {
//!     // Rust uses RAII-like struct construction, as a result this must be
//!     // somehow initialized after the struct. We can use an Option in a Cell
//!     // for this.
//!     this: Cell<Option<&'this MySelfRefStruct<'this>>>,
//! }
//! ```
//!
//! Then, define a type to implement the `Opaque`. This can be done
//! automatically with the `opaque` macro:
//!
//! ```rust
//! # use std::cell::Cell;
//! # // Your self-referential struct.
//! # struct MySelfRefStruct<'this> {
//! #     // Rust uses RAII-like struct construction, as a result this must be
//! #     // somehow initialized after the struct. We can use an Option in a Cell
//! #     // for this.
//! #     this: Cell<Option<&'this MySelfRefStruct<'this>>>,
//! # }
//!
//! use xselfref::opaque;
//!
//! // A "marker type" that implements `Opaque`.
//! // This follows the "type family" GAT pattern.
//! struct MySelfRefStructKey;
//!
//! opaque! {
//!     impl Opaque for MySelfRefStructKey {
//!         type Kind<'this> = MySelfRefStruct<'this>;
//!     }
//! }
//!
//! // Alternatively, it is possible to implement `Opaque` on, for example,
//! // `MySelfRefStruct<'static>`, but the added lifetime adds verbosity which
//! // may be considered unnecessary/undesired.
//! ```
//!
//! Now you can construct a `Holder` and pick a storage for it. For example,
//! in a `Box`:
//!
//! ```rust
//! # use std::cell::Cell;
//! # // Your self-referential struct.
//! # struct MySelfRefStruct<'this> {
//! #     // Rust uses RAII-like struct construction, as a result this must be
//! #     // somehow initialized after the struct. We can use an Option in a Cell
//! #     // for this.
//! #     this: Cell<Option<&'this MySelfRefStruct<'this>>>,
//! # }
//! # use xselfref::opaque;
//! # // A "marker type" that implements `Opaque`.
//! # // This follows the "type family" GAT pattern.
//! # struct MySelfRefStructKey;
//! # opaque! {
//! #     impl Opaque for MySelfRefStructKey {
//! #         type Kind<'this> = MySelfRefStruct<'this>;
//! #     }
//! # }
//! # // Alternatively, it is possible to implement `Opaque` on, for example,
//! # // `MySelfRefStruct<'static>`, but the added lifetime adds verbosity which
//! # // may be considered unnecessary/undesired.
//!
//! use xselfref::Holder;
//!
//! fn main() {
//!     // first, construct the struct
//!     let holder = Box::pin(Holder::<'_, MySelfRefStructKey>::new_with(
//!         |foo| foo.build({
//!             MySelfRefStruct {
//!                 this: Cell::new(None)
//!             }
//!         })
//!     ));
//!
//!     // then, build the self-reference
//!     holder.as_ref().operate_in(
//!         |this| {
//!             this.this.set(Some(this.get_ref()));
//!         }
//!     );
//! }
//! ```
//!
//! # Examples
//!
//! This is a more complex example borrowing from an external lifetime:
//!
//! ```rust
//! use core::cell::Cell;
//! use core::marker::PhantomData;
//! use core::pin::Pin;
//! 
//! use xselfref::Holder;
//! use xselfref::opaque;
//!
//! struct Foo<'a, 'b: 'a> {
//!     foo: Cell<Option<&'a Foo<'a, 'b>>>,
//!     t: &'b str,
//! }
//!
//! struct FooKey<'b>(PhantomData<&'b str>);
//! opaque! {
//!     impl['b] Opaque for FooKey<'b> {
//!         type Kind<'a> = Foo<'a, 'b>;
//!     }
//! }
//!
//! fn main() {
//!     // a non-'static &str
//!     let stack_array: [u8; 5] = *b"hello";
//!     let stack_str = core::str::from_utf8(&stack_array).unwrap();
//!
//!     // construct the struct
//!     let holder = Box::pin(Holder::<'_, FooKey<'_>>::new_with(|foo| {
//!         foo.build(Foo {
//!             foo: Default::default(),
//!             t: stack_str,
//!         })
//!     }));
//!
//!     holder.as_ref().operate_in(|foo| {
//!         foo.foo.set(Some(foo.get_ref()));
//!     });
//! }
//! ```
//!
//! # Features
//!
//! Due to [PhantomData is unsound](https://github.com/rust-lang/rust/issues/102810)
//! we currently require the following features for `T: ?Sized` support in
//! `xselfref::opaque!`:
//!
//! - `alloc` - `xselfref::opaque!` for `T: ?Sized` is provided by `Box`.
//! - `nightly` - `xselfref::opaque!` for `T: ?Sized` is provided by a *wrapper*
//!     around `PhantomData`, which works around the above issue. we call this
//!     "PhantomDrop".
//!
//! When enabling both features, `nightly` takes over and we use the wrapper
//! always. This doesn't make a significant difference since the generated UB
//! check is dead code anyway, but `PhantomDrop` doesn't depend on `alloc` and
//! can be used in `no_std` environments.
//!
//! If not using either feature, `T: ?Sized` support requires `unsafe`ly
//! implementing `Opaque`.
//!
//! Note that we do **not** enable any features by default! We assume most
//! folks aren't coming to this crate for its `T: ?Sized` support, so these are
//! the best defaults for crates to depend on. If they do need the `?Sized`
//! support they can just enable one of these (probably `alloc`).

use core::marker::PhantomPinned;
use core::pin::Pin;
use core::mem;

// there's no sound way to dropck T: ?Sized without either alloc or nightly.
//
// so we just have the user opt-in to alloc or nightly as desired.
//
// when using alloc, we use Box<T> for UBCheck.
//
// when using nightly, we use our custom PhantomDrop<T> for UBCheck.
//
// when using neither, we just error on T: ?Sized and require a manual unsafe
// impl of Opaque.

#[cfg(all(feature="alloc", not(feature="nightly")))]
extern crate alloc;

#[cfg(all(feature="alloc", not(feature="nightly")))]
#[doc(hidden)]
pub struct UBCheck<T: ?Sized>(alloc::boxed::Box<T>);

#[cfg(feature="nightly")]
#[doc(hidden)]
pub struct UBCheck<T: ?Sized>(core::marker::PhantomData<T>);

#[cfg(all(not(feature="alloc"), not(feature="nightly")))]
#[doc(hidden)]
pub struct UBCheck<T>(T); // use feature "alloc" or "nightly" for T: ?Sized

#[cfg(feature="nightly")]
// SAFETY: dropck's like a Box<T>, but is no-alloc friendly.
unsafe impl<#[may_dangle] T: ?Sized> Drop for UBCheck<T> {
    fn drop(&mut self) {}
}

#[cfg(feature="qcell")]
pub mod srce;

/// An opaqueified self-referential struct "key".
///
/// # Safety
///
/// This is unsafe because there are a bunch of soundness invariants that need
/// to be upheld. The following list is non-exhaustive:
///
/// - `Kind` must not have a `Drop` impl in any "path" that may trace back to
///     the original self-referential type, if said `Drop` impl can observe
///     the self-referential type.
/// - We assume `Kind` has the same layout for any `'a`. This is true as of the
///     time of writing this, and relies on Rust not having lifetime
///     specialization.
///
/// It's recommended to use the `selfref::opaque!` macro instead, which
/// enforces these invariants. For example, this doesn't compile:
///
/// ```rust compile_fail
/// use std::cell::Cell;
/// use selfref::opaque;
///
/// struct Foo<'a> {
///     foo: Cell<Option<&'a Foo<'a>>>,
/// }
///
/// impl<'a> Drop for Foo<'a> {
///     fn drop(&mut self) {
///     }
/// }
///
/// struct FooKey;
/// opaque! {
///     impl Opaque for FooKey {
///         type Kind<'a> = Foo<'a>;
///     }
/// }
/// ```
///
/// But by removing the `Drop` impl, it compiles:
///
/// ```rust
/// use std::cell::Cell;
/// use xselfref::opaque;
///
/// struct Foo<'a> {
///     foo: Cell<Option<&'a Foo<'a>>>,
/// }
///
/// //impl<'a> Drop for Foo<'a> {
/// //    fn drop(&mut self) {
/// //    }
/// //}
///
/// struct FooKey;
/// opaque! {
///     impl Opaque for FooKey {
///         type Kind<'a> = Foo<'a>;
///     }
/// }
/// ```
///
/// # Examples
///
/// ```rust
/// use core::cell::Cell;
/// 
/// use xselfref::Opaque;
///
/// struct Foo<'a> {
///     foo: Cell<Option<&'a Foo<'a>>>,
/// }
///
/// struct FooKey;
/// // SAFETY: Foo has no Drop impl and has the same layout for any 'a.
/// unsafe impl Opaque for FooKey {
///     type Kind<'a> = Foo<'a>;
/// }
/// ```
pub unsafe trait Opaque {
    /// The actual self-referential struct.
    type Kind<'a>: ?Sized where Self: 'a;
    #[doc(hidden)]
    fn ub_check() {
    }
}

/// Creates an opaqueified self-referential struct "key".
///
/// Safe wrapper around [`Opaque`] that checks the soundness requirements at
/// compile-time.
///
/// There are 2 forms of this macro. The second form accepts type parameters.
///
/// Note that where bounds go after the impl block.
///
/// # Examples
///
/// Simple example:
///
/// ```rust
/// use core::cell::Cell;
/// 
/// use xselfref::opaque;
///
/// struct Foo<'a> {
///     foo: Cell<Option<&'a Foo<'a>>>,
/// }
///
/// struct FooKey;
/// opaque! {
///     impl Opaque for FooKey {
///         type Kind<'a> = Foo<'a>;
///     }
/// }
/// ```
///
/// Type parameters and where bounds:
///
/// ```rust
/// use core::cell::Cell;
/// use core::fmt::Display;
/// use core::marker::PhantomData;
/// 
/// use xselfref::opaque;
///
/// struct Foo<'a, T: Display> {
///     foo: Cell<Option<&'a Foo<'a, T>>>,
///     t: T,
/// }
///
/// struct FooKey<T>(PhantomData<T>);
/// opaque! {
///     impl[T] Opaque for FooKey<T> {
///         type Kind<'a> = Foo<'a, T>;
///     } where T: Display
/// }
/// ```
#[macro_export]
macro_rules! opaque {
    (
        impl Opaque for $key:ty {
            type Kind<$l:lifetime> = $kind:ty;
        } $(where $($bounds:tt)*)?
    ) => {
        unsafe impl $crate::Opaque for $key $(where $($bounds)*)? {
            type Kind<$l> = $kind where Self: $l;
            fn ub_check() {
                fn ub_detect_helper(
                    _f: impl ::core::ops::Fn(
                        for<$l> fn([&$l (); 0]) -> $crate::UBCheck<$kind>,
                        for<$l> fn(&$l $crate::UBCheck<$kind>)
                    )
                ) $(where $($bounds)*)? {
                }
                ub_detect_helper(|f, g| {
                    let x: $crate::UBCheck<Self::Kind<'_>> = f([]);
                    g(&x);
                });
            }
        }
    };
    (
        impl[$($params:tt)+] Opaque for $key:ty {
            type Kind<$l:lifetime> = $kind:ty;
        } $(where $($bounds:tt)*)?
    ) => {
        unsafe impl<$($params)+> $crate::Opaque for $key
        $(where $($bounds)*)? {
            type Kind<$l> = $kind where Self: $l;
            fn ub_check() {
                fn ub_detect_helper<$($params)+>(
                    _f: impl ::core::ops::Fn(
                        for<$l> fn([&$l (); 0]) -> $crate::UBCheck<$kind>,
                        for<$l> fn(&$l $crate::UBCheck<$kind>)
                    )
                ) $(where $($bounds)*)? {
                }
                ub_detect_helper(|f, g| {
                    let x: $crate::UBCheck<Self::Kind<'_>> = f([]);
                    g(&x);
                });
            }
        }
    };
}

/// Holds an "opaqueified" `T::Kind`.
///
/// Note the lifetime, `'k`. This can be anything, as long as `T` outlives it.
/// 
/// # Examples
///
/// ```rust
/// use core::cell::Cell;
/// 
/// use xselfref::Holder;
/// use xselfref::opaque;
///
/// #[derive(Default)]
/// struct Foo<'a> {
///     foo: Cell<Option<&'a Foo<'a>>>,
/// }
///
/// struct FooKey;
/// opaque! {
///     impl Opaque for FooKey {
///         type Kind<'a> = Foo<'a>;
///     }
/// }
///
/// fn main() {
///     // We can use a closure here, but we need to give the compiler a hint.
///     let holder = Holder::<'_, FooKey>::new_with(
///         |foo| foo.build(Foo::default())
///     );
/// }
/// ```
pub struct Holder<'k, T> where T: Opaque + 'k {
  _pinned: PhantomPinned,
  inner: <T as Opaque>::Kind<'k>,
}

/// Helper for creating a [`Holder`].
///
/// This is necessary because closures don't work properly here.
///
/// See [`Holder::new_with`] for examples.
pub struct Builder<'k, T: Opaque + 'k> where T::Kind<'k>: Sized {
    inner: Option<T::Kind<'k>>,
}

impl<'k, T: Opaque + 'k> Builder<'k, T> where T::Kind<'k>: Sized {
    /// Builds the [`Holder`].
    #[inline]
    pub fn build(&mut self, t: T::Kind<'k>) {
        self.inner = Some(t);
    }
}

impl<'k, T> Holder<'k, T> where T: Opaque {
    /// Creates a new holder.
    ///
    /// # Examples
    ///
    /// Simple example:
    ///
    /// ```rust
    /// use core::cell::Cell;
    /// 
    /// use xselfref::Holder;
    /// use xselfref::opaque;
    ///
    /// #[derive(Default)]
    /// struct Foo<'a> {
    ///     foo: Cell<Option<&'a Foo<'a>>>,
    /// }
    ///
    /// struct FooKey;
    /// opaque! {
    ///     impl Opaque for FooKey {
    ///         type Kind<'a> = Foo<'a>;
    ///     }
    /// }
    ///
    /// fn main() {
    ///     // We can use a closure here, but we need to help the compiler.
    ///     let holder = Holder::<'_, FooKey>::new_with(
    ///         |foo| foo.build(Foo::default())
    ///     );
    /// }
    /// ```
    ///
    /// Lifetime parameters:
    ///
    /// ```rust
    /// use core::cell::Cell;
    /// use core::marker::PhantomData;
    /// 
    /// use xselfref::Holder;
    /// use xselfref::opaque;
    ///
    /// struct Foo<'a, 'b: 'a> {
    ///     foo: Cell<Option<&'a Foo<'a, 'b>>>,
    ///     t: &'b str,
    /// }
    ///
    /// struct FooKey<'b>(PhantomData<&'b str>);
    /// opaque! {
    ///     impl['b] Opaque for FooKey<'b> {
    ///         type Kind<'a> = Foo<'a, 'b>;
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let stack_array: [u8; 5] = *b"hello";
    ///     // a non-'static &str
    ///     let stack_str = core::str::from_utf8(&stack_array).unwrap();
    ///     let holder = Holder::<'_, FooKey<'_>>::new_with(|foo| {
    ///         foo.build(Foo {
    ///             foo: Default::default(),
    ///             t: stack_str,
    ///         });
    ///     });
    /// }
    /// ```
    pub fn new_with<F>(f: F) -> Self
    where
        F: for<'a> FnOnce(&mut Builder<'a, T>),
        T::Kind<'k>: Sized,
    {
        let mut builder = Builder { inner: None };
        f(&mut builder);
        Self {
            // it is important that the constructor cannot observe 'k!
            inner: builder.inner.unwrap(),
            _pinned: PhantomPinned
        }
    }
}

/// Wrapper around a `Pin<&'k T::Kind<'k>>` for implied bounds.
///
/// Derefs to `Pin<&'k T::Kind<'k>>`.
pub struct OperateIn<'k, T> where T: Opaque + 'k {
    inner: Pin<&'k T::Kind<'k>>,
}

impl<'k, T> core::ops::Deref for OperateIn<'k, T> where T: Opaque {
    type Target = Pin<&'k T::Kind<'k>>;

    fn deref(&self) -> &Pin<&'k T::Kind<'k>> {
        &self.inner
    }
}

impl<'k, T> Holder<'k, T> where T: Opaque {
    /// Operates in this (pinned) holder.
    ///
    /// This "unwraps" the value in this holder, and binds its lifetime to a
    /// new stack frame.
    ///
    /// # Examples
    ///
    /// Simple example:
    ///
    /// ```rust
    /// use core::cell::Cell;
    /// 
    /// use xselfref::Holder;
    /// use xselfref::opaque;
    ///
    /// #[derive(Default)]
    /// struct Foo<'a> {
    ///     foo: Cell<Option<&'a Foo<'a>>>,
    /// }
    ///
    /// struct FooKey;
    /// opaque! {
    ///     impl Opaque for FooKey {
    ///         type Kind<'a> = Foo<'a>;
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let holder = Box::pin(Holder::<'_, FooKey>::new_with(
    ///         |foo| foo.build(Foo::default())
    ///     ));
    ///     // Actually making our Foo refer to itself.
    ///     holder.as_ref().operate_in(
    ///         |foo| {
    ///             foo.foo.set(Some(foo.get_ref()));
    ///         }
    ///     );
    /// }
    /// ```
    ///
    /// With lifetime parameters:
    ///
    /// ```rust
    /// use core::cell::Cell;
    /// use core::marker::PhantomData;
    /// use core::pin::Pin;
    /// 
    /// use xselfref::Holder;
    /// use xselfref::opaque;
    ///
    /// struct Foo<'a, 'b: 'a> {
    ///     foo: Cell<Option<&'a Foo<'a, 'b>>>,
    ///     t: &'b str,
    /// }
    ///
    /// struct FooKey<'b>(PhantomData<&'b str>);
    /// opaque! {
    ///     impl['b] Opaque for FooKey<'b> {
    ///         type Kind<'a> = Foo<'a, 'b>;
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let stack_array: [u8; 5] = *b"hello";
    ///     // a non-'static &str
    ///     let stack_str = core::str::from_utf8(&stack_array).unwrap();
    ///     let holder = Box::pin(Holder::<'_, FooKey<'_>>::new_with(|foo| {
    ///         foo.build(Foo {
    ///             foo: Default::default(),
    ///             t: stack_str,
    ///         });
    ///     }));
    ///     // Actually making our Foo refer to itself.
    ///     holder.as_ref().operate_in(|foo| {
    ///         foo.foo.set(Some(foo.get_ref()));
    ///     });
    /// }
    /// ```
    pub fn operate_in<'i, F, R>(self: Pin<&'i Self>, f: F) -> R
    where 
        F: for<'x> FnOnce(OperateIn<'x, T>) -> R
    {
        /// Converts `Pin<&'a T::Kind<'k>>` to `Pin<&'b T::Kind<'b>>`.
        ///
        /// Not sure why this is called "upcast_dangling" since none of these
        /// are actually dangling. But anyway.
        unsafe fn upcast_dangling<'a, 'b, 'c, T: Opaque + 'c>(
            x: Pin<&'a T::Kind<'c>>,
        ) -> Pin<&'b T::Kind<'b>>
        where T::Kind<'c>: 'a {
            mem::transmute(x)
        }
        f(OperateIn {
            inner: unsafe {
                upcast_dangling::<'i, 'k, '_, T>
                (self.map_unchecked(|self_ref| {
                    &self_ref.inner
                }))
            }
        })
    }

    pub fn deref_part<'a>(self: Pin<&'a Self>) -> &'a T::Part
    where
        T: NonSelfrefPart
    {
        T::deref_part(&self.get_ref().inner)
    }
}

pub trait NonSelfrefPart: Opaque {

    type Part;

    fn deref_part<'a, 'b>(data: &'a Self::Kind<'b>) -> &'a Self::Part
        where 'b: 'a;
}