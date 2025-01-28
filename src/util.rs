use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub struct Perfect<T: 'static>(pub(crate) &'static T);

impl<T> Perfect<T> {
    pub(crate) fn new(t: T) -> Self {
        Self(Box::leak(Box::new(t)))
    }

    fn ptr(self) -> *const T {
        self.0 as *const T
    }
}

impl<T: fmt::Display> fmt::Display for Perfect<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> Clone for Perfect<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Perfect<T> {}

impl<T> PartialEq for Perfect<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr() == other.ptr()
    }
}

impl<T> Eq for Perfect<T> {}

impl<T> Hash for Perfect<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        (self.0 as *const T).hash(hasher)
    }
}

impl<T> PartialOrd for Perfect<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Perfect<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ptr().cmp(&other.ptr())
    }
}

impl<T> std::ops::Deref for Perfect<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T> std::borrow::Borrow<T> for Perfect<T> {
    fn borrow(&self) -> &T {
        self.0
    }
}
