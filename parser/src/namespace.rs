use std::cmp;
use std::sync::Arc;

/// A namespace kind.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum NamespaceKind {
    /// An explicit namespace.
    Namespace,
    /// A namespace for items defined within a function.
    Function,
    /// A namespace for items defined within a type.
    Type,
}

/// A nestable namspace.
#[derive(Debug)]
pub struct Namespace<'input> {
    pub(crate) parent: Option<Arc<Namespace<'input>>>,
    pub(crate) name: Option<&'input str>,
    pub(crate) kind: NamespaceKind,
}

impl<'input> Namespace<'input> {
    pub(crate) fn new(
        parent: &Option<Arc<Namespace<'input>>>,
        name: Option<&'input str>,
        kind: NamespaceKind,
    ) -> Arc<Namespace<'input>> {
        Arc::new(Namespace {
            parent: parent.clone(),
            name,
            kind,
        })
    }

    /// The parent namespace.
    pub fn parent(&self) -> Option<&Namespace<'input>> {
        self.parent.as_deref()
    }

    /// The namespace name.
    #[inline]
    pub fn name(&self) -> Option<&'input str> {
        self.name
    }

    /// The namespace kind.
    #[inline]
    pub fn kind(&self) -> NamespaceKind {
        self.kind
    }

    fn len(&self) -> usize {
        match &self.parent {
            Some(parent) => parent.len() + 1,
            None => 1,
        }
    }

    fn up(&self, len: usize) -> &Namespace<'input> {
        if len == 0 {
            self
        } else {
            match &self.parent {
                Some(parent) => parent.up(len - 1),
                None => self,
            }
        }
    }

    pub(crate) fn is_anon_type(namespace: &Option<Arc<Namespace>>) -> bool {
        match namespace {
            Some(namespace) => {
                namespace.kind == NamespaceKind::Type
                    && (namespace.name.is_none() || Namespace::is_anon_type(&namespace.parent))
            }
            None => false,
        }
    }

    fn _is_within<T: AsRef<str>>(&self, namespace: &[T]) -> (bool, usize) {
        let (ret, offset) = match &self.parent {
            Some(parent) => parent._is_within(namespace),
            None => (true, 0),
        };

        if ret {
            if offset < namespace.len() {
                match self.name() {
                    Some(name) => (name == namespace[offset].as_ref(), offset + 1),
                    None => (false, offset + 1),
                }
            } else {
                (true, offset)
            }
        } else {
            (false, 0)
        }
    }

    /// Return true if this namespace is within the given namespace.
    ///
    /// `namespace` is a slice of names, starting with the root namespace name.
    pub fn is_within<T: AsRef<str>>(&self, namespace: &[T]) -> bool {
        self._is_within(namespace) == (true, namespace.len())
    }

    fn _cmp(a: &Namespace, b: &Namespace) -> cmp::Ordering {
        debug_assert_eq!(a.len(), b.len());
        match (a.parent.as_ref(), b.parent.as_ref()) {
            (Some(p1), Some(p2)) => {
                let ord = Self::_cmp(p1, p2);
                if ord != cmp::Ordering::Equal {
                    return ord;
                }
            }
            _ => {}
        }
        a.name.cmp(&b.name)
    }

    fn cmp(a: &Namespace, b: &Namespace) -> cmp::Ordering {
        let len_a = a.len();
        let len_b = b.len();
        match len_a.cmp(&len_b) {
            cmp::Ordering::Equal => Self::_cmp(a, b),
            cmp::Ordering::Less => {
                let b = b.up(len_b - len_a);
                match Self::_cmp(a, b) {
                    cmp::Ordering::Equal => cmp::Ordering::Less,
                    other => other,
                }
            }
            cmp::Ordering::Greater => {
                let a = a.up(len_a - len_b);
                match Self::_cmp(a, b) {
                    cmp::Ordering::Equal => cmp::Ordering::Greater,
                    other => other,
                }
            }
        }
    }

    pub(crate) fn cmp_ns_and_name(
        ns1: Option<&Namespace>,
        name1: Option<&str>,
        ns2: Option<&Namespace>,
        name2: Option<&str>,
    ) -> cmp::Ordering {
        match (ns1, ns2) {
            (Some(ns1), Some(ns2)) => match Namespace::cmp(ns1, ns2) {
                cmp::Ordering::Equal => name1.cmp(&name2),
                o => o,
            },
            (Some(_), None) => cmp::Ordering::Greater,
            (None, Some(_)) => cmp::Ordering::Less,
            (None, None) => name1.cmp(&name2),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn cmp() {
        let ns1 = Namespace::new(&None, Some("a".into()), NamespaceKind::Namespace);
        let ns2 = Namespace::new(&None, Some("b".into()), NamespaceKind::Namespace);
        assert_eq!(Namespace::cmp(&ns1, &ns2), cmp::Ordering::Less);
    }
}
