use std::cmp;
use std::io::Write;
use std::rc::Rc;

use Result;

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum NamespaceKind {
    Namespace,
    Function,
    Type,
}

#[derive(Debug)]
pub(crate) struct Namespace<'input> {
    pub parent: Option<Rc<Namespace<'input>>>,
    pub name: Option<&'input [u8]>,
    pub kind: NamespaceKind,
}

impl<'input> Namespace<'input> {
    pub fn new(
        parent: &Option<Rc<Namespace<'input>>>,
        name: Option<&'input [u8]>,
        kind: NamespaceKind,
    ) -> Rc<Namespace<'input>> {
        Rc::new(Namespace {
            parent: parent.clone(),
            name: name,
            kind: kind,
        })
    }

    fn len(&self) -> usize {
        match self.parent {
            Some(ref parent) => parent.len() + 1,
            None => 1,
        }
    }

    fn up(&self, len: usize) -> &Namespace {
        if len == 0 {
            self
        } else {
            match self.parent {
                Some(ref parent) => parent.up(len - 1),
                None => self,
            }
        }
    }

    pub fn is_anon_type(namespace: &Option<Rc<Namespace>>) -> bool {
        match *namespace {
            Some(ref namespace) => {
                namespace.kind == NamespaceKind::Type
                    && (namespace.name.is_none() || Namespace::is_anon_type(&namespace.parent))
            }
            None => false,
        }
    }

    pub fn print(&self, w: &mut Write) -> Result<()> {
        if let Some(ref parent) = self.parent {
            parent.print(w)?;
        }
        match self.name {
            Some(name) => write!(w, "{}", String::from_utf8_lossy(name))?,
            None => write!(w, "<anon>")?,
        }
        if self.kind == NamespaceKind::Function {
            write!(w, "()")?;
        }
        write!(w, "::")?;
        Ok(())
    }

    fn _filter(&self, namespace: &[&str]) -> (bool, usize) {
        let (ret, offset) = match self.parent {
            Some(ref parent) => parent._filter(namespace),
            None => (true, 0),
        };

        if ret {
            if offset < namespace.len() {
                match self.name {
                    Some(name) => (name == namespace[offset].as_bytes(), offset + 1),
                    None => (false, offset + 1),
                }
            } else {
                (true, offset)
            }
        } else {
            (false, 0)
        }
    }

    pub fn filter(&self, namespace: &[&str]) -> bool {
        self._filter(namespace) == (true, namespace.len())
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

    pub fn cmp_ns_and_name(
        ns1: &Option<Rc<Namespace>>,
        name1: Option<&[u8]>,
        ns2: &Option<Rc<Namespace>>,
        name2: Option<&[u8]>,
    ) -> cmp::Ordering {
        match (ns1, ns2) {
            (&Some(ref ns1), &Some(ref ns2)) => match Namespace::cmp(ns1, ns2) {
                cmp::Ordering::Equal => name1.cmp(&name2),
                o => o,
            },
            (&Some(_), &None) => cmp::Ordering::Greater,
            (&None, &Some(_)) => cmp::Ordering::Less,
            (&None, &None) => name1.cmp(&name2),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn cmp() {
        let ns1 = Namespace::new(&None, Some(b"a"), NamespaceKind::Namespace);
        let ns2 = Namespace::new(&None, Some(b"b"), NamespaceKind::Namespace);
        assert_eq!(Namespace::cmp(&ns1, &ns2), cmp::Ordering::Less);
    }
}
