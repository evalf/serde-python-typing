use pyo3::conversion::ToPyObject;
use pyo3::exceptions::ValueError;
use pyo3::types::{PyComplex, PyDict, PyFrozenSet, PyList, PySet, PyTuple, PyString, IntoPyDict};
use pyo3::{PyErr, PyObject, Python};
use serde::de::{DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::fmt;

use crate::schema::Type;

// Like `?` for a `PyResult<T>` but if the result is an error, store the
// error and return a serde error instead.
macro_rules! pytry {
  ($py:expr, $result:expr) => {
    match $result {
      Ok(v) => v,
      Err(e) => {
        let e: PyErr = e.into();
        e.restore($py);
        return Err(serde::de::Error::custom("python error"));
      }
    }
  };
}

macro_rules! raise {
  ($py:expr, $exc:ty, $msg:expr) => {
    <$exc>::py_err($msg).restore($py);
    return Err(serde::de::Error::custom("python error"));
  };
}

pub struct Wrapper<'a> {
  py: Python<'a>,
  typ: &'a Type,
}

#[derive(Deserialize)]
struct Complex {
  real: f64,
  imag: f64,
}

impl<'de, 'a> DeserializeSeed<'de> for Wrapper<'a> {
  type Value = PyObject;

  fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
    match self.typ {
      Type::Str => deserializer.deserialize_str(VisitString(self.py)),
      Type::Bytes => deserializer.deserialize_bytes(VisitBytes(self.py)),
      Type::Bool => deserializer.deserialize_bool(VisitBool(self.py)),
      Type::Int => deserializer.deserialize_i64(VisitInt(self.py)),
      Type::Float => deserializer.deserialize_f64(VisitFloat(self.py)),
      Type::Complex => {
        let val = Complex::deserialize(deserializer)?;
        Ok(PyComplex::from_doubles(self.py, val.real, val.imag).into())
      }
      Type::Sequence(typ) => Ok(PyList::new(self.py, deserializer.deserialize_seq(VisitSeq { py: self.py, typ })?).into()),
      Type::UniformTuple(typ) => Ok(PyTuple::new(self.py, deserializer.deserialize_seq(VisitSeq { py: self.py, typ })?).into()),
      Type::Set(typ) => Ok(pytry!(self.py, PySet::new(self.py, &deserializer.deserialize_seq(VisitSeq { py: self.py, typ })?)).into()),
      Type::FrozenSet(typ) => Ok(pytry!(self.py, PyFrozenSet::new(self.py, &deserializer.deserialize_seq(VisitSeq { py: self.py, typ })?)).into()),
      Type::Tuple(typs) => deserializer.deserialize_seq(VisitTuple { py: self.py, typs: &typs }),
      Type::Dict(ktyp, vtyp) => Ok(deserializer.deserialize_map(VisitMap { py: self.py, ktyp, vtyp })?.into_py_dict(self.py).into()),
      Type::PositionalCallable(typs, callable) => Ok(pytry!(self.py, callable.call1(self.py, pytry!(self.py, deserializer.deserialize_seq(VisitTuple { py: self.py, typs: &typs })?.cast_as(self.py))))),
      Type::KeywordCallable(typs, callable) => Ok(pytry!(self.py, callable.call(self.py, (), Some(deserializer.deserialize_map(VisitKwargs { py: self.py, typs: &typs })?.into_py_dict(self.py))))),
      _ => Err(serde::de::Error::custom("foo not implemented")),
    }
  }
}

macro_rules! new_visitor {
  ($name:ident using $meth:ident($ty:ty) expecting $exp:literal) => {
    struct $name<'a>(Python<'a>);

    impl<'de, 'a> Visitor<'de> for $name<'a> {
      type Value = PyObject;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, $exp)
      }
      fn $meth<E: serde::de::Error>(self, v: $ty) -> Result<Self::Value, E> {
        Ok(v.to_object(self.0))
        //Ok(<$pyclass>::new(self.0, v).into())
      }
    }
  };
}

new_visitor! {VisitString using visit_str(&str) expecting "a string"}
new_visitor! {VisitBytes using visit_bytes(&[u8]) expecting "a bytestring"}
new_visitor! {VisitBool using visit_bool(bool) expecting "a bool"}
new_visitor! {VisitInt using visit_i64(i64) expecting "an int"}
new_visitor! {VisitFloat using visit_f64(f64) expecting "a float"}

struct VisitSeq<'a> {
  py: Python<'a>,
  typ: &'a Type,
}

impl<'de, 'a> Visitor<'de> for VisitSeq<'a> {
  type Value = Vec<PyObject>;

  fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    write!(formatter, "a sequence")
  }
  fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
    let mut v = Vec::new();
    while let Some(elem) = seq.next_element_seed(Wrapper { py: self.py, typ: self.typ })? {
      v.push(elem);
    }
    Ok(v)
  }
}

struct VisitTuple<'a> {
  py: Python<'a>,
  typs: &'a Vec<Type>,
}

impl<'de, 'a> Visitor<'de> for VisitTuple<'a> {
  type Value = PyObject;

  fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    write!(formatter, "a tuple")
  }
  fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
    let mut v = Vec::new();
    for typ in self.typs {
      match seq.next_element_seed(Wrapper { py: self.py, typ })? {
        Some(elem) => v.push(elem),
        None => {
          raise!(self.py, ValueError, "too few elements");
        }
      };
    }
    Ok(PyTuple::new(self.py, v).into())
  }
}

struct VisitKwargs<'a> {
  py: Python<'a>,
  typs: &'a Vec<(String, Type)>,
}

impl<'de, 'a> Visitor<'de> for VisitKwargs<'a> {
  type Value = Vec<(PyObject, PyObject)>;

  fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    write!(formatter, "a map")
  }
  fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
    let mut typs: BTreeMap<&str, &Type> = self.typs.iter().map(|(k, v)| (k.as_ref(), v)).collect();
    let mut v: Vec<(PyObject, PyObject)> = Vec::new();
    while let Some(key) = map.next_key::<&str>()? {
      if let Some(typ) = typs.get(&key) {
        v.push((key.to_object(self.py), map.next_value_seed(Wrapper { py: self.py, typ: typ })?));
      } else {
        raise!(self.py, ValueError, format!("unexpected argument {}", key));
      }
    }
    Ok(v)
  }
}

struct VisitMap<'a> {
  py: Python<'a>,
  ktyp: &'a Type,
  vtyp: &'a Type,
}

impl<'de, 'a> Visitor<'de> for VisitMap<'a> {
  type Value = Vec<(PyObject, PyObject)>;

  fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    write!(formatter, "a map")
  }
  fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
    let mut v: Vec<(PyObject, PyObject)> = Vec::new();
    while let Some(key) = map.next_key_seed(Wrapper { py: self.py, typ: self.ktyp })? {
      v.push((key, map.next_value_seed(Wrapper { py: self.py, typ: self.vtyp })?));
    }
    Ok(v)
  }
}

pub fn loads<'de, 'a, D: Deserializer<'de>>(py: Python<'a>, typ: &Type, deserializer: D) -> Result<PyObject, D::Error> {
  Wrapper { py, typ }.deserialize(deserializer)
}
