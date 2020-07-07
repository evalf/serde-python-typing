use pyo3::conversion::ToPyObject;
use pyo3::exceptions::ValueError;
use pyo3::type_object::PyTypeObject;
use pyo3::types::{PyBool, PyBytes, PyComplex, PyDict, PyFloat, PyFrozenSet, PyInt, PyList, PySet, PySlice, PyString, PyTuple, PyType, IntoPyDict};
use pyo3::{AsPyRef, Py, PyAny, PyErr, PyObject, PyResult, Python};
use serde::de::{Deserialize, DeserializeSeed, EnumAccess, SeqAccess, VariantAccess, Visitor, MapAccess};
use serde::ser::{SerializeSeq, SerializeMap};
use serde::{de, ser, Deserializer, Serialize, Serializer};
use std::fmt;
use std::collections::BTreeMap;

trait TryAll<F, E> {
  fn try_all(&mut self, f: F) -> Result<bool, E>;
}

impl<I, F, E> TryAll<F, E> for I
where
  I: Iterator,
  F: FnMut(I::Item) -> Result<bool, E>,
{
  fn try_all(&mut self, mut f: F) -> Result<bool, E> {
    // TODO: use try_fold here?
    while let Some(item) = self.next() {
      if !f(item)? {
        return Ok(false);
      }
    }
    Ok(true)
  }
}

trait TryAny<F, E> {
  fn try_any(&mut self, f: F) -> Result<bool, E>;
}

impl<I, F, E> TryAny<F, E> for I
where
  I: Iterator,
  F: FnMut(I::Item) -> Result<bool, E>,
{
  fn try_any(&mut self, mut f: F) -> Result<bool, E> {
    // TODO: use try_fold here?
    while let Some(item) = self.next() {
      if f(item)? {
        return Ok(true);
      }
    }
    Ok(false)
  }
}

trait AsVec<'a>
where
  Self: 'a,
{
  fn as_vec(self) -> PyResult<Vec<&'a PyAny>>;
}

impl<'a> AsVec<'a> for &'a PyAny {
  fn as_vec(self) -> PyResult<Vec<&'a PyAny>> {
    self.iter()?.collect::<PyResult<_>>()
  }
}

// tuple = PyTuple
// list = PyList
// set = PySet
// frozenset = PyFrozenSet
// dict = PyDict
// import typing
// from enum import Enum: PyType
// from decimal import Decimal: PyType
// from collections.abc import Sequence: PyType, Mapping: PyType
// from collections import OrderedDict: PyType

pub struct Globals<'py> {
  py: Python<'py>,
  tuple: &'py PyType,
  list: &'py PyType,
  set: &'py PyType,
  frozenset: &'py PyType,
  dict: &'py PyType,
  sequence: &'py PyType,
  mapping: &'py PyType,
  ordereddict: &'py PyType,
  decimal: &'py PyType,
  ellipsis: &'py PyAny,
  builtins: &'py PyAny,
  typing: &'py PyAny,
  collections_abc: &'py PyAny,
  enum_enum: &'py PyAny,
  parameter: &'py PyAny,
  signature: &'py PyAny,
}

impl<'py> Globals<'py> {
  pub fn new(py: Python<'py>) -> PyResult<Self> {
    let builtins = py.import("builtins")?;
    let collections_abc = py.import("collections.abc")?;
    let inspect = py.import("inspect")?;
    Ok(Self {
      py,
      tuple: PyTuple::type_object(py),
      list: PyList::type_object(py),
      set: PySet::type_object(py),
      frozenset: PyFrozenSet::type_object(py),
      dict: PyDict::type_object(py),
      sequence: collections_abc.getattr("Sequence")?.cast_as()?,
      mapping: collections_abc.getattr("Mapping")?.cast_as()?,
      ordereddict: py.import("collections")?.getattr("OrderedDict")?.cast_as()?,
      decimal: py.import("decimal")?.getattr("Decimal")?.cast_as()?,
      ellipsis: builtins.getattr("Ellipsis")?,
      builtins,
      typing: py.import("typing")?,
      collections_abc,
      enum_enum: py.import("enum")?.getattr("Enum")?,
      parameter: py.import("inspect")?.getattr("Parameter")?,
      signature: inspect.getattr("signature")?,
    })
  }
  pub fn is_subclass(&self, a: &'py PyAny, b: &'py PyAny) -> PyResult<bool> {
    Ok(self.builtins.getattr("issubclass")?.call1((a, b))?.is_true()?)
  }
  pub fn get_origin(&self, ty: &'py PyAny) -> PyResult<Option<&'py PyAny>> {
    if let Ok(get_origin) = self.typing.getattr("get_origin") {
      let origin = get_origin.call1((ty,))?;
      if origin.is_none() {
        Ok(None)
      } else {
        Ok(Some(origin))
      }
    } else if let Ok(origin) = ty.getattr("__origin__") {
      if origin.is_none() {
        Ok(None)
      } else if origin == self.typing.getattr("Tuple")? {
        Ok(Some(self.tuple.as_ref()))
      } else if origin == self.typing.getattr("List")? {
        Ok(Some(self.list.as_ref()))
      } else if origin == self.typing.getattr("Set")? {
        Ok(Some(self.set.as_ref()))
      } else if origin == self.typing.getattr("FrozenSet")? {
        Ok(Some(self.frozenset.as_ref()))
      } else if origin == self.typing.getattr("Dict")? {
        Ok(Some(self.dict.as_ref()))
      } else {
        Ok(Some(origin))
      }
    } else {
      Ok(None)
    }
  }
  pub fn get_args(&self, ty: &'py PyAny) -> PyResult<Vec<&'py PyAny>> {
    if let Ok(get_args) = self.typing.getattr("get_args") {
      get_args.call1((ty,))?.as_vec()
    } else if let Ok(args) = ty.getattr("__args__") {
      if self.get_origin(ty)? == Some(self.collections_abc.getattr("Callable")?) && args.get_item(0)? != self.ellipsis {
        Ok(vec![args.get_item(PySlice::new(self.py, 0, -1, 1))?, args.get_item(-1)?])
      } else {
        args.as_vec()
      }
    } else {
      Ok(Vec::new())
    }
  }
  fn get_param_type<'a>(&self, p: &'a PyAny) -> PyResult<&'a PyAny> {
    let empty = self.parameter.getattr("empty")?;
    let not_empty = |v| if v == empty { None } else { Some(v) };
    if let Some(a) = not_empty(p.getattr("annotation")?) {
      Ok(a)
    } else if let Some(d) = not_empty(p.getattr("default")?) {
      Ok(d.get_type())
    } else {
      Err(ValueError::py_err(format!("invalid function signature: type cannot be inferred for argument {}", p.getattr("name")?)))
    }
  }
}

pub enum WrappedError<E> {
  Python(PyErr),
  Other(E),
}

pub type WrappedResult<T, E> = Result<T, WrappedError<E>>;

impl<P: Into<PyErr>, E> From<P> for WrappedError<E> {
  fn from(v: P) -> Self {
    Self::Python(v.into())
  }
}

pub trait Wrap<T, E> {
  fn wrap(self) -> WrappedResult<T, E>;
}

impl<T, E> Wrap<T, E> for Result<T, E> {
  fn wrap(self) -> WrappedResult<T, E> {
    match self {
      Ok(v) => Ok(v),
      Err(e) => Err(WrappedError::Other(e)),
    }
  }
}

pub trait TypeFuncs
where
  Self: Sized + fmt::Display,
{
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>>;
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool>;
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool>;
  fn is_instance(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    if !self.is_instance_self(py, value)? {
      Ok(false)
    } else {
      match depth {
        Some(0) => Ok(true),
        Some(depth) => self.is_instance_children(py, value, Some(depth - 1)),
        None => self.is_instance_children(py, value, None),
      }
    }
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error>;
  fn serialize<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    if self.is_instance(py, value, Some(0))? {
      self.serialize_checked(serializer, py, value)
    } else {
      let got_type_str = match value.get_type().str() {
        Ok(s) => format!("`{}`", s.to_string_lossy()),
        Err(_) => "?".to_string(),
      };
      Err(ValueError::py_err(format!("expected an instance of `{}` but got an instance of {}", self, got_type_str)).into())
    }
  }
  fn serialize_variant<S: Serializer>(&self, serializer: S, py: Python, name: &'static str, variant_index: u32, variant: &'static str, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    serializer.serialize_newtype_variant(name, variant_index, variant, &PySerialize::new(py, self, value)).wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error>;
  fn deserialize_variant<'de, A: VariantAccess<'de>>(&self, access: A, py: Python) -> WrappedResult<PyObject, A::Error> {
    access.newtype_variant_seed(PyDeserialize::new(py, self)).wrap()
  }
}

#[derive(Debug)]
pub struct NoneType;

impl fmt::Display for NoneType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "NoneType")
  }
}

impl TypeFuncs for NoneType {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    Ok(if pytype.is_none() || pytype == globals.py.None().as_ref(globals.py).get_type().as_ref() { Some(Self) } else { None })
  }
  fn is_instance_self(&self, _py: Python, value: &PyAny) -> PyResult<bool> {
    Ok(value.is_none())
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Ok(true)
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, _py: Python, _value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    serializer.serialize_unit().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct PyVisitor<'py>(Python<'py>);

    impl<'de, 'py> Visitor<'de> for PyVisitor<'py> {
      type Value = PyObject;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "None")
      }
      fn visit_unit<E: de::Error>(self) -> Result<PyObject, E> {
        Ok(self.0.None())
      }
    }

    deserializer.deserialize_unit(PyVisitor(py)).wrap()
  }
}

macro_rules! mk_simple_type {
  {$Type:ident for $pytype:ty, $pytypestr:literal; $serialize:ident; $deserialize:ident using $visit:ident($visitty:ty) expecting $exp:literal} => {
    mk_simple_type!{$Type for $pytype, $pytypestr; $serialize accepts; $deserialize using $visit($visitty) expecting $exp}
  };
  {$Type:ident for $pytype:ty, $pytypestr:literal; $serialize:ident accepts $($accept:ty),*; $deserialize:ident using $visit:ident($visitty:ty) expecting $exp:literal} => {
    #[derive(Debug)]
    pub struct $Type;

    impl TypeFuncs for $Type {
      fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
        Ok(if pytype == globals.py.get_type::<$pytype>().as_ref() { Some(Self) } else { None })
      }
      fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
        Ok(py.is_instance::<$pytype, _>(value)? $(|| py.is_instance::<$accept, _>(value)?)*)
      }
      fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
        Ok(true)
      }
      fn serialize_checked<S: Serializer>(&self, serializer: S, _py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
        serializer.$serialize(value.extract()?).wrap()
      }
      fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
        struct PyVisitor<'py>(Python<'py>);

        impl<'de, 'py> Visitor<'de> for PyVisitor<'py> {
          type Value = PyObject;

          fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            write!(formatter, $exp)
          }
          fn $visit<E: de::Error>(self, v: $visitty) -> Result<Self::Value, E> {
            Ok(v.to_object(self.0))
          }
        }

        Ok(deserializer.$deserialize(PyVisitor(py)).wrap()?.to_object(py))
      }
    }

    impl fmt::Display for $Type {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, $pytypestr)
      }
    }
  }
}

mk_simple_type! {Bool for PyBool, "bool"; serialize_bool; deserialize_bool using visit_bool(bool) expecting "a bool"}
mk_simple_type! {Int for PyInt, "int"; serialize_i64; deserialize_i64 using visit_i64(i64) expecting "an int"}
mk_simple_type! {Float for PyFloat, "float"; serialize_f64 accepts PyInt; deserialize_f64 using visit_f64(f64) expecting "a float"}
mk_simple_type! {Str for PyString, "str"; serialize_str; deserialize_str using visit_str(&str) expecting "a str"}
mk_simple_type! {Bytes for PyBytes, "bytes"; serialize_bytes; deserialize_bytes using visit_bytes(&[u8]) expecting "a bytestring"}

#[derive(Debug)]
pub struct Complex;

impl fmt::Display for Complex {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "complex")
  }
}

impl TypeFuncs for Complex {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    Ok(if pytype == globals.py.get_type::<PyComplex>().as_ref() { Some(Self) } else { None })
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    Ok(py.is_instance::<PyComplex, _>(value)? || py.is_instance::<PyFloat, _>(value)? || py.is_instance::<PyInt, _>(value)?)
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Ok(true)
  }
  fn serialize<S: Serializer>(&self, serializer: S, _py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let ri = if let Ok(v) = value.cast_as::<PyComplex>() {
      (v.real(), v.imag())
    } else if let Ok(v) = value.cast_as::<PyFloat>() {
      (v.value(), 0.0)
    } else if let Ok(v) = value.cast_as::<PyInt>() {
      (v.extract::<i64>()? as f64, 0.0)
    } else {
      let got_type_str = match value.get_type().str() {
        Ok(s) => format!("`{}`", s.to_string_lossy()),
        Err(_) => "?".to_string(),
      };
      return Err(ValueError::py_err(format!("expected an instance of `{}` but got an instance of {}", self, got_type_str)).into());
    };
    #[cfg(feature = "complex-str")]
    let ri = &if ri.1 == 0.0 {
      format!("{}", ri.0)
    } else if ri.0 == 0.0 {
      format!("{}j", ri.1)
    } else {
      format!("{}+{}j", ri.0, ri.1)
    };
    ri.serialize(serializer).wrap()
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    self.serialize(serializer, py, value)
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    #[cfg(feature = "complex-str")]
    let (r, i) = {
      fn strip_j(s: &str) -> Option<&str> {
        if s.ends_with('j') {
          Some(&s[..s.len() - 1])
        } else {
          None
        }
      }
      let mut parts = <&str>::deserialize(deserializer).wrap()?.split('+');
      let (r, i) = match (parts.next(), parts.next(), parts.next()) {
        (Some(r), Some(i), None) => match strip_j(i) {
          Some(i) => (r, i),
          None => {
            return Err(ValueError::py_err("cannot parse complex value"))?;
          }
        },
        (Some(v), None, None) => match strip_j(v) {
          Some(i) => ("0", i),
          None => (v, "0"),
        },
        _ => {
          return Err(ValueError::py_err("cannot parse complex value"))?;
        }
      };
      let r = match r.parse::<f64>() {
        Ok(v) => v,
        Err(_e) => {
          return Err(ValueError::py_err("cannot parse complex value"))?;
        }
      };
      let i = match i.parse::<f64>() {
        Ok(v) => v,
        Err(_e) => {
          return Err(ValueError::py_err("cannot parse complex value"))?;
        }
      };
      (r, i)
    };
    #[cfg(not(feature = "complex-str"))]
    let (r, i): (f64, f64) = Deserialize::deserialize(deserializer).wrap()?;
    Ok(PyComplex::from_doubles(py, r, i).into())
  }
}

#[derive(Debug)]
pub struct Decimal(Py<PyType>);

impl fmt::Display for Decimal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "decimal.Decimal")
  }
}

impl<'a> TypeFuncs for Decimal {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    Ok(if pytype == globals.decimal.as_ref() { Some(Self(globals.decimal.into())) } else { None })
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    self.0.as_ref(py).is_instance(value)
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Ok(true)
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, _py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    value.str()?.extract::<&str>()?.serialize(serializer).wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    let value: &str = Deserialize::deserialize(deserializer).wrap()?;
    Ok(self.0.as_ref(py).call1((value,))?.into())
  }
}

#[derive(Debug)]
pub struct Sequence {
  name_head: &'static str,
  name_tail: &'static str,
  elem_type: Box<Type>,
  new: PyObject,
  inst_cls: Py<PyType>,
}

impl fmt::Display for Sequence {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}{}{}", self.name_head, self.elem_type, self.name_tail)
  }
}

impl TypeFuncs for Sequence {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    let origin = if let Some(origin) = globals.get_origin(pytype)? { origin } else { return Ok(None) };
    let args: Vec<&PyAny> = globals.get_args(pytype)?;
    let (name_head, name_tail, new, inst_cls) = {
      if origin == globals.sequence.as_ref() && args.len() == 1 {
        ("typing.Sequence[", "]", globals.list, globals.sequence)
      } else if origin == globals.list.as_ref() && args.len() == 1 {
        ("typing.List[", "]", globals.list, globals.list)
      } else if origin == globals.set.as_ref() && args.len() == 1 {
        ("typing.Set[", "]", globals.set, globals.set)
      } else if origin == globals.frozenset.as_ref() && args.len() == 1 {
        ("typing.FrozenSet[", "]", globals.frozenset, globals.frozenset)
      } else if origin == globals.tuple.as_ref() && args.len() == 2 && args[1] == globals.ellipsis {
        ("typing.Tuple[", ", ...]", globals.tuple, globals.tuple)
      } else {
        return Ok(None);
      }
    };
    let elem_type = Box::new(Type::from_python(globals, args[0])?);
    Ok(Some(Sequence { name_head, name_tail, elem_type, new: new.into(), inst_cls: inst_cls.into() }))
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    self.inst_cls.as_ref(py).is_instance(value)
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    value.iter()?.try_all(|item| self.elem_type.is_instance(py, item?, depth))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let mut seq = serializer
      .serialize_seq(match value.len() {
        Ok(len) => Some(len),
        Err(_) => None,
      })
      .wrap()?;
    for item in value.iter()? {
      seq.serialize_element(&PySerialize::new(py, &*self.elem_type, item?)).wrap()?;
    }
    seq.end().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct PyVisitor<'py, 'a> {
      py: Python<'py>,
      elem_type: &'a Type,
    }

    impl<'de, 'py, 'a> Visitor<'de> for PyVisitor<'py, 'a> {
      type Value = Vec<PyObject>;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a sequence")
      }
      fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut result = match seq.size_hint() {
          Some(n) => Vec::with_capacity(n),
          None => Vec::new(),
        };
        while let Some(elem) = seq.next_element_seed(PyDeserialize::new(self.py, self.elem_type))? {
          result.push(elem);
        }
        Ok(result)
      }
    }

    let result = deserializer.deserialize_seq(PyVisitor { py, elem_type: &self.elem_type }).wrap()?;
    Ok(self.new.call1(py, (PyList::new(py, result),))?)
  }
}

#[derive(Debug)]
pub struct Tuple(Vec<Type>);

impl fmt::Display for Tuple {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "typing.Tuple[")?;
    let mut elem_types = self.0.iter();
    if let Some(elem_type) = elem_types.next() {
      write!(f, "{}", elem_type)?;
      elem_types.try_for_each(|elem_type| write!(f, ", {}", elem_type))?
    }
    write!(f, "]")
  }
}

impl TypeFuncs for Tuple {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    let origin = if let Some(origin) = globals.get_origin(pytype)? { origin } else { return Ok(None) };
    let args = globals.get_args(pytype)?;
    if origin != globals.tuple.as_ref() || args.len() == 0 || args[args.len() - 1] == globals.ellipsis {
      return Ok(None);
    }
    Ok(Some(Tuple(args.iter().map(|item| Type::from_python(globals, item)).collect::<PyResult<_>>()?)))
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    Ok(py.is_instance::<PyTuple, _>(value)? && value.len()? == self.0.len())
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    self.0.iter().zip(value.iter()?).try_all(|(ty, val)| ty.is_instance(py, val?, depth))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let mut ser = serializer.serialize_seq(Some(self.0.len())).wrap()?;
    for (elem_type, elem) in self.0.iter().zip(value.iter()?) {
      ser.serialize_element(&PySerialize::new(py, elem_type, elem?)).wrap()?;
    }
    ser.end().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct PyVisitor<'py, 'a> {
      py: Python<'py>,
      elem_types: &'a Vec<Type>,
    }

    impl<'de, 'py, 'a> Visitor<'de> for PyVisitor<'py, 'a> {
      type Value = Vec<PyObject>;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a tuple")
      }
      fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut result = Vec::with_capacity(self.elem_types.len());
        for elem_type in self.elem_types {
          match seq.next_element_seed(PyDeserialize::new(self.py, elem_type))? {
            Some(elem) => result.push(elem),
            None => {
              ValueError::py_err("too few elements").restore(self.py);
              return Err(de::Error::custom("python error"));
            }
          };
        }
        Ok(result)
      }
    }

    let result = deserializer.deserialize_seq(PyVisitor { py, elem_types: &self.0 }).wrap()?;
    let result: &PyAny = PyTuple::new(py, result.iter());
    Ok(result.into())
  }
}

struct VariantIndex(&'static [&'static str]);

impl<'de> DeserializeSeed<'de> for VariantIndex {
  type Value = u64;

  fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
    deserializer.deserialize_identifier(VariantIndexVisitor(self.0))
  }
}

struct VariantIndexVisitor(&'static [&'static str]);

impl<'de> Visitor<'de> for VariantIndexVisitor {
  type Value = u64;

  fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    write!(formatter, "variant identifier")
  }
  fn visit_u64<E: de::Error>(self, value: u64) -> Result<Self::Value, E> {
    if value < self.0.len() as u64 {
      Ok(value)
    } else {
      Err(de::Error::invalid_value(de::Unexpected::Unsigned(value), &self)) // format!("variant index 0 <= i < {}", self.0.len())))
    }
  }
  fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
    if let Some(index) = self.0.iter().position(|item| item == &value) {
      Ok(index as u64)
    } else {
      Err(de::Error::unknown_variant(value, self.0))
    }
  }
  fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
    self.visit_str(&serde::export::from_utf8_lossy(value))
  }
}

#[derive(Debug)]
pub struct Enum {
  name: String,
  variants: Vec<String>,
  cls: Py<PyType>,
}

impl fmt::Display for Enum {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.name)
  }
}

impl TypeFuncs for Enum {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    match pytype.cast_as::<PyType>() {
      Ok(pytype) if globals.is_subclass(pytype, globals.enum_enum)? => {
        let name: String = pytype.getattr("__name__")?.extract()?;
        let variants: Vec<String> = pytype.getattr("__members__")?.iter()?.map(|v| v?.extract()).collect::<PyResult<_>>()?;
        Ok(Some(Self { name, variants, cls: pytype.into() }))
      }
      _ => Ok(None),
    }
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    self.cls.as_ref(py).is_instance(value)
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Ok(true)
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, _py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let variant = value.getattr("name")?.extract()?;
    if let Some((index, _)) = self.variants.iter().enumerate().find(|(_, v)| v == &variant) {
      let strings = as_static_strings(&[&self.name, variant]);
      serializer.serialize_unit_variant(strings[0], index as u32, strings[1]).wrap()
    } else {
      Err(ValueError::py_err(format!("unexpected variant for enum {}: {}", self.name, variant)))?
    }
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct EnumVisitor(&'static [&'static str]);

    impl<'de> Visitor<'de> for EnumVisitor {
      type Value = String;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "an enum")
      }
      fn visit_enum<A: EnumAccess<'de>>(self, data: A) -> Result<Self::Value, A::Error> {
        let (index, access) = data.variant_seed(VariantIndex(self.0))?;
        let variant = self.0[index as usize].into();
        access.unit_variant()?;
        Ok(variant)
      }
    }

    let mut strings: Vec<&str> = Vec::with_capacity(self.variants.len() + 1);
    strings.push(&self.name);
    for variant in &self.variants {
      strings.push(&variant);
    }
    let static_strings = as_static_strings(&strings);
    let variant = deserializer.deserialize_enum(static_strings[0], &static_strings[1..], EnumVisitor(&static_strings[1..])).wrap()?;
    Ok(self.cls.as_ref(py).getattr("__members__")?.get_item(variant)?.into())
  }
}

#[derive(Debug)]
pub struct Optional(Box<Type>);

impl fmt::Display for Optional {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "typing.Optional[{}]", self.0)
  }
}

impl TypeFuncs for Optional {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    if globals.get_origin(pytype)? != Some(globals.typing.getattr("Union")?) {
      return Ok(None);
    }
    let args = globals.get_args(pytype)?;
    let none = globals.py.None();
    let nonetype = none.as_ref(globals.py).get_type().as_ref();
    if args.iter().all(|arg| !arg.is_none() && arg != &nonetype) {
      return Ok(None);
    }
    let args: Vec<&PyAny> = args.into_iter().filter(|arg| !arg.is_none() && arg != &nonetype).collect();
    Ok(match args.len() {
      0 => None,
      1 => Some(Self(Box::new(Type::from_python(globals, args[0])?))),
      _ => Some(Self(Box::new(Type::Union(Union::from_vec(globals, &args)?)))),
    })
  }
  fn is_instance_self(&self, _py: Python, _value: &PyAny) -> PyResult<bool> {
    Ok(true)
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    if value.is_none() {
      Ok(true)
    } else {
      self.0.is_instance(py, value, depth)
    }
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    if value.is_none() {
      serializer.serialize_none().wrap()
    } else {
      serializer.serialize_some(&PySerialize::new(py, &*self.0, value)).wrap()
    }
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct PyVisitor<'py, 'a> {
      py: Python<'py>,
      some_type: &'a Type,
    }

    impl<'de, 'py, 'a> Visitor<'de> for PyVisitor<'py, 'a> {
      type Value = PyObject;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "an option")
      }
      fn visit_none<E: de::Error>(self) -> Result<Self::Value, E> {
        Ok(self.py.None())
      }
      fn visit_some<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        PyDeserialize::new(self.py, self.some_type).deserialize(deserializer)
      }
    }

    deserializer.deserialize_option(PyVisitor { py, some_type: &*self.0 }).wrap()
  }
}

#[derive(Debug)]
pub struct Union(Vec<(String, Type)>);

impl Union {
  pub fn from_vec(globals: &Globals, args: &Vec<&PyAny>) -> PyResult<Self> {
    let mut variants = Vec::with_capacity(args.len());
    for arg in args.iter() {
      let name = arg.getattr("__name__")?.extract()?;
      let ty = Type::from_python(globals, arg)?;
      variants.push((name, ty));
    }
    Ok(Union(variants))
  }
}

impl fmt::Display for Union {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "typing.Union[")?;
    let mut variants = self.0.iter();
    if let Some((_name, ty)) = variants.next() {
      write!(f, "{}", ty)?;
      variants.try_for_each(|(_name, ty)| write!(f, ", {}", ty))?
    }
    write!(f, "]")
  }
}

impl TypeFuncs for Union {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    if globals.get_origin(pytype)? != Some(globals.typing.getattr("Union")?) {
      return Ok(None);
    }
    Ok(Some(Union::from_vec(globals, &globals.get_args(pytype)?)?))
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    self.0.iter().try_any(|(_name, ty)| ty.is_instance(py, value, Some(0)))
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    self.0.iter().try_any(|(_name, ty)| ty.is_instance(py, value, _depth))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    for (variant_index, (variant_name, ty)) in (&self.0).iter().enumerate() {
      if ty.is_instance(py, value, Some(0))? {
        let strings = as_static_strings(&["anonymous", &variant_name]);
        return ty.serialize_variant(serializer, py, strings[0], variant_index as u32, strings[1], value);
      }
    }
    Err(ValueError::py_err("unknown variant"))?
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct EnumVisitor<'py, 'a> {
      py: Python<'py>,
      variants: &'a Vec<(String, Type)>,
      static_variants: &'static [&'static str],
    }

    impl<'de, 'py, 'a> Visitor<'de> for EnumVisitor<'py, 'a> {
      type Value = PyObject;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "an enum")
      }
      fn visit_enum<A: EnumAccess<'de>>(self, data: A) -> Result<Self::Value, A::Error> {
        let (index, access) = data.variant_seed(VariantIndex(self.static_variants))?;
        if let Some((_name, ty)) = self.variants.get(index as usize) {
          match ty.deserialize_variant(access, self.py) {
            Ok(v) => Ok(v),
            Err(WrappedError::Other(e)) => Err(e),
            Err(WrappedError::Python(e)) => {
              e.restore(self.py);
              Err(de::Error::custom("python error"))
            }
          }
        } else {
          ValueError::py_err("unknown variant").restore(self.py);
          Err(de::Error::custom("python error"))
        }
      }
    }

    let mut strings: Vec<&str> = Vec::with_capacity(self.0.len() + 1);
    strings.push("");
    for (name, _ty) in &self.0 {
      strings.push(&name);
    }
    let static_strings = as_static_strings(&strings);
    deserializer.deserialize_enum(static_strings[0], &static_strings[1..], EnumVisitor { py, variants: &self.0, static_variants: &static_strings[1..] }).wrap()
  }
}

#[derive(Debug)]
pub struct Mapping {
  name: &'static str,
  key_type: Box<Type>,
  value_type: Box<Type>,
  new: PyObject,
  inst_cls: Py<PyType>,
}

impl fmt::Display for Mapping {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}[{}, {}]", self.name, self.key_type, self.value_type)
  }
}

impl TypeFuncs for Mapping {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    let origin = if let Some(origin) = globals.get_origin(pytype)? { origin } else { return Ok(None) };
    let args: Vec<&PyAny> = globals.get_args(pytype)?;
    if args.len() != 2 {
      return Ok(None);
    }
    let (name, new, inst_cls) = {
      if origin == globals.mapping.as_ref() {
        ("typing.Mapping", globals.dict, globals.mapping)
      } else if origin == globals.dict.as_ref() {
        ("typing.Dict", globals.dict, globals.dict)
      } else if origin == globals.ordereddict.as_ref() {
        ("typing.OrderedDict", globals.ordereddict, globals.ordereddict)
      } else {
        return Ok(None);
      }
    };
    let key_type = Box::new(Type::from_python(globals, args[0])?);
    let value_type = Box::new(Type::from_python(globals, args[1])?);
    Ok(Some(Mapping { name, key_type, value_type, new: new.into(), inst_cls: inst_cls.into() }))
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    self.inst_cls.as_ref(py).is_instance(value)
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    for item in value.call_method0("items")?.iter()? {
      let item = item?;
      if item.len()? != 2 {
        return Err(ValueError::py_err(format!("invalid number of values to unpack (expected 2, got {})", item.len()?)));
      }
      if !self.key_type.is_instance(py, item.get_item(0)?, depth)? || !self.value_type.is_instance(py, item.get_item(1)?, depth)? {
        return Ok(false);
      }
    }
    Ok(true)
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let mut ser = serializer.serialize_map(match value.len() {
      Ok(len) => Some(len),
      Err(_) => None,
    }).wrap()?;
    for item in value.call_method0("items")?.iter()? {
      let item = item?;
      if item.len()? != 2 {
        return Err(ValueError::py_err(format!("invalid number of values to unpack (expected 2, got {})", item.len()?)))?;
      }
      ser.serialize_entry(&PySerialize::new(py, &*self.key_type, item.get_item(0)?), &PySerialize::new(py, &*self.value_type, item.get_item(1)?)).wrap()?;
    }
    ser.end().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct VisitMap<'py, 'a> {
      py: Python<'py>,
      key_type: &'a Type,
      value_type: &'a Type,
    }

    impl<'de, 'py, 'a> Visitor<'de> for VisitMap<'py, 'a> {
      type Value = Vec<(PyObject, PyObject)>;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "map")
      }
      fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut v: Vec<(PyObject, PyObject)> = Vec::new();
        while let Some(key) = map.next_key_seed(PyDeserialize::new(self.py, self.key_type))? {
          v.push((key, map.next_value_seed(PyDeserialize::new(self.py, self.value_type))?));
        }
        Ok(v)
      }
    }

    Ok(deserializer.deserialize_map(VisitMap { py, key_type: &self.key_type, value_type: &self.value_type }).wrap()?.into_py_dict(py).into())
  }
}

#[derive(Debug)]
pub struct CallableKeywords {
  name: String,
  parameters: Vec<(String, Type)>,
  callable: PyObject,
}

impl fmt::Display for CallableKeywords {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.name)
  }
}

impl TypeFuncs for CallableKeywords {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    if !pytype.is_callable() {
      return Ok(None);
    }
    let sig = globals.signature.call1((pytype,))?;
    let params: Vec<&PyAny> = sig.getattr("parameters")?.call_method0("values")?.as_vec()?;
    let kinds: Vec<&PyAny> = params.iter().map(|p| p.getattr("kind")).collect::<PyResult<_>>()?;
    let name: String = pytype.getattr("__name__")?.extract()?;
    let positional_or_keyword = globals.parameter.getattr("POSITIONAL_OR_KEYWORD")?;
    let keyword_only = globals.parameter.getattr("KEYWORD_ONLY")?;
    if kinds.iter().all(|kind| kind == &positional_or_keyword || kind == &keyword_only) {
      let typs = params.iter().map(|p| Ok((p.getattr("name")?.extract::<String>()?, Type::from_python(globals, globals.get_param_type(p)?)?)));
      let parameters = typs.collect::<PyResult<_>>()?;
      Ok(Some(Self { name, parameters: parameters, callable: pytype.into() }))
    } else {
      Ok(None)
    }
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    if py.is_instance::<PyType, _>(self.callable.as_ref(py))? {
      self.callable.as_ref(py).cast_as::<PyType>()?.is_instance(value)
    } else {
      Ok(false)
    }
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Err(ValueError::py_err("not implemented"))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let (args, kwargs): (Vec<&PyAny>, BTreeMap<String, &PyAny>) = if let Ok(result) = value.call_method0("__getnewargs__") {
      (result.extract()?, BTreeMap::new())
    } else if let Ok(result) = value.call_method0("__getnewargs_ex__") {
      result.extract()?
    } else if py.import("dataclasses")?.getattr("is_dataclass")?.call1((value,))?.extract()? {
      (Vec::new(), self.parameters.iter().map(|(name, _typ)| Ok((name.to_owned(), value.getattr(name)?))).collect::<PyResult<_>>()?)
    } else {
      return Err(ValueError::py_err("cannot call `__getnewargs__` or `__getnewargs_ex__`"))?;
    };
    let mut args = args.iter();
    let mut ser = serializer.serialize_map(Some(self.parameters.len())).wrap()?;
    for (name, typ) in self.parameters.iter() {
      let val = if let Some(arg) = args.next() {
        arg
      } else if let Some(arg) = kwargs.get(name) {
        arg
      } else {
        return Err(ValueError::py_err(format!("cannot find argument {}", name)))?;
      };
      ser.serialize_entry(&name, &PySerialize::new(py, typ, val)).wrap()?;
    }
    ser.end().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct VisitKwargs<'py, 'a> {
      py: Python<'py>,
      parameters: &'a Vec<(String, Type)>,
    }

    impl<'de, 'py, 'a> Visitor<'de> for VisitKwargs<'py, 'a> {
      type Value = Vec<(PyObject, PyObject)>;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a map")
      }
      fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut parameters: BTreeMap<&str, &Type> = self.parameters.iter().map(|(k, v)| (k.as_ref(), v)).collect();
        let mut v: Vec<(PyObject, PyObject)> = Vec::new();
        while let Some(key) = map.next_key::<&str>()? {
          if let Some(typ) = parameters.remove(&key) {
            v.push((key.to_object(self.py), map.next_value_seed(PyDeserialize::new(self.py, typ))?));
          } else {
            ValueError::py_err(format!("unexpected argument {}", key)).restore(self.py);
            return Err(de::Error::custom("python error"));
          }
        }
        Ok(v)
      }
    }

    let kwargs = deserializer.deserialize_map(VisitKwargs { py, parameters: &self.parameters }).wrap()?;
    Ok(self.callable.call(py, (), Some(kwargs.into_py_dict(py)))?)
  }
}

#[derive(Debug)]
pub struct CallablePositional {
  name: String,
  parameters: Vec<Type>,
  callable: PyObject,
}

impl fmt::Display for CallablePositional {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.name)
  }
}

impl TypeFuncs for CallablePositional {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    if !pytype.is_callable() {
      return Ok(None);
    }
    if pytype == globals.tuple.as_ref() || pytype == globals.list.as_ref() || pytype == globals.set.as_ref() || pytype == globals.frozenset.as_ref() || pytype == globals.dict.as_ref() {
      return Ok(None);
    }
    let sig = globals.signature.call1((pytype,))?;
    let params: Vec<&PyAny> = sig.getattr("parameters")?.call_method0("values")?.as_vec()?;
    let kinds: Vec<&PyAny> = params.iter().map(|p| p.getattr("kind")).collect::<PyResult<_>>()?;
    let name: String = pytype.getattr("__name__")?.extract()?;
    let positional_or_keyword = globals.parameter.getattr("POSITIONAL_OR_KEYWORD")?;
    let positional_only = globals.parameter.getattr("POSITIONAL_ONLY")?;
    if kinds.iter().all(|kind| kind == &positional_or_keyword || kind == &positional_only) {
      let parameters = params.iter().map(|p| Type::from_python(globals, globals.get_param_type(p)?)).collect::<PyResult<_>>()?;
      Ok(Some(Self { name, parameters: parameters, callable: pytype.into() }))
    } else {
      Ok(None)
    }
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    if py.is_instance::<PyType, _>(self.callable.as_ref(py))? {
      self.callable.as_ref(py).cast_as::<PyType>()?.is_instance(value)
    } else {
      Ok(false)
    }
  }
  fn is_instance_children(&self, _py: Python, _value: &PyAny, _depth: Option<usize>) -> PyResult<bool> {
    Err(ValueError::py_err("not implemented"))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    let args: Vec<&PyAny> = if let Ok(result) = value.call_method0("__getnewargs__") {
      result.extract()?
    } else {
      return Err(ValueError::py_err("cannot call `__getnewargs__`"))?;
    };
    if args.len() != self.parameters.len() {
      return Err(ValueError::py_err(format!("expected {} arguments but got {}", self.parameters.len(), args.len())))?;
    }
    let mut ser = serializer.serialize_seq(Some(self.parameters.len())).wrap()?;
    for (ty, arg) in self.parameters.iter().zip(args) {
      ser.serialize_element(&PySerialize::new(py, ty, arg)).wrap()?;
    }
    ser.end().wrap()
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    struct VisitArgs<'py, 'a> {
      py: Python<'py>,
      parameters: &'a Vec<Type>,
    }

    impl<'de, 'py, 'a> Visitor<'de> for VisitArgs<'py, 'a> {
      type Value = Vec<PyObject>;

      fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a tuple")
      }
      fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut v: Vec<PyObject> = Vec::with_capacity(self.parameters.len());
        for ty in self.parameters.iter() {
          if let Some(elem) = seq.next_element_seed(PyDeserialize::new(self.py, ty))? {
            v.push(elem)
          } else {
            ValueError::py_err("unexpected end of sequence").restore(self.py);
            return Err(de::Error::custom("python error"));
          }
        }
        Ok(v)
      }
    }

    let args = deserializer.deserialize_seq(VisitArgs { py, parameters: &self.parameters }).wrap()?;
    let args = PyTuple::new(py, args);
    Ok(self.callable.as_ref(py).call1(args)?.into())
  }
}

macro_rules! callback_variants {
  ($callback:ident $($tt:tt)*) => { $callback!{[NoneType, Bool, Int, Float, Complex, Decimal, Str, Bytes, Sequence, Tuple, Enum, Optional, Union, Mapping, CallableKeywords, CallablePositional] $($tt)*} }
}

macro_rules! dispatch_variants {
  ($e:ident.$meth:ident$args:tt) => { (callback_variants!(dispatch_variants $e.$meth$args)) };
  ([$($variant:ident),*] $e:ident.$meth:ident$args:tt) => {
    match $e { $(Type::$variant(v) => v.$meth$args,)* }
  };
}

macro_rules! mk_type { {[$($t:ident),+]} => { #[derive(Debug)] pub enum Type { $($t($t)),+ } } }
callback_variants! {mk_type}

impl Type {
  pub fn from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Self> {
    if let Some(t) = Self::try_from_python(globals, pytype)? {
      Ok(t)
    } else {
      Err(ValueError::py_err("unsupported type"))
    }
  }
}

impl TypeFuncs for Type {
  fn try_from_python(globals: &Globals, pytype: &PyAny) -> PyResult<Option<Self>> {
    macro_rules! try_types {
      {[$($t:ident),+]} => { $(if let Some(t) = $t::try_from_python(globals, pytype)? { return Ok(Some(Self::$t(t))) };)+ }
    }
    callback_variants! {try_types}
    Ok(None)
  }
  fn is_instance_self(&self, py: Python, value: &PyAny) -> PyResult<bool> {
    dispatch_variants!(self.is_instance_self(py, value))
  }
  fn is_instance_children(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    dispatch_variants!(self.is_instance_children(py, value, depth))
  }
  fn is_instance(&self, py: Python, value: &PyAny, depth: Option<usize>) -> PyResult<bool> {
    dispatch_variants!(self.is_instance(py, value, depth))
  }
  fn serialize_checked<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    dispatch_variants!(self.serialize_checked(serializer, py, value))
  }
  fn serialize<S: Serializer>(&self, serializer: S, py: Python, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    dispatch_variants!(self.serialize(serializer, py, value))
  }
  fn serialize_variant<S: Serializer>(&self, serializer: S, py: Python, name: &'static str, variant_index: u32, variant: &'static str, value: &PyAny) -> WrappedResult<S::Ok, S::Error> {
    dispatch_variants!(self.serialize_variant(serializer, py, name, variant_index, variant, value))
  }
  fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> WrappedResult<PyObject, D::Error> {
    dispatch_variants!(self.deserialize(deserializer, py))
  }
  fn deserialize_variant<'de, A: VariantAccess<'de>>(&self, access: A, py: Python) -> WrappedResult<PyObject, A::Error> {
    dispatch_variants!(self.deserialize_variant(access, py))
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    macro_rules! dispatch {
      ([$($t:ident),+]) => { match self { $(Type::$t(t) => t.fmt(f)),+ } }
    }
    callback_variants! {dispatch}
  }
}

pub struct PySerialize<'py, 'a, T: TypeFuncs> {
  py: Python<'py>,
  ty: &'a T,
  val: &'py PyAny,
}

impl<'py, 'a, T: TypeFuncs> PySerialize<'py, 'a, T> {
  pub fn new(py: Python<'py>, ty: &'a T, val: &'py PyAny) -> Self {
    PySerialize { py, ty, val }
  }
}

impl<'py, 'a, T: TypeFuncs> Serialize for PySerialize<'py, 'a, T> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    match self.ty.serialize(serializer, self.py, self.val) {
      Ok(v) => Ok(v),
      Err(WrappedError::Other(e)) => Err(e),
      Err(WrappedError::Python(e)) => {
        e.restore(self.py);
        Err(ser::Error::custom("python error"))
      }
    }
  }
}

pub struct PyDeserialize<'py, 'a, T: TypeFuncs> {
  py: Python<'py>,
  ty: &'a T,
}

impl<'py, 'a, T: TypeFuncs> PyDeserialize<'py, 'a, T> {
  pub fn new(py: Python<'py>, ty: &'a T) -> Self {
    PyDeserialize { py, ty }
  }
}

impl<'de, 'py, 'a, T: TypeFuncs> DeserializeSeed<'de> for PyDeserialize<'py, 'a, T> {
  type Value = PyObject;

  fn deserialize<D: Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
    match self.ty.deserialize(deserializer, self.py) {
      Ok(v) => Ok(v),
      Err(WrappedError::Other(e)) => Err(e),
      Err(WrappedError::Python(e)) => {
        e.restore(self.py);
        Err(de::Error::custom("python error"))
      }
    }
  }
}

static mut STATIC_STR: [u8; 1024] = [0; 1024];
static mut STATIC_STRS: [&'static str; 100] = [""; 100];

pub fn as_static_strings(strings: &[&str]) -> &'static [&'static str] {
  unsafe {
    let mut offset = 0;
    for (i, s) in strings.iter().enumerate() {
      if i >= 100 {
        panic!("as_static_strings: too many items");
      }
      if offset + s.len() > 1024 {
        panic!("as_static_strings: insufficient static memory");
      }
      for (i, ch) in s.bytes().enumerate() {
        STATIC_STR[offset + i] = ch;
      }
      STATIC_STRS[i] = std::str::from_utf8(&STATIC_STR[offset..offset + s.len()]).unwrap();
      offset += s.len();
    }
    &STATIC_STRS[..strings.len()]
  }
}
