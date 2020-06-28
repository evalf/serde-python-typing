use pyo3::exceptions::ValueError;
use pyo3::types::{PyAny, PyBool, PyBytes, PyComplex, PyDict, PyFloat, PyFrozenSet, PyInt, PyList, PySet, PyString, PyTuple, PyType};
use pyo3::{PyObject, PyResult, Python, Py, AsPyRef};
use std::fmt;

#[derive(Debug)]
pub enum Type {
  Bool,
  Int,
  Float,
  Complex,
  Str,
  Bytes,
  Decimal,
  Enum(Py<PyType>),
  Sequence(Box<Type>),
  List(Box<Type>),
  UniformTuple(Box<Type>),
  Tuple(Vec<Type>),
  Set(Box<Type>),
  FrozenSet(Box<Type>),
  Dict(Box<Type>, Box<Type>),
  PositionalCallable(Vec<Type>, PyObject),
  KeywordCallable(Vec<(String, Type)>, PyObject),
}

impl Type {
  pub fn from_python(py: Python, t: &PyAny) -> PyResult<Type> {
    let typing = py.import("typing")?;
    let builtins = py.import("builtins")?;
    let collections_abc = py.import("collections.abc")?;
    let inspect = py.import("inspect")?;
    let py_get_origin = typing.getattr("get_origin")?;
    let py_get_args = typing.getattr("get_args")?;
    let py_signature = inspect.getattr("signature")?;
    let positional_only = inspect.getattr("Parameter")?.getattr("POSITIONAL_ONLY")?;
    let positional_or_keyword = inspect.getattr("Parameter")?.getattr("POSITIONAL_OR_KEYWORD")?;
    let keyword_only = inspect.getattr("Parameter")?.getattr("KEYWORD_ONLY")?;
    let empty = inspect.getattr("Signature")?.getattr("empty")?;
    let sequence = collections_abc.getattr("Sequence")?.cast_as()?;
    let ellipsis = builtins.getattr("Ellipsis")?;
    let decimal = py.import("decimal")?.getattr("Decimal")?;
    let py_enum = py.import("enum")?.getattr("Enum")?;
    let parser = Parser { py, py_get_origin, py_get_args, py_signature, positional_only, positional_or_keyword, keyword_only, empty, sequence, ellipsis, decimal, py_enum };
    parser.parse(t)
  }
  pub fn to_string(&self, py: Python) -> String {
    format!("{}", FmtType { py, typ: &self })
  }
}

struct FmtType<'py, 'a> {
  py: Python<'py>,
  typ: &'a Type,
}

impl<'py, 'a> FmtType<'py, 'a> {
  fn wrap(&self, typ: &'a Type) -> FmtType<'py, 'a> {
    FmtType { py: self.py, typ }
  }
}

impl<'py, 'a> fmt::Display for FmtType<'py, 'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.typ {
      Type::Bool => write!(f, "bool"),
      Type::Int => write!(f, "int"),
      Type::Float => write!(f, "float"),
      Type::Complex => write!(f, "complex"),
      Type::Str => write!(f, "str"),
      Type::Bytes => write!(f, "bytes"),
      Type::Decimal => write!(f, "decimal.Decimal"),
      Type::Enum(t) => write!(f, "{}", if let Ok(n) = get_name(t.as_ref(self.py).into()) { n } else { "enum.Enum".to_string() }),
      Type::Sequence(t) => write!(f, "typing.Sequence[{}]", self.wrap(t)),
      Type::List(t) => write!(f, "list[{}]", self.wrap(t)),
      Type::UniformTuple(t) => write!(f, "tuple[{}, ...]", self.wrap(t)),
      Type::Tuple(typs) => {
        write!(f, "tuple[")?;
        let mut typs = typs.iter();
        if let Some(t) = typs.next() {
          write!(f, "{}", self.wrap(t))?;
          typs.try_for_each(|t| write!(f, ", {}", self.wrap(t)))?
        }
        write!(f, "]")
      }
      Type::Set(t) => write!(f, "set[{}]", self.wrap(t)),
      Type::FrozenSet(t) => write!(f, "frozenset[{}]", self.wrap(t)),
      Type::Dict(k, v) => write!(f, "dict[{}, {}]", self.wrap(k), self.wrap(v)),
      Type::PositionalCallable(_, c) => write!(f, "{}", if let Ok(n) = get_name(c.as_ref(self.py)) { n } else { "callable".to_string() }),
      Type::KeywordCallable(_, c) => write!(f, "{}", if let Ok(n) = get_name(c.as_ref(self.py)) { n } else { "callable".to_string() }),
    }
  }
}

fn get_name(c: &PyAny) -> PyResult<String> {
  c.getattr("__name__")?.extract()
}

struct Parser<'a> {
  py: Python<'a>,
  py_get_origin: &'a PyAny,
  py_get_args: &'a PyAny,
  py_signature: &'a PyAny,
  positional_only: &'a PyAny,
  positional_or_keyword: &'a PyAny,
  keyword_only: &'a PyAny,
  empty: &'a PyAny,
  sequence: &'a PyType,
  ellipsis: &'a PyAny,
  decimal: &'a PyAny,
  py_enum: &'a PyAny,
}

impl<'a> Parser<'a> {
  pub fn parse(&self, t: &PyAny) -> PyResult<Type> {
    if self.py.is_instance::<PyType, _>(t)? {
      let t: &PyType = t.cast_as()?;
      if t == self.py.get_type::<PyBool>() {
        return Ok(Type::Bool);
      } else if t == self.py.get_type::<PyInt>() {
        return Ok(Type::Int);
      } else if t == self.py.get_type::<PyFloat>() {
        return Ok(Type::Float);
      } else if t == self.py.get_type::<PyComplex>() {
        return Ok(Type::Complex);
      } else if t == self.py.get_type::<PyString>() {
        return Ok(Type::Str);
      } else if t == self.py.get_type::<PyBytes>() {
        return Ok(Type::Bytes);
      } else if self.py.import("builtins")?.getattr("issubclass")?.call1((t, self.decimal))?.is_true()? {
        return Ok(Type::Decimal);
      } else if self.py.import("builtins")?.getattr("issubclass")?.call1((t, self.py_enum))?.is_true()? {
        return Ok(Type::Enum(t.cast_as::<PyType>()?.into()));
      } else if t == self.py.get_type::<PyTuple>() {
        return Err(ValueError::py_err("cannot serialize tuple; use typing.Tuple[] instead".to_string()));
      } else if t == self.py.get_type::<PyList>() {
        return Err(ValueError::py_err("cannot serialize list; use typing.List[] instead".to_string()));
      } else if t == self.py.get_type::<PySet>() {
        return Err(ValueError::py_err("cannot serialize set; use typing.Set[] instead".to_string()));
      } else if t == self.py.get_type::<PyFrozenSet>() {
        return Err(ValueError::py_err("cannot serialize frozenset; use typing.FrozenSet[] instead".to_string()));
      } else if t == self.py.get_type::<PyDict>() {
        return Err(ValueError::py_err("cannot serialize dict; use typing.Dict[] instead".to_string()));
      }
    }
    if let Some(origin) = self.get_origin(t)? {
      let args: &PyTuple = self.py_get_args.call1((t,))?.cast_as()?;
      if origin == self.sequence {
        if args.len() == 1 {
          return Ok(Type::Sequence(Box::new(self.parse(args.get_item(0))?)));
        } else {
          return Err(ValueError::py_err(format!("{}: expected 1 generic argument but got {}", t.str()?, args.len())));
        }
      } else if origin == self.py.get_type::<PyList>() {
        if args.len() == 1 {
          return Ok(Type::List(Box::new(self.parse(args.get_item(0))?)));
        } else {
          return Err(ValueError::py_err(format!("{}: expected 1 generic argument but got {}", t.str()?, args.len())));
        }
      } else if origin == self.py.get_type::<PyTuple>() {
        if args.len() == 0 {
          return Err(ValueError::py_err(format!("{}: expected at least 1 generic argument but got 0", t.str()?)));
        } else if args.len() == 2 && args.get_item(1) == self.ellipsis {
          return Ok(Type::UniformTuple(Box::new(self.parse(args.get_item(0))?)));
        } else {
          return Ok(Type::Tuple(args.iter().map(|v| self.parse(v)).collect::<PyResult<Vec<Type>>>()?));
        }
      } else if origin == self.py.get_type::<PySet>() {
        if args.len() == 1 {
          return Ok(Type::Set(Box::new(self.parse(args.get_item(0))?)));
        } else {
          return Err(ValueError::py_err(format!("{}: expected 1 generic argument but got {}", t.str()?, args.len())));
        }
      } else if origin == self.py.get_type::<PyFrozenSet>() {
        if args.len() == 1 {
          return Ok(Type::FrozenSet(Box::new(self.parse(args.get_item(0))?)));
        } else {
          return Err(ValueError::py_err(format!("{}: expected 1 generic argument but got {}", t.str()?, args.len())));
        }
      } else if origin == self.py.get_type::<PyDict>() {
        if args.len() == 2 {
          return Ok(Type::Dict(Box::new(self.parse(args.get_item(0))?), Box::new(self.parse(args.get_item(1))?)));
        } else {
          return Err(ValueError::py_err(format!("{}: expected 1 generic argument but got {}", t.str()?, args.len())));
        }
      }
    }
    if t.is_callable() {
      let sig = self.py_signature.call1((t,))?;
      let params: Vec<&PyAny> = sig.getattr("parameters")?.call_method0("values")?.iter()?.collect::<PyResult<_>>()?;
      let kinds: Vec<&PyAny> = params.iter().map(|p| p.getattr("kind")).collect::<PyResult<_>>()?;
      if kinds.iter().all(|kind| kind == &self.positional_or_keyword || kind == &self.keyword_only) {
        let typs = params.iter().map(|p| Ok((p.getattr("name")?.extract::<String>()?, self.get_param_type(p)?)));
        return Ok(Type::KeywordCallable(typs.collect::<PyResult<_>>()?, t.into()));
      } else if kinds.iter().all(|kind| kind == &self.positional_only || kind == &self.positional_or_keyword) {
        let typs = params.iter().map(|p| self.parse(p.getattr("annotation")?));
        return Ok(Type::PositionalCallable(typs.collect::<PyResult<_>>()?, t.into()));
      } else {
        return Err(ValueError::py_err("mixing positional and keyword arguments is not allowed"));
      }
    }
    Err(ValueError::py_err(format!("serialization to/from {} is not supported", t.str()?)))
  }
  fn not_empty<'b>(&self, v: &'b PyAny) -> Option<&'b PyAny> {
    if v == self.empty {
      None
    } else {
      Some(v)
    }
  }
  fn get_param_type(&self, p: &PyAny) -> PyResult<Type> {
    if let Some(a) = self.not_empty(p.getattr("annotation")?) {
      self.parse(a)
    } else if let Some(d) = self.not_empty(p.getattr("default")?) {
      self.parse(d.get_type())
    } else {
      Err(ValueError::py_err(format!("invalid function signature: type cannot be inferred for argument {}", p.getattr("name")?)))
    }
  }
  fn get_origin(&self, t: &PyAny) -> PyResult<Option<&PyType>> {
    let origin: &PyAny = self.py_get_origin.call1((t,))?;
    if origin.is_none() {
      Ok(None)
    } else {
      Ok(Some(origin.cast_as()?))
    }
  }
}
