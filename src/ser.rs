use pyo3::exceptions::ValueError;
use pyo3::types::{PyAny, PyBool, PyBytes, PyComplex, PyFloat, PyFrozenSet, PyInt, PyList, PySet, PyString, PyTuple, PyType};
use pyo3::{AsPyRef, PyErr, PyResult, Python};
use serde::ser::{SerializeMap, SerializeSeq, Serializer};
use serde::Serialize;
use std::collections::BTreeMap;

use crate::Type;

trait WrapPyErr<T> {
  fn c<E: serde::ser::Error>(self, py: Python) -> Result<T, E>;
}

impl<T, P: Into<PyErr>> WrapPyErr<T> for Result<T, P> {
  fn c<E: serde::ser::Error>(self, py: Python) -> Result<T, E> {
    match self {
      Ok(v) => Ok(v),
      Err(e) => {
        e.into().restore(py);
        Err(serde::ser::Error::custom("python error"))
      }
    }
  }
}

macro_rules! raise {
  ($py:expr, $exc:ty, $msg:expr) => {
    <$exc>::py_err($msg).restore($py);
    return Err(serde::ser::Error::custom("python error"));
  };
}

macro_rules! raise_if {
  ($test:expr, $py:expr, $exc:ty, $msg:expr) => {
    if $test {
      raise!($py, $exc, $msg);
    }
  };
}

macro_rules! is_instance {
  ($py:expr, $val:expr, T:$typ:ty) => {
    $py.is_instance::<$typ, _>($val).c($py)?
  };
  ($py:expr, $val:expr, O:$typ:expr) => {
    $typ.is_instance($val).c($py)?
  };
}

fn get_type_name(typ: &PyType) -> PyResult<String> {
  let name = typ.getattr("__name__")?.str()?.to_string()?.to_string();
  let module = typ.getattr("__module__")?.str()?.to_string()?.to_string();
  Ok(if module == "builtins" { name } else { format!("{}.{}", module, name) })
}

fn get_type_name_or_question(typ: &PyType) -> String {
  match get_type_name(typ) {
    Ok(name) => format!("`{}`", name),
    Err(_) => "?".to_string(),
  }
}

macro_rules! get_type_obj {
  ($py:expr, T:$typ:ty) => {
    $py.get_type::<$typ>()
  };
  ($py:expr, O:$typ:expr) => {{
    let typ: &PyType = $typ;
    typ
  }};
}

macro_rules! check_is_instance {
  ($py:expr, $val:expr, T:$typ:ty) => {
    let val: &PyAny = $val;
    raise_if!(
      !is_instance!($py, val, T: $typ),
      $py,
      ValueError,
      format!(
        "expected an instance of {} but got an instance of {}",
        match get_type_name(get_type_obj!($py, T: $typ)) {
          Ok(v) => format!("`{}`", v),
          Err(_) => "?".to_string(),
        },
        match get_type_name(val.get_type()) {
          Ok(v) => format!("`{}`", v),
          Err(_) => "?".to_string(),
        }
      )
    );
  };
  ($py:expr, $val:expr, O:$typ:expr) => {
    let val: &PyAny = $val;
    raise_if!(
      !is_instance!($py, val, O: $typ),
      $py,
      ValueError,
      format!(
        "expected an instance of {} but got an instance of {}",
        match get_type_name(get_type_obj!($py, O: $typ)) {
          Ok(v) => format!("`{}`", v),
          Err(_) => "?".to_string(),
        },
        match get_type_name(val.get_type()) {
          Ok(v) => format!("`{}`", v),
          Err(_) => "?".to_string(),
        }
      )
    );
  };
}

fn serialize_seq<S: Serializer>(py: Python, serializer: S, seq: &PyAny, typ: &Type) -> Result<S::Ok, S::Error> {
  let mut serseq = serializer.serialize_seq(match seq.len() {
    Ok(len) => Some(len),
    Err(_) => None,
  })?;
  for val in seq.iter().c(py)? {
    serseq.serialize_element(&Wrapper { py: py, typ, val: val.c(py)? })?;
  }
  serseq.end()
}

fn get_is_dataclass(py: Python) -> PyResult<&PyAny> {
  py.import("dataclasses")?.getattr("is_dataclass")
}

fn is_dataclass(py: Python, v: &PyAny) -> PyResult<bool> {
  if let Ok(is_dataclass) = get_is_dataclass(py) {
    Ok(is_dataclass.call1((v,))?.extract()?)
  } else {
    Ok(false)
  }
}

pub struct Wrapper<'a> {
  py: Python<'a>,
  typ: &'a Type,
  val: &'a PyAny,
}

pub fn wrap<'a>(py: Python<'a>, typ: &'a Type, val: &'a PyAny) -> Wrapper<'a> {
  Wrapper { py, typ, val }
}

#[cfg(feature = "complex-struct")]
#[derive(Serialize)]
struct Complex {
  real: f64,
  imag: f64,
}

impl<'a> Serialize for Wrapper<'a> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let py = self.py;
    match self.typ {
      Type::Str => {
        check_is_instance!(py, self.val, T: PyString);
        serializer.serialize_str(self.val.extract().c(py)?)
      }
      Type::Bytes => {
        check_is_instance!(py, self.val, T: PyBytes);
        serializer.serialize_bytes(self.val.extract().c(py)?)
      }
      Type::Bool => {
        check_is_instance!(py, self.val, T: PyBool);
        serializer.serialize_bool(self.val.extract().c(py)?)
      }
      Type::Int => {
        check_is_instance!(py, self.val, T: PyInt);
        serializer.serialize_i64(self.val.extract().c(py)?)
      }
      Type::Float => serializer.serialize_f64(if is_instance!(py, self.val, T: PyFloat) {
        self.val.extract::<f64>().c(py)?
      } else if is_instance!(py, self.val, T: PyInt) {
        self.val.extract::<i64>().c(py)? as f64
      } else {
        raise!(py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
      }),
      #[cfg(feature = "complex-str")]
      Type::Complex => {
        let (r, i) = if is_instance!(py, self.val, T: PyComplex) {
          let v: &PyComplex = self.val.cast_as().c(py)?;
          (v.real(), v.imag())
        } else if is_instance!(py, self.val, T: PyFloat) {
          (self.val.extract().c(py)?, 0.0)
        } else if is_instance!(py, self.val, T: PyInt) {
          (self.val.extract::<i64>().c(py)? as f64, 0.0)
        } else {
          raise!(py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
        };
        serializer.serialize_str(&if i == 0.0 {
          format!("{}", r)
        } else if r == 0.0 {
          format!("{}j", i)
        } else {
          format!("{}+{}j", r, i)
        })
      }
      #[cfg(feature = "complex-struct")]
      Type::Complex => if is_instance!(py, self.val, T: PyComplex) {
        let v: &PyComplex = self.val.cast_as().c(py)?;
        Complex { real: v.real(), imag: v.imag() }
      } else if is_instance!(py, self.val, T: PyFloat) {
        Complex { real: self.val.extract().c(py)?, imag: 0.0 }
      } else if is_instance!(py, self.val, T: PyInt) {
        Complex { real: self.val.extract::<i64>().c(py)? as f64, imag: 0.0 }
      } else {
        raise!(py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
      }
      .serialize(serializer),
      Type::Decimal => {
        let m = py.import("decimal").c(py)?;
        let decimal: &PyType = m.getattr("Decimal").c(py)?.cast_as().c(py)?;
        check_is_instance!(py, self.val, O:decimal);
        serializer.serialize_str(self.val.str().c(py)?.extract().c(py)?)
      }
      Type::Enum(t) => {
        check_is_instance!(py, self.val, O:t.as_ref(py));
        serializer.serialize_str(self.val.getattr("name").c(py)?.extract().c(py)?)
      }
      Type::Sequence(typ) => serialize_seq(py, serializer, self.val, typ),
      Type::List(typ) => {
        check_is_instance!(py, self.val, T: PyList);
        serialize_seq(py, serializer, self.val, typ)
      }
      Type::UniformTuple(typ) => {
        check_is_instance!(py, self.val, T: PyTuple);
        serialize_seq(py, serializer, self.val, typ)
      }
      Type::Set(typ) => {
        check_is_instance!(py, self.val, T: PySet);
        serialize_seq(py, serializer, self.val, typ)
      }
      Type::FrozenSet(typ) => {
        check_is_instance!(py, self.val, T: PyFrozenSet);
        serialize_seq(py, serializer, self.val, typ)
      }
      Type::Tuple(typs) => {
        check_is_instance!(py, self.val, T: PyTuple);
        let val_len = self.val.len().c(py)?;
        raise_if!(val_len != typs.len(), py, ValueError, format!("expected a `tuple` of length {} but got {}", typs.len(), val_len));
        let mut sertup = serializer.serialize_seq(Some(typs.len()))?;
        for (typ, val) in typs.iter().zip(self.val.iter().c(py)?) {
          sertup.serialize_element(&Wrapper { py: py, typ, val: val.c(py)? })?;
        }
        sertup.end()
      }
      Type::Dict(ktyp, vtyp) => {
        let mut sermap = serializer.serialize_map(match self.val.len() {
          Ok(len) => Some(len),
          Err(_) => None,
        })?;
        for item in self.val.call_method0("items").c(py)?.iter().c(py)? {
          let item = item.c(py)?;
          let item_len = item.len().c(py)?;
          raise_if!(item_len < 2, py, ValueError, format!("not enough values to unpack (expected 2, got {})", item_len));
          raise_if!(item_len > 2, py, ValueError, format!("too many values to unpack (expected 2)"));
          sermap.serialize_entry(&Wrapper { py: py, typ: ktyp, val: item.get_item(0).c(py)? }, &Wrapper { py: py, typ: vtyp, val: item.get_item(1).c(py)? })?;
        }
        sermap.end()
      }
      Type::PositionalCallable(typs, callable) => {
        let obj: &PyAny = callable.as_ref(py);
        raise_if!(!is_instance!(py, obj.get_type(), T: PyType), py, ValueError, "only types can be serialized");
        let obj: &PyType = obj.cast_as::<PyType>().c(py)?;
        check_is_instance!(py, self.val, O: obj);
        let args: Vec<&PyAny> = self.val.call_method0("__getnewargs__").c(py)?.extract().c(py)?;
        if args.len() != typs.len() {
          raise!(py, ValueError, format!("__getnewargs__ returned {} args but {} were expected", args.len(), typs.len()));
        }
        let mut sertup = serializer.serialize_seq(Some(typs.len()))?;
        typs.iter().zip(args).try_for_each(|(typ, val)| sertup.serialize_element(&Wrapper { py: py, typ, val }))?;
        sertup.end()
      }
      Type::KeywordCallable(typs, callable) => {
        let obj: &PyAny = callable.as_ref(py);
        raise_if!(!is_instance!(py, obj.get_type(), T: PyType), py, ValueError, "only types can be serialized");
        let obj: &PyType = obj.cast_as::<PyType>().c(py)?;
        check_is_instance!(py, self.val, O: obj);
        let (args, kwargs): (Vec<&PyAny>, BTreeMap<String, &PyAny>) = if let Ok(result) = self.val.call_method0("__getnewargs__") {
          (result.extract().c(py)?, BTreeMap::new())
        } else if let Ok(result) = self.val.call_method0("__getnewargs_ex__") {
          result.extract().c(py)?
        } else if is_dataclass(py, self.val).c(py)? {
          (Vec::new(), typs.iter().map(|(name, _typ)| Ok((name.to_owned(), self.val.getattr(name).c(py)?))).collect::<Result<_, S::Error>>()?)
        } else {
          raise!(py, ValueError, format!("cannot call `__getnewargs__` or `__getnewargs_ex__`"));
        };
        let mut args = args.iter();
        let mut sermap = serializer.serialize_map(Some(typs.len()))?;
        for (name, typ) in typs {
          let val = if let Some(arg) = args.next() {
            arg
          } else if let Some(arg) = kwargs.get(name) {
            arg
          } else {
            raise!(py, ValueError, format!("cannot find argument {}", name));
          };
          sermap.serialize_entry(name, &Wrapper { py: py, typ, val })?;
        }
        sermap.end()
      }
      _ => Err(serde::ser::Error::custom("not implemented")),
    }
  }
}
