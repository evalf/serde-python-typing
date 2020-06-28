use pyo3::exceptions::ValueError;
use pyo3::types::{PyAny, PyBool, PyBytes, PyComplex, PyFloat, PyFrozenSet, PyInt, PyList, PySet, PyString, PyTuple, PyType};
use pyo3::{AsPyRef, PyErr, PyResult, Python};
use serde::ser::{SerializeMap, SerializeSeq, Serializer};
use serde::Serialize;
use std::collections::BTreeMap;

use crate::Type;

// Like `?` for a `PyResult<T>` but if the result is an error, store the
// error and return a serde error instead.
macro_rules! pytry {
  ($py:expr, $result:expr) => {
    match $result {
      Ok(v) => v,
      Err(e) => {
        let e: PyErr = e.into();
        e.restore($py);
        return Err(serde::ser::Error::custom("python error"));
      }
    }
  };
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
    pytry!($py, $py.is_instance::<$typ, _>($val))
  };
  ($py:expr, $val:expr, O:$typ:expr) => {
    pytry!($py, $typ.is_instance($val))
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
  for val in pytry!(py, seq.iter()) {
    serseq.serialize_element(&Wrapper { py: py, typ, val: pytry!(py, val) })?;
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
    match self.typ {
      Type::Str => {
        check_is_instance!(self.py, self.val, T: PyString);
        serializer.serialize_str(pytry!(self.py, self.val.extract()))
      }
      Type::Bytes => {
        check_is_instance!(self.py, self.val, T: PyBytes);
        serializer.serialize_bytes(pytry!(self.py, self.val.extract()))
      }
      Type::Bool => {
        check_is_instance!(self.py, self.val, T: PyBool);
        serializer.serialize_bool(pytry!(self.py, self.val.extract()))
      }
      Type::Int => {
        check_is_instance!(self.py, self.val, T: PyInt);
        serializer.serialize_i64(pytry!(self.py, self.val.extract()))
      }
      Type::Float => serializer.serialize_f64(if is_instance!(self.py, self.val, T: PyFloat) {
        pytry!(self.py, self.val.extract::<f64>())
      } else if is_instance!(self.py, self.val, T: PyInt) {
        pytry!(self.py, self.val.extract::<i64>()) as f64
      } else {
        raise!(self.py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
      }),
      #[cfg(feature = "complex-str")]
      Type::Complex => {
        let (r, i) = if is_instance!(self.py, self.val, T: PyComplex) {
          let v: &PyComplex = pytry!(self.py, self.val.cast_as());
          (v.real(), v.imag())
        } else if is_instance!(self.py, self.val, T: PyFloat) {
          (pytry!(self.py, self.val.extract()), 0.0)
        } else if is_instance!(self.py, self.val, T: PyInt) {
          (pytry!(self.py, self.val.extract::<i64>()) as f64, 0.0)
        } else {
          raise!(self.py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
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
      Type::Complex => if is_instance!(self.py, self.val, T: PyComplex) {
        let v: &PyComplex = pytry!(self.py, self.val.cast_as());
        Complex { real: v.real(), imag: v.imag() }
      } else if is_instance!(self.py, self.val, T: PyFloat) {
        Complex { real: pytry!(self.py, self.val.extract()), imag: 0.0 }
      } else if is_instance!(self.py, self.val, T: PyInt) {
        Complex { real: pytry!(self.py, self.val.extract::<i64>()) as f64, imag: 0.0 }
      } else {
        raise!(self.py, ValueError, format!("expected an instance of `float` or `int` but got {}", get_type_name_or_question(self.val.get_type())));
      }
      .serialize(serializer),
      Type::Decimal => {
        let m = pytry!(self.py, self.py.import("decimal"));
        let decimal: &PyType = pytry!(self.py, pytry!(self.py, m.getattr("Decimal")).cast_as());
        check_is_instance!(self.py, self.val, O:decimal);
        serializer.serialize_str(pytry!(self.py, pytry!(self.py, self.val.str()).extract()))
      }
      Type::Enum(t) => {
        check_is_instance!(self.py, self.val, O:t.as_ref(self.py));
        serializer.serialize_str(pytry!(self.py, pytry!(self.py, self.val.getattr("name")).extract()))
      }
      Type::Sequence(typ) => serialize_seq(self.py, serializer, self.val, typ),
      Type::List(typ) => {
        check_is_instance!(self.py, self.val, T: PyList);
        serialize_seq(self.py, serializer, self.val, typ)
      }
      Type::UniformTuple(typ) => {
        check_is_instance!(self.py, self.val, T: PyTuple);
        serialize_seq(self.py, serializer, self.val, typ)
      }
      Type::Set(typ) => {
        check_is_instance!(self.py, self.val, T: PySet);
        serialize_seq(self.py, serializer, self.val, typ)
      }
      Type::FrozenSet(typ) => {
        check_is_instance!(self.py, self.val, T: PyFrozenSet);
        serialize_seq(self.py, serializer, self.val, typ)
      }
      Type::Tuple(typs) => {
        check_is_instance!(self.py, self.val, T: PyTuple);
        let val_len = pytry!(self.py, self.val.len());
        raise_if!(val_len != typs.len(), self.py, ValueError, format!("expected a `tuple` of length {} but got {}", typs.len(), val_len));
        let mut sertup = serializer.serialize_seq(Some(typs.len()))?;
        for (typ, val) in typs.iter().zip(pytry!(self.py, self.val.iter())) {
          sertup.serialize_element(&Wrapper { py: self.py, typ, val: pytry!(self.py, val) })?;
        }
        sertup.end()
      }
      Type::Dict(ktyp, vtyp) => {
        let mut sermap = serializer.serialize_map(match self.val.len() {
          Ok(len) => Some(len),
          Err(_) => None,
        })?;
        for item in pytry!(self.py, pytry!(self.py, self.val.call_method0("items")).iter()) {
          let item = pytry!(self.py, item);
          let item_len = pytry!(self.py, item.len());
          raise_if!(item_len < 2, self.py, ValueError, format!("not enough values to unpack (expected 2, got {})", item_len));
          raise_if!(item_len > 2, self.py, ValueError, format!("too many values to unpack (expected 2)"));
          sermap.serialize_entry(&Wrapper { py: self.py, typ: ktyp, val: pytry!(self.py, item.get_item(0)) }, &Wrapper { py: self.py, typ: vtyp, val: pytry!(self.py, item.get_item(1)) })?;
        }
        sermap.end()
      }
      Type::PositionalCallable(typs, callable) => {
        let obj: &PyAny = callable.as_ref(self.py);
        raise_if!(!is_instance!(self.py, obj.get_type(), T: PyType), self.py, ValueError, "only types can be serialized");
        let obj: &PyType = pytry!(self.py, obj.cast_as::<PyType>());
        check_is_instance!(self.py, self.val, O: obj);
        let args: Vec<&PyAny> = pytry!(self.py, pytry!(self.py, self.val.call_method0("__getnewargs__")).extract());
        if args.len() != typs.len() {
          raise!(self.py, ValueError, format!("__getnewargs__ returned {} args but {} were expected", args.len(), typs.len()));
        }
        let mut sertup = serializer.serialize_seq(Some(typs.len()))?;
        typs.iter().zip(args).try_for_each(|(typ, val)| sertup.serialize_element(&Wrapper { py: self.py, typ, val }))?;
        sertup.end()
      }
      Type::KeywordCallable(typs, callable) => {
        let obj: &PyAny = callable.as_ref(self.py);
        raise_if!(!is_instance!(self.py, obj.get_type(), T: PyType), self.py, ValueError, "only types can be serialized");
        let obj: &PyType = pytry!(self.py, obj.cast_as::<PyType>());
        check_is_instance!(self.py, self.val, O: obj);
        let (args, kwargs): (Vec<&PyAny>, BTreeMap<String, &PyAny>) = if let Ok(result) = self.val.call_method0("__getnewargs__") {
          (pytry!(self.py, result.extract()), BTreeMap::new())
        } else if let Ok(result) = self.val.call_method0("__getnewargs_ex__") {
          pytry!(self.py, result.extract())
        } else if pytry!(self.py, is_dataclass(self.py, self.val)) {
          (Vec::new(), typs.iter().map(|(name, _typ)| Ok((name.to_owned(), pytry!(self.py, self.val.getattr(name))))).collect::<Result<_, S::Error>>()?)
        } else {
          raise!(self.py, ValueError, format!("cannot call `__getnewargs__` or `__getnewargs_ex__`"));
        };
        let mut args = args.iter();
        let mut sermap = serializer.serialize_map(Some(typs.len()))?;
        for (name, typ) in typs {
          let val = if let Some(arg) = args.next() {
            arg
          } else if let Some(arg) = kwargs.get(name) {
            arg
          } else {
            raise!(self.py, ValueError, format!("cannot find argument {}", name));
          };
          sermap.serialize_entry(name, &Wrapper { py: self.py, typ, val })?;
        }
        sermap.end()
      }
      _ => Err(serde::ser::Error::custom("not implemented")),
    }
  }
}
