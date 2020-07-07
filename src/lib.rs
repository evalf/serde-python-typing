mod types;

use pyo3::exceptions::ValueError;
use pyo3::types::PyAny;
use pyo3::{PyErr, PyNativeType, PyObject, PyResult, Python};
use serde::de::DeserializeSeed;
use serde::ser::Serialize;
use serde::{Deserializer, Serializer};
use std::fmt;
use types::{PyDeserialize, PySerialize, Globals, TypeFuncs};

pub struct Type(types::Type);

impl Type {
  pub fn from_python(pytype: &PyAny) -> PyResult<Self> {
    Ok(Type(types::Type::from_python(&Globals::new(pytype.py())?, pytype)?))
  }
  pub fn is_instance(&self, value: &PyAny) -> PyResult<bool> {
    self.0.is_instance(value.py(), value, None)
  }
  pub fn serialize<S: Serializer>(&self, serializer: S, value: &PyAny) -> PyResult<S::Ok> {
    let py = value.py();
    wrap_err(py, PySerialize::new(py, &self.0, value).serialize(serializer))
  }
  pub fn deserialize<'de, D: Deserializer<'de>>(&self, deserializer: D, py: Python) -> PyResult<PyObject> {
    wrap_err(py, PyDeserialize::new(py, &self.0).deserialize(deserializer))
  }
}

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.0.fmt(f)
  }
}

pub fn wrap_err<T, E: fmt::Display>(py: Python, r: Result<T, E>) -> PyResult<T> {
  match r {
    Ok(v) => Ok(v),
    Err(e) => Err(if PyErr::occurred(py) { PyErr::fetch(py) } else { ValueError::py_err(e.to_string()) }),
  }
}
