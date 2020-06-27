use std::fmt::Display;
use pyo3::{Python, PyResult, PyErr};
use pyo3::exceptions::ValueError;

pub mod schema;
pub mod ser;
pub mod de;

pub fn wrap_err<T, E: Display>(py: Python, r: Result<T, E>) -> PyResult<T> {
  match r {
    Ok(v) => Ok(v),
    Err(e) => Err(if PyErr::occurred(py) { PyErr::fetch(py) } else { ValueError::py_err(e.to_string()) } ),
  }
}
