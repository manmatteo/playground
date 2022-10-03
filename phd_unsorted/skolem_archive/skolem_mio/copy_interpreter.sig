sig copy_interpreter.
accum_sig lib.
accum_sig classical.

type rigid i -> o.
type flex i -> o.

type interp (list o) -> (list o) -> (list o) -> (list o) -> o.

type instan o -> o -> o.
type flatten o -> (list o) -> o.

type dummy i.
type andq o -> o -> o.
type impq o -> o -> o.
type allq (i -> o) -> o.

type example int -> (list o) -> (list o) -> (list o) -> o.
type test_all o.
type test_spec (list o) -> (list o) -> (list o) -> o.
type test int -> o.