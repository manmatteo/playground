sig ljf-certificates.
accum_sig ljf-formulas.

kind cert, index                   type.
kind choice                        type.
type left, right                   choice.

type storeL_jc, storeR_jc          cert -> (A -> cert) -> (A -> index) -> prop.
type decideL_je, decideR_je        cert -> cert -> index -> prop.
type releaseL_je, releaseR_je      cert -> cert -> prop.
type initialL_je                   cert -> prop.
type initialR_je                   cert -> index -> prop.
type cut_je                        cert -> cert -> cert -> form -> prop.
type arr_jc, some_jc, all_jc       cert -> (A -> cert) -> prop.
type some_je, all_je               cert -> cert -> A -> prop.
type andPos_jc                     cert -> cert -> prop.
type or_jc, andNeg_jc,
     arr_je, andPos_je             cert -> cert -> cert -> prop.
type or_je, andNeg_je              cert -> cert -> choice -> prop.
type true_je                       cert -> prop.
type true_jc                       cert -> cert -> prop.
type false_jc                      cert -> prop.
