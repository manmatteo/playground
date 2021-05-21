sig maxcert.

accum_sig lkf-certificates.
%accum_sig lib.
% accum_sig classical.

% type all                  int -> cert -> (i -> cert).
% type and_neg              int -> cert -> cert -> cert.
% type and_pos              int -> cert -> cert -> cert.
% %type cut                  cert -> cert -> cert -> form.
% type decide               int -> index -> cert -> cert.
% type false_neg            int -> cert -> cert.
% type initial              int -> index -> cert.
% type or_neg               int -> cert -> cert.
% type or_pos               int -> choice -> cert -> cert.
% type release              int -> cert -> cert.
% type some                 int -> i -> cert -> cert.
% type store                int -> index -> cert -> cert.
% type true_pos             int -> cert.

% type idx int -> index.

kind  max  type.
type ix                     int -> index.
type  max            int -> max -> cert.
type  max0                             max.
type  max1                     max -> max.
type  max2            max -> max -> max.
type  maxa                  index -> max.
type  maxi          index -> max -> max.
type  maxv           (i -> max) -> max.
type  maxt             i -> max -> max.
type  maxf   form -> max -> max -> max.
type  maxc         choice -> max -> max.