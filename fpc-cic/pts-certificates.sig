% Proof certificates for pure type systems
% Note: all those certificates that lead to an asynchronous-left phase
% (i.e. where something is in the ephemeral zone) give a certificate
% constructor as output.
% Only storeL_jc does the opposite: it takes constructors for cert and index,
% and binds them to an eigenvariable; the instanciated certificate and index are
% passed on. Thus, it only has the sort information as output.

kind s type. % sorts
kind ps type. % polarized sorts

% namespace certificates{
%%%%%%%%%%%%%%%% In    % Sort and SCert (O) % Output
type prodL_je    cert -> s -> cert -> cert -> (cert -> cert) -> prop.
type prodR_jc    cert -> s -> cert         -> (cert -> cert) -> prop.
type releaseL_je cert -> s -> cert         -> (cert -> cert) -> prop.
type releaseR_je cert -> s -> cert                   -> cert -> prop.
type decideL_jc  cert -> s -> cert          -> cert -> index -> prop.
type decideR_jc  cert -> s -> cert                   -> cert -> prop.
type storeR_jc   cert                                -> cert -> prop.
type axiomL_je   cert -> s -> cert                           -> prop.
type axiomR_je   cert -> s -> cert                  -> index -> prop.
type prodsort_jc cert -> ps -> ps -> ps -> index -> cert -> cert -> cert -> prop.
type sorted_jc   cert                                        -> prop.
type storeL_jc   (cert -> cert) -> (cert -> index)  -> cert -> prop.

%% Sorts, axioms, relations
% type sort  s -> term.
type p s -> ps.
type n s -> ps.
type sort ps -> A.
type axiom ps -> ps -> prop.
type rel ps -> ps -> ps -> prop.