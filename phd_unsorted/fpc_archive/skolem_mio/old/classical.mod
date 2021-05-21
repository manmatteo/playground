module classical.

% By specifying print names (pname) for all signature items, we can
% get copy clauses for free.

copy T S :- fun_pname T Name L, fun_pname S Name K, mappred copy L K.
