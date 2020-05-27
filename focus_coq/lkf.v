(* Problems of classical focalization in Coq *)

(* What was underlined by Pichon *)
Goal forall a:Prop, (fix := (a -> False)) -> a.