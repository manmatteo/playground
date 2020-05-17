#open "naturals.def".
#theorem ack_total "pi x\ nat x => pi y\ nat y => sigma a\ ack x y a, nat a".
intros.
%% This invariant is needed only once, so we could as well just "prove".
induction("x\ pi y\ nat y => sigma a\ (ack x y a, nat a)").
%% Trivial (invariance of the automatic invariant)
prove.
async. %% Split base case and induction step
%- Compute nat y0 |- sigma a\ ack 0 y0 a, nat a
    sigma_r. and_r. %% Intro metavar, split goals ack and nat.
    prove.          %% Computes result of ack, "a" becomes s(y0)
    prove.          %% nat y0 |- nat (s y0)
%- Induction step. This is where we want to be careful and double the context 
    induction("x\ pi y\ 
            (pi z\ (nat z => (sigma a\ (ack y z a, nat a)))) 
               => (sigma a\(ack (s y) x a, nat a)),
               pi y\ 
            (pi z\ (nat z => (sigma a\ (ack y z a, nat a)))) 
               => (sigma a\(ack (s y) x a, nat a))").
     prove. %% Trivial invariance of the invariant
     % prove. %% !!! Prove main theorem with automated tactic !!! Won't work with the double inv
 
% async. prove. %% Base case with double inv.
% pi_l. imp_l.
% and_r. prove.
% async.
% sigma_r. and_r.
% mu_r. %% Unfold ackermann
% right. sigma_r. sigma_r. sigma_r. %% Select appropriate case, intro metavars
% and_r. and_r. %% Split goals
% % prove. %% Unifies results
%  %% Compute ack (s y2) y1 B
% %% Full details left implicit for now
%  %async. %% Split base and induction steps.
%         %- Base: given y3, forall z (nat z => ack y3 z is total)
%         %        |- compute ack (s y3) 0
%  %        pi_l. imp_l.     %% Metavar on the left. The imp is safe: ctx is empty
%  %        prove.           %% LHS of imp assumption: nat Z.
%  %        %% Second premise of imp: compute ack 
%  %        sigma_r. and_r.  %% Intro metavar, split goals ack and nat
%         
