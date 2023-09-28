
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
  
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro pb,
  by_cases p:P,
  exact p,
  exfalso,
  exact pb(p),
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro np,
  by_cases p:P,
  exact p,
  exfalso,
  exact np(p),
  intro p,
  intro np,
  exact np(p),
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pb,
  cases pb with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro npq,
  intro p,
  cases npq with np q,
  exfalso,
  exact np(p),
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro nq,
  cases pq with p q,
  exfalso,
  exact nq(p),
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pb,
  intro qb,
  intro p,
  have q:Q := pb p,
  have b:false :=qb q,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nqnp,
  intro p,
  by_cases q:Q,
  exact q,
  have np: ¬P:= nqnp q,
  exfalso,
  exact np(p),
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro pq,
  intro nq,
  intro p,
  have q:Q := pq p,
  exact nq(q),
  intro nqnp,
  intro p,
  by_cases q:Q,
  exact q,
  exfalso,
  have np:¬P :=nqnp q, 
  exact np(p),
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro  nnp,
  apply nnp,
  right,
  intro p,
  apply nnp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  exfalso,
  exact np(p),
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases npnq with np nq,
  cases pq,
  exact np(pq),
  exact nq(pq),
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases pq with p q,
  cases npnq,
  exact npnq(p),
  exact npnq(q),
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro nq,
  apply npq,
  right,
  exact nq,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  cases npnq with np nq,
  intro pq,
  apply np,
  cases pq,
  exact pq,
  exfalso,
  apply nq,
  exact pq,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases p:P,
  left,
  intro q,
  apply npq,
  split,
  exact p,
  exact q,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqnp,
  intro pq,
  cases pq with p q,
  cases nqnp,
  exact nqnp(q),
  exact nqnp(p),
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro npq,
  by_cases p:P,
  left,
  intro q,
  apply npq,
  split,
  exact p,
  exact q,
  right,
  exact p,
  intro npnq,
  intro pq,
  cases pq with p q,
  cases npnq,
  exact npnq(q),
  exact npnq(p),
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro npq,
  split,
  intro p,
  apply npq,
  left,
  exact p,
  intro q,
  apply npq,
  right,
  exact q,
  intro npnq,
  cases npnq with np nq,
  intro npq,
  apply np,
  cases npq,
  exact npq,
  exfalso,
  exact nq(npq),
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  cases qr with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  cases pqpr,
  cases pqpr with p q,
  split,
  exact p,
  left,
  exact q,
  cases pqpr with p q,
  split,
  exact p,
  right,
  exact q,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split,
  cases pqr,
  left,
  exact pqr,
  cases pqr with q r,
  right,
  exact q,
  cases pqr,
  left,
  exact pqr,
  cases pqr with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq,
  left,
  exact pq,
  cases pr,
  left,
  exact pr,
  right,
  split,
  exact pq,
  exact pr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  apply pqr,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pqr,
  intro pq,
  cases pq with p q,
  apply pqr,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p pq,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp,
  exact pp,
  exact pp,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nep,
  intro a,
  intro p,
  apply nep,
  existsi a, 
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro tp,
  intro nep,
  cases nep with q p2,
  have np:= tp q,
  apply np,
  exact p2,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro np,
  by_contradiction h,
  apply np,
  intro x,
  by_contradiction h1,
  apply h,
  existsi x,
  exact h1,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro enp,
  intro ap,
  cases enp with x np,
  have px:= ap x,
  have false := np px,
  exact false,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro np,
  by_contradiction h,
  apply np,
  intro x,
  by_contradiction h1,
  apply h,
  existsi x,
  exact h1,
  intro enp,
  intro ap,
  cases enp with x np,
  have px:= ap x,
  have false:= np px,
  exact false,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro exU,
  intro axU,
  cases exU with p xU,
  have npx:= axU p,
  have f:false := npx xU,
  exact f,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro axU,
  intro exU,
  cases exU with p xU,
  have npx:= axU p,
  have f:false := xU npx,
  exact f,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
