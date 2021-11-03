Require Export GeoCoq.Tarski_dev.Ch05_bet_le.
Require Import GeoCoq.Utils.all_equiv.

Section Equivalence_between_decidability_properties_of_basic_relations.

Context `{Tn:无维度中性塔斯基公理系统}.

Lemma 等长的决定性_eq_dec :
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
    intros H A B.
    elim (H A B A A); intro HCong.
      left; apply 等长的同一性 with A; assumption.
    right; intro; subst; apply HCong.
    apply 等长的伪自反性.
Qed.

Lemma eq_dec_等长的决定性 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D).
Proof.
intro eq_dec.
apply (@等长的决定性 Tn (Build_无维度中性塔斯基公理系统_带两点重合决定性 Tn eq_dec)).
Qed.

Lemma 中间性的决定性_eq_dec :
  (forall A B C, Bet A B C \/ ~ Bet A B C) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
intros.
induction (H A B A).
left; apply 中间性的同一律; assumption.
right; intro; subst; apply H0;  apply ABB中间性.
Qed.

Lemma eq_dec_中间性的决定性 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C, Bet A B C \/ ~ Bet A B C).
Proof.
intro eq_dec.
apply (@中间性的决定性 Tn (Build_无维度中性塔斯基公理系统_带两点重合决定性 Tn eq_dec)).
Qed.

Definition decidability_of_equality_of_points := forall A B:Tpoint, A=B \/ A<>B.

Definition decidability_of_congruence_of_points := forall A B C D:Tpoint,
  Cong A B C D \/ ~ Cong A B C D.

Definition decidability_of_betweenness_of_points := forall A B C:Tpoint,
  Bet A B C \/ ~ Bet A B C.

Theorem equivalence_between_decidability_properties_of_basic_relations :
  all_equiv  (decidability_of_equality_of_points::
              decidability_of_congruence_of_points::
              decidability_of_betweenness_of_points::nil).
Proof.
apply all_equiv__equiv.
simpl.
unfold decidability_of_equality_of_points, decidability_of_congruence_of_points,
        decidability_of_betweenness_of_points.
assert (P:=等长的决定性_eq_dec).
assert (Q:=eq_dec_等长的决定性).
assert (R:=中间性的决定性_eq_dec).
assert (S:=eq_dec_中间性的决定性).
repeat split; auto.
Qed.

End Equivalence_between_decidability_properties_of_basic_relations.
