Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section tarski_playfair.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma tarski_s_euclid_implies_playfair :
 tarski_s_parallel_postulate ->
 playfair_s_postulate.
Proof.
assert (HAux:  tarski_s_parallel_postulate ->
  forall A1 A2 B1 B2 C1 C2 P, ~ Col P A1 A2 ->
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2).
  {
intros HTE; intros.
apply par_distincts in H0.
apply par_distincts in H2.
分离合取式.
assert(HPar1 : 严格平行 A1 A2 B1 B2) by (apply (par_not_col_strict _ _ _ _ P); Col; intro; apply H; Col).
assert(HPar2 : 严格平行 A1 A2 C1 C2) by (apply (par_not_col_strict _ _ _ _ P); Col; intro; apply H; Col).
elim (line_dec B1 B2 C1 C2); intro HLine.

  assumption.

  assert (HLineNew : ~ Col C1 B1 B2 \/ ~ Col C2 B1 B2) by (induction (共线的决定性 C1 B1 B2); induction (共线的决定性 C2 B1 B2);tauto).
  clear HLine; rename HLineNew into HLine.
  assert(HC' : exists C', Col C1 C2 C' /\ TS B1 B2 A1 C').
    {
    assert (共面 A1 A2 P A1) by (exists A1; left; split; Col).
    apply 平行蕴含共面 in H0.
    apply 平行蕴含共面 in H2.
    assert (共面 A1 A2 P B1) by (apply 等价共面ABDC, col_cop__cop with B2; Col).
    assert (共面 A1 A2 P B2) by (apply 等价共面ABDC, col_cop__cop with B1; Col; Cop).
    assert (共面 A1 A2 P C1) by (apply 等价共面ABDC, col_cop__cop with C2; Col).
    assert (共面 A1 A2 P C2) by (apply 等价共面ABDC, col_cop__cop with C1; Col; Cop).
    elim HLine; clear HLine; intro HNC;
    [destruct (cop_not_par_other_side B1 B2 C1 C2 P A1) as [C' [HCol HTS]]|
     destruct (cop_not_par_other_side B1 B2 C2 C1 P A1) as [C' [HCol HTS]]];
    try exists C'; Col; try (intro; apply HPar1; exists A1; Col);
    apply coplanar_pseudo_trans with A1 A2 P; Col.
    }
  ex_and HC' C'.
  unfold TS in H9.
  assert (~ Col A1 B1 B2) by (分离合取式; auto).
  分离合取式.
  ex_and H12 B.
  double C' P C.
  unfold 中点 in H14.
  分离合取式.
  assert(HD : exists D, Bet B D C /\ Bet P D A1) by (apply 帕施公理 with C'; Between).
  ex_and HD D.
  assert(C' <> P) by (intro; subst C'; contradiction).
  assert (Par A1 A2 C' P) by (apply par_col2_par with C1 C2; Col).
  assert(HPar3 : 严格平行 A1 A2 C' P) by (apply (par_not_col_strict _ _ _ _ P); Col).
  assert(B <> P).
    intro.
    subst B.
    apply (par_not_col _ _ _ _ A1) in HPar3.
      apply HPar3; Col.
      Col.
  assert(P <> C).
    intro.
    treat_equalities.
    absurde.

  assert(P <> D) by (intro; subst D; apply H11; ColR).

  assert(HE := HTE P B C D A1 H17 H16 H22).
  ex_and HE X; ex_and H23 Y.
  assert(Hx := l12_6 A1 A2 P X).

  assert (P<>X)
    by (intro;treat_equalities;intuition).

  assert(严格平行 A1 A2 P X) by (apply (par_strict_col2_par_strict _ _ B1 B2); trivial; ColR).
  apply Hx in H27.
  assert(Hy := l12_6 A1 A2 P Y).

  assert (P<>Y)
    by (intro;treat_equalities;intuition).

  assert(HPar4 : 严格平行 A1 A2 P Y) by (apply (par_strict_col2_par_strict _ _ C1 C2); trivial; ColR).
  apply Hy in HPar4.
  assert(HOS : OS A1 A2 X Y)
     by (apply one_side_transitivity with P; Side).
  apply col_one_side_out in HOS; Col.
  exfalso.
  apply (not_bet_and_out X A1 Y); split; assumption.
  }
intros HTE A1; intros.
assert( A1 <> A2 /\ B1 <> B2) by (apply par_distinct;auto).
assert( A1 <> A2 /\ C1 <> C2) by (apply par_distinct;auto).
分离合取式.
clear H4.
induction(共线的决定性 P A1 A2).
  (** If P is one line A1A2 then line A1A2=B1B2=C1C2 and we can conclude. *)
  induction H.

    exfalso.
    apply H.
    exists P.
    split; Col.

    induction H1.

      exfalso.
      apply H1.
      exists P.
      split; Col.

      分离合取式.
      split;ColR.
  (** In the other case we use the previous lemma. *)
  apply (HAux HTE A1 A2 _ _ _ _ P); auto.
Qed.

End tarski_playfair.