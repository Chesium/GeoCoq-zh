Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section midpoint_playfair.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma midpoint_converse_postulate_implies_playfair :
  midpoint_converse_postulate ->
  playfair_s_postulate.
Proof.
intros HT A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim HPar1; clear HPar1; intro HPar1; elim HPar2; clear HPar2; intro HPar2.

  {
  assert (HDiff : P <> A1) by (intro; apply HPar1; exists P; subst; Col).
  assert (HX := 构造对称点 A1 P); destruct HX as [X HMid1].
  revert B1 B2 C1 C2 HCol1 HCol2 HPar1 HPar2.
  assert (Haux : forall B1 B2, Col P B1 B2 -> 严格平行 A1 A2 B1 B2 ->
            exists B3, Col B1 B2 B3 /\ BetS A2 B3 X /\ 严格平行 A1 A2 P B3).
    {
    cut (forall B1 B2, Col P B1 B2 -> 严格平行 A1 A2 B1 B2 -> P <> B1 ->
            exists B3, Col B1 B2 B3 /\ BetS A2 B3 X /\ 严格平行 A1 A2 P B3).
      {
      intros Haux B1 B2 HCol1 HPar1.
      elim (两点重合的决定性 P B1); auto.
      intro.
      assert (P <> B2) by (intro; subst; 统计不重合点; auto).
      destruct (Haux B2 B1) as [B3 []]; Par; Col.
      exists B3; split; Col.
      }
    intros B1 B2 HCol1 HPar1 HPB1.
    统计不重合点.
    destruct (hilbert_s_version_of_pasch X A1 A2 B1 P) as [B3 [HCol HBet]];
    [..|repeat split; Between|].

        {
        apply 等价共面DCAB, col_cop__cop with P; Col.
        apply 等价共面ACBD, col_cop__cop with B2; Col.
        apply 平行蕴含共面; Par.
        }

        {
        apply par_strict_not_col_2 with A1.
        apply par_strict_right_comm, par_strict_col_par_strict with B2; Col.
        }

        {
        intro; apply HPB1, l6_21_两线交点的唯一性 with A1 P B1 P; Col; [|ColR].
        apply par_strict_not_col_2 with A2.
        apply par_strict_comm, par_strict_col_par_strict with B2; Col.
        }

        {
        assert (Col B1 B2 B3) by ColR.
        exists B3; split; trivial.
        unfold BetS in *.
        induction HBet; 分离合取式; [|exfalso; apply HPar1; exists B3; split; Col].
        split; [repeat split; Between|].
        apply par_strict_col2_par_strict with B1 B2; Col.
        intro; treat_equalities; apply HPar1; exists P; split; ColR.
        }
      }
  intros B1 B2 C1 C2 HCol1 HCol2 HPar1 HPar2.
  destruct (Haux B1 B2 HCol1 HPar1) as [B3 [HCol3 [HBet1 HPar3]]].
  destruct (Haux C1 C2 HCol2 HPar2) as [C3 [HCol4 [HBet2 HPar4]]].
  assert (HCol5 : Col A2 X B3) by (unfold BetS in *; 分离合取式; Col).
  assert (HCol6 : Col A2 X C3) by (unfold BetS in *; 分离合取式; Col).
  assert (HNC' : ~ Col A1 A2 X)
    by (intro; apply HPar1; exists P; split; ColR).
  assert (B3 = C3) by (apply 中点的唯一性1 with A2 X; apply HT with A1 P; Col; Par).
  subst; split; ColR.
  }

  {
  分离合取式; exfalso; apply HPar1.
  exists P; split; ColR.
  }

  {
  分离合取式; exfalso; apply HPar2.
  exists P; split; ColR.
  }

  {
  分离合取式; split; ColR.
  }
Qed.

End midpoint_playfair.