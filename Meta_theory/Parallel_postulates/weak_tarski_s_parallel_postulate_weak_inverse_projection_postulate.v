Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma  weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux :
  weak_tarski_s_parallel_postulate ->
  forall A B C P T,
    Per A B C -> 在角内 T A B C ->
    P <> T -> 等角 P B A P B C -> Per B P T -> 共面 A B C P ->
    (exists X, Out B A X /\ Col T P X) \/ (exists Y, Out B C Y /\ Col T P Y).
Proof.
  intros tora A B C P T HPer H在角内 HPT H等角 HPerP HCop.

  assert (HIn : 在角内 P A B C)
    by (apply conga_cop_inangle_per2__inangle with T; assumption).
  assert (H为锐角 : 为锐角 P B A)
    by (apply acute_sym, conga_inangle_per__acute with C; assumption).
  assert (H为锐角' : 为锐角 P B C) by (apply (acute_conga__acute P B A); assumption).
  统计不重合点.
  assert (HPerp : Perp B P P T) by (apply 直角转L形垂直; auto).
  assert (HNCol : ~ Col A B C) by (apply 成直角三点不共线; auto).
  assert (HNCol1 : ~ Col B P T) by (apply 成直角三点不共线; auto).
  destruct (共线的决定性 A B T).
    left; exists T; split; Col.
    apply l6_6, acute_col_perp__out_1 with P; Col.
  destruct (tora A B C T) as [U [V [HU [HV HUTV]]]]; trivial.
  destruct (共线的决定性 P T U) as [HCol|HNCol2].
    left; exists U; split; Col.
  destruct (共线的决定性 P T V) as [HCol|HNCol3].
    right; exists V; split; Col.
  destruct (cop__one_or_two_sides P T B U) as [HTS|HOS]; Col; [CopR|..].
  - destruct HTS as [_ [_ [X [HX1 HX2]]]].
    left; exists X; split; Col.
    apply l6_7 with U; auto.
    统计不重合点; apply l6_6, bet_out; auto.
    intro; subst; apply HNCol1, HX1.
  - assert (HTS : TS P T B V) by (apply l9_8_2 with U; Side; repeat split; [..|exists T; split]; Col).
    destruct HTS as [_ [_ [Y [HY1 HY2]]]].
    right; exists Y; split; Col.
    apply l6_7 with V; auto.
    assert (Y <> B) by (intro; subst; apply HNCol1, HY1).
    统计不重合点; Out.
Qed.

Lemma weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate :
  weak_tarski_s_parallel_postulate -> weak_inverse_projection_postulate.
Proof.
intro wtpp.
cut (forall A B C P T,
       Per A B C -> 在角内 T A B C ->
       P <> T -> 等角 P B A P B C -> 共面 A B C P -> Per B P T ->
       exists X Y, Out B A X /\ Col T P X /\ Out B C Y /\ Col T P Y).

  {
  intros rabp A B C D E F P Q H为锐角 HPerE HSuma HOut HPQ HPerP HCop.
  assert (HNCol1 : ~ Col A B C).
    intro; suma.统计不重合点; apply (成直角三点不共线 D E F); auto.
    apply (两退化角之和退化 A B C A B C); assumption.
  assert (HNCol2 : ~ Col B P Q) by (统计不重合点; apply 成直角三点不共线; auto).
  assert (H等角 : 等角 A B C P B C).
    统计不重合点; apply out2__conga; [apply l6_6|apply out_trivial]; auto.
  assert (HNCol3 : ~ Col P B C) by (apply (不共线三点构成的角的等角三点也不共线 A B C); assumption).
  assert (HPerp : Perp B P P Q) by (apply 直角转L形垂直; 统计不重合点; auto).
  apply 和角的左交换性 in HSuma.
  destruct HSuma as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
  assert (HQ' : exists Q', P <> Q' /\ Col P Q Q' /\ 在角内 Q' C B P).
  { destruct (cop_not_par_same_side B P Q P P C) as [Q0 [HCol HOS]]; Col.
      CopR.
    destruct (one_side_dec B C P Q0).
      exists Q0; split; [统计不重合点; auto|split; [Col|Side]].
    assert (HQ' : exists Q', Col P Q Q' /\ Col B C Q').
    { destruct (共线的决定性 B C Q0).
        exists Q0; Col.
      统计不重合点.
      destruct (cop_nos__ts B C P Q0) as [_ [_ [Q' [HCol' HBet]]]]; Col; Cop.
      exists Q'; split; ColR.
    }
    destruct HQ' as [Q' [HCol1 HCol2]].
    exists Q'.
    assert (P <> Q') by (intro; subst; apply HNCol3; Col).
    split; auto; split; Col.
    apply out321__inangle; auto.
      统计不重合点; auto.
    apply l6_6, (acute_col_perp__out_1 P); Col.
      apply (acute_conga__acute A B C); assumption.
    apply 垂线共线点也构成垂直2 with Q; auto.
  }
  destruct HQ' as [Q' [HPQ' [HCol HInangle]]].
  apply l6_6 in HOut.
  assert (HInangle' : 在角内 Q' C B J).
  { apply in_angle_trans with P; trivial.
    统计不重合点.
    apply l11_25 with A C J; [|apply out_trivial..|]; auto.
    apply os_ts__inangle.
      assert (~ Col A B J) by (apply (不共线三点构成的角的等角三点也不共线 A B C); 等角).
      apply cop_nos__ts; Col; Cop.
    assert (~ Col C B J).
      apply (不共线三点构成的角的等角三点也不共线 D E F); 等角; apply 成直角三点不共线; auto.
    apply invert_one_side, one_side_symmetry, cop_nts__os; Col.
    apply 和角不大于平角推不同侧不异侧_间接 with A B C; 和角.
  }
  destruct (rabp C B J P Q') as [Y [_ [HY1 [HY2 _]]]]; trivial.
    apply (l11_17_等于直角的角是直角 D E F); 等角.
    统计不重合点; apply l11_10 with A C A J; try (apply out_trivial); 等角.
    CopR.
    apply 直角边共线点也构成直角2 with Q; auto.
  exists Y; split; ColR.
  }

  {
  intros A B C P T HPer H在角内 HPT H等角 HCop HPerP.
  assert (HNOut : ~ Out B A C) by (intro; 统计不重合点; apply (成直角三点不共线 A B C); Col).
  assert (HPerp : Perp B P P T) by (统计不重合点; apply 直角转L形垂直; auto).
  destruct (weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux wtpp A B C P T) as [[X [HX1 HX2]]|[Y [HY1 HY2]]]; trivial.
  - destruct (构造对称点 X P) as [Y HY].
    assert (X <> Y).
    { intro; treat_equalities.
      apply HNOut, l6_7 with P; trivial.
      apply (l11_21_a P B A); Out.
    }
    assert (Out B C Y).
    { apply conga_cop_out_reflectl__out with A P X; trivial.
      apply l10_4_spec; split.
        exists P; split; Col.
      left; apply 与垂线共线之线也为垂线3 with P T; ColR.
    }
    exists X, Y; repeat (split; [assumption|]); ColR.
  - destruct (构造对称点 Y P) as [X HX].
    assert (X <> Y).
    { intro; treat_equalities.
      apply HNOut, l6_7 with P; apply l6_6; trivial.
      apply (l11_21_a P B C); [Out|等角].
    }
    assert (Out B A X).
    { apply conga_cop_out_reflectl__out with C P Y; Out; [Cop|等角|].
      apply l10_4_spec; split.
        exists P; split; Col.
      left; apply 与垂线共线之线也为垂线3 with P T; ColR.
    }
    exists X, Y; repeat (split; [try assumption|]); ColR.
  }
Qed.

End weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.