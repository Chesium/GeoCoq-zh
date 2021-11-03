Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Tarski_dev.Annexes.sums.

Require Import GeoCoq.Utils.all_equiv.

Import circles.

Section Elementary_Continuity_Props.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(**    All these properties are known to be equivalent in an arbitrary Hilbert plane (Tarski_2D)
  as shown by Strommer, but we don't have formalized the proof yet.

  We have the following proofs:
  - five equivalent variants of the circle-circle continuity axiom;
  - three equivalent variants of the line-circle continuity axiom;
  - the implication from the circle-circle continuity axiom to the line-circle continuity axiom.

  Since we have proved the circle-circle continuity axiom to follow from Tarski's axiom of continuity,
  all these properties do.
*)

Lemma segment_circle__one_point_line_circle : segment_circle <-> one_point_line_circle.
Proof.
  unfold segment_circle, one_point_line_circle.
  split.
  - intros Hsc A B U V P HCol HUV HBet.
    destruct (两点重合的决定性 A B).
      unfold 在圆上或圆内, 在圆上 in *.
      treat_equalities.
      exists A; Cong.
    assert (HPIn : 在圆上或圆内 P A B) by (apply bet__le1213; assumption).
    destruct (每组共线三点都有另一共线点 U V P) as [W [HUW [HVW [HPW HCol2]]]]; trivial.
    destruct (两点重合的决定性 A P).
    { subst P.
      destruct (由一点往一方向构造等长线段 W A A B) as [Q [HQ1 HQ2]].
      destruct (Hsc A B A Q) as [Z [HZ1 HZ2]]; trivial.
        apply 等长则小于等于; Cong.
      exists Z; split; trivial.
      ColR.
    }
    destruct (由一点往一方向构造等长线段 W P P A) as [Q0 [HQ01 HQ02]].
    destruct (由一点往一方向构造等长线段 P Q0 A B) as [Q [HQ1 HQ2]].
    destruct (Hsc A B P Q) as [Z [HZ1 HZ2]]; trivial.
      apply (l5_6_等长保持小于等于关系 Q Q0 Q A); Cong.
      apply (triangle_reverse_inequality P); Cong.
      assert_diffs.
      apply l6_6, bet_out; auto.
    exists Z; split; trivial.
    ColR.

  - intros Hoplc A B P Q HPIn HQOut.
    destruct (两点重合的决定性 A B).
      unfold 在圆上或圆内 in HPIn; treat_equalities.
      exists A; split; Between; Circle.
    destruct (两点重合的决定性 P Q).
      subst Q; exists P; split; Between; Circle.
    destruct (等长的决定性 A B A Q) as [HCong|HNCong].
      exists Q; split; Between; Circle.
    assert (HB' : exists B', Cong A B A B' /\ Bet A P B').
    { destruct (两点重合的决定性 A P).
        subst; exists B; split; Cong; Between.
      destruct (l6_11_existence A A B P) as [B' [HOut HCong]]; auto.
      exists B'; split; Cong.
      apply l6_13_1.
        apply l6_6, HOut.
      apply (l5_6_等长保持小于等于关系 A P A B); Cong.
    }
    destruct HB' as [B' [HCong HBet]].
    destruct (Hoplc A B' P Q P) as [Z1 [HCol1 HZ1]]; Col.
    assert (HZ1On: 在圆上 Z1 A B) by (apply 等长的传递性 with A B'; Cong).
    clear dependent B'.
    destruct (or_bet_out P Z1 Q) as [HBet|[HOut|HNCol]];
      [exists Z1; auto| |exfalso; apply HNCol; Col].
    destruct (chord_completion A B Z1 P) as [Z2 [HZ2On HBet]]; trivial.
    exists Z2; split; trivial.
    assert_diffs.
    assert (HBet2 : Bet Z1 Z2 Q).
    { apply out2__bet.
        apply l6_7 with P; trivial.
        apply l6_6, bet_out; auto.
      apply (col_inc2_outcs__out A B); Circle.
        ColR.
      split; trivial.
    }
    eBetween.
Qed.

Lemma one_point_line_circle__two_points_line_circle :
  one_point_line_circle <-> two_points_line_circle.
Proof.
  unfold one_point_line_circle, two_points_line_circle.
  split.
  - intros Hoplc A B U V P HCol HUV HBet.
    destruct (两点重合的决定性 P B) as [Heq|HPB].
      subst P; exists B, B; repeat split; Circle; Between.
    destruct (Hoplc A B U V P HCol HUV HBet) as [Z1 [HZ1Col HZ1On]].
    exists Z1.
    assert (HPIn : 在圆上或圆内 P A B) by (apply bet__le1213, HBet).
    destruct (chord_completion A B Z1 P) as [Z2 [HZ2On HPBet]]; trivial.
    assert (Z1 <> P).
      intro; treat_equalities; apply HPB, between_cong with A; trivial.
    assert_diffs.
    exists Z2; repeat (split; trivial); ColR.

  - intros Htplc A B U V P HCol HUV HBet.
    destruct (Htplc A B U V P HCol HUV HBet) as [Z [_ [HZ1 [HZ2 _]]]].
    exists Z; auto.
Qed.


Lemma circle_circle_bis__circle_circle_axiom : circle_circle_bis <-> circle_circle_axiom.
Proof.
  split; intro cc.
  - intros A B C D B' D' HCong1 HCong2 HBet1 HBet2.
    apply cc with D' B'; try apply bet__le1213; trivial.
  - intros A B C D P Q HPOn HPIn HQOn HQIn.
    assert (HQ' : Le A P A Q) by (apply 长度小于等于的传递性 with A B; Le).
    apply l5_5_1 in HQ'.
    destruct HQ' as [Q' [HBet1 HCong1]].
    assert (HP' : Le C Q C P) by (apply 长度小于等于的传递性 with C D; Le).
    apply l5_5_1 in HP'.
    destruct HP' as [P' [HBet2 HCong2]].
    destruct (cc A Q' C P' Q P) as [Z []]; Cong.
    exists Z; split.
      apply 等长的传递性 with A Q; [apply 等长的传递性 with A Q'|]; Cong.
      apply 等长的传递性 with C P; [apply 等长的传递性 with C P'|]; Cong.
Qed.

Lemma circle_circle__circle_circle_bis : circle_circle -> circle_circle_bis.
Proof.
  intros Hcc A B C D P Q HPOn HPIn HQOn HQIn.
  destruct (两点重合的决定性 P Q).
    subst Q; exists P; split; assumption.
  destruct (chord_completion C D P Q) as [P' [HP'On HBetQ]]; trivial.
  destruct (chord_completion A B Q P) as [Q' [HQ'On HBetP]]; trivial.
  apply (Hcc A B C D P P'); trivial.
  destruct (长度小于等于的决定性 A P' A B); trivial.
  assert (P' = Q).
  { apply 双中间性推出点重合 with Q'.
      eBetween.
    assert_diffs.
    apply (col_inc_onc2__bet A B); trivial; ColR.
  }
  subst.
  apply 等长则小于等于; Cong.
Qed.

Lemma circle_circle_bis__one_point_line_circle :
  circle_circle_bis -> one_point_line_circle.
Proof.
  unfold circle_circle_bis, one_point_line_circle.
  intro Hcc.
  assert (Haux : forall A B U V P, Col U V P -> U <> V -> Bet A P B -> ~ Per A U V ->
      exists Z : Tpoint, Col U V Z /\ 在圆上 Z A B).
  { intros A B U V P HCol HUV HBet HNPer.
    destruct (共线的决定性 U V B) as [|HNCol].
      exists B; split; Circle.
    destruct (两点重合的决定性 A P).
      subst P.
      destruct (每组共线三点都有另一共线点 U V A) as [W [HUW [HVW [HPW HCol2]]]]; trivial.
      destruct (由一点往一方向构造等长线段 W A A B) as [Z [HZ1 HZ2]].
      exists Z; split; trivial; ColR.
    destruct (l10_6_existence U V A) as [C HC].
    destruct (l10_6_existence U V B) as [D HD].
    assert (HBet' : Bet C P D).
      apply image_gen_preserves_bet with A P B U V; trivial.
      left; split; trivial.
      apply col__image_spec, HCol.
    assert (HCong : Cong B P D P) by (apply (is_image_col_cong U V); assumption).
    assert (HDIn : 在圆上或圆内 D A B).
      apply triangle_inequality with P; Cong.
    assert (HBIn : 在圆上或圆内 B C D).
      apply triangle_inequality with P; Cong.
    destruct (Hcc A B C D D B) as [Z0 []]; Circle.
    destruct (circle_circle_cop A B C D Z0 U) as [Z [HZ1 [HZ2 HCop]]]; trivial.
    clear dependent Z0.
    exists Z; split; trivial.
    apply cong_cop_image__col with A C; trivial.
    - intro; treat_equalities.
      assert (Col A U V) by (apply l10_8, HC).
      apply HNCol; ColR.
    - apply 等长的传递性 with A B; trivial.
      apply 等长的传递性 with C D; Cong.
      apply 等长的对称性, l10_10 with U V; assumption.
    - apply coplanar_perm_2.
      apply coplanar_trans_1 with C; Cop.
      intro.
      destruct (两点重合的决定性 A C).
        subst C.
        assert (Col A U V) by (apply l10_8, HC).
        apply HNCol; ColR.
      assert (Habs : 严格对称于 U A C U V).
        apply image_image_in; Col.
        apply is_image_is_image_spec; auto.
      destruct Habs as [_ [|]]; auto.
      apply HNPer.
      destruct (两点重合的决定性 A U).
        subst; Perp.
      apply perp_per_2, perp_left_comm, perp_col with C; Perp; Col.
  }
  intros A B U V P HCol HUV HBet.
  destruct (per_dec A U V); [|apply Haux with P; assumption].
  destruct (Haux A B V U P) as [Z []]; Col.
    intro; apply HUV, l8_7 with A; assumption.
  exists Z; split; Col.
Qed.

Lemma circle_circle__circle_circle_two :
 circle_circle <-> circle_circle_two.
Proof.
  unfold circle_circle, circle_circle_two.
  split.
  { intros Hcc A B C D P Q.
    intros.
    destruct (两点重合的决定性 A C).
    subst C.
      exists P; exists P.
      assert (Cong A B A D).
        apply 长度小于等于的反对称性.
        apply (l5_6_等长保持小于等于关系 A B A Q); Cong.
        apply (l5_6_等长保持小于等于关系 A P A B); Cong.
      assert (Cong A P A B) by (apply 等长的传递性 with A D; Cong).
      repeat split; trivial.
      intro Habs.
      destruct Habs.
      contradiction.
    destruct (Hcc A B C D P Q) as [Z1 [HZ1A HZ1B]]; trivial.
    exists Z1.
    destruct (l10_6_existence A C Z1) as [Z2 HZ2].
    exists Z2.
    assert (Cong Z1 C Z2 C) by (apply (is_image_col_cong A C Z1 Z2 C); Col).
    assert (Cong Z1 A Z2 A) by (apply (is_image_col_cong A C Z1 Z2 A); Col).
    repeat split; trivial; [CongR..|].
    intros.
    intro; subst Z2.
    clean.
    destruct (or_bet_out A C Z1) as [HBet|[HOut|HNCol]].
    - apply (小于推出反向不小于等于 A B A Q); trivial.
      apply l5_6_等长保持小于等于关系 with A Q A Z1; Cong.
      apply triangle_inequality with C; trivial.
      apply 等长的传递性 with C D; Cong.
    - apply (小于推出反向不小于等于 A P A B); trivial.
      apply l5_6_等长保持小于等于关系 with A Z1 A P; Cong.
      apply triangle_reverse_inequality with C; trivial.
      apply 等长的传递性 with C D; Cong.
    - assert (HCol := l10_8 A C Z1 HZ2); Col.
  }
  intros Hcct A B C D P Q.
  intros.
  destruct (Hcct A B C D P Q) as [Z1 [Z2 [HZ1On [HZ1On' _]]]]; trivial.
  exists Z1; auto.
Qed.

Lemma euclid_22_aux : forall A B C D E F A' B' E' F' C1 C2 E1,
  SumS A B C D E' F' -> SumS C D E F A' B' -> Le E F E' F' -> Le A B A' B' ->
  Out A B C1 -> Cong A C1 C D -> Bet B A C2 -> Cong A C2 C D ->
  Out B A E1 -> Cong B E1 E F ->
  Bet C1 E1 C2.
Proof.
  intros A B C D E F A' B' E' F'; intros.
  assert (Bet C1 A C2) by (assert_diffs; apply l6_2 with B; auto).
  apply not_out_bet.
    ColR.
  intro HOut; destruct HOut as [HC1E1 [HC2E1 [HBet|HBet]]].
  - assert (Bet A C1 E1) by eBetween.
    assert (Bet A E1 B).
      apply out2__bet; trivial.
      apply l6_7 with C1; apply l6_6; trivial.
      assert_diffs; apply bet_out; trivial.
    apply (长度小于等于推出反向不小于 A B A' B'); trivial.
    apply le_lt12_sums2__lt with C D E F A E1 E1 B; Sums; Le.
    split.
      exists C1; split; Cong.
    intro HCong.
    apply HC1E1, between_cong with A; trivial.
    apply 等长的传递性 with C D; trivial.
  - assert (Bet A C2 E1) by eBetween.
    assert (Bet B C2 E1) by (assert_diffs; apply l6_2 with A; auto; apply bet_out; Between).
    apply (长度小于等于推出反向不小于 E F E' F'); trivial.
    apply (等长保持小于关系 B C2 B E1); Cong.
      split; [exists C2; Cong|].
      intro HCong.
      apply HC2E1, between_cong with B; trivial.
    apply (sums2__cong56 A B C D); trivial; exists B, A, C2; repeat split; Cong.
Qed.

Lemma circle_circle_bis__euclid_22 : circle_circle_bis -> euclid_s_prop_1_22.
Proof.
  intros Hcc A B C D E F A' B' C' D' E' F' HSum1 HSum2 HSum3 HLe1 HLe2 HLe3.
  exists A, B.
  destruct (两点重合的决定性 A B); [|destruct (两点重合的决定性 C D)]; [| |destruct (两点重合的决定性 E F)].
  - destruct (由一点往一方向构造等长线段_0 C D A) as [P HCong].
    exists P; repeat split; Cong.
    subst B.
    apply 等长的传递性 with C D; trivial.
    apply 长度小于等于的反对称性.
      apply (l5_6_等长保持小于等于关系 C D C' D'); Cong; apply (sums2__cong56 A A E F); Sums.
      apply (l5_6_等长保持小于等于关系 E F E' F'); Cong; apply (sums2__cong56 A A C D); Sums.
  - exists A; treat_equalities; repeat split; Cong.
    apply 长度小于等于的反对称性.
      apply (l5_6_等长保持小于等于关系 A B A' B'); Cong; apply (sums2__cong56 C C E F); Sums.
      apply (l5_6_等长保持小于等于关系 E F E' F'); Cong; apply (sums2__cong56 A B C C); Sums.
  - exists B; treat_equalities; repeat split; Cong.
    apply 长度小于等于的反对称性.
      apply (l5_6_等长保持小于等于关系 A B A' B'); Cong; apply (sums2__cong56 C D E E); Sums.
      apply (l5_6_等长保持小于等于关系 C D C' D'); Cong; apply (sums2__cong56 A B E E); Sums.
  - destruct (由一点往一方向构造等长线段_3 A B C D) as [C1 [HC1 HC1']]; auto.
    destruct (由一点往一方向构造等长线段_3 B A E F) as [E1 [HE1 HE1']]; auto.
    destruct (由一点往一方向构造等长线段 B A C D) as [C2 [HC2 HC2']].
    destruct (由一点往一方向构造等长线段 A B E F) as [E2 [HE2 HE2']].
    assert (Bet C1 E1 C2) by (apply (euclid_22_aux A B C D E F A' B' E' F'); trivial).
    assert (Bet E1 C1 E2) by (apply (euclid_22_aux B A E F C D B' A' C' D'); Sums; Le).
    destruct (Hcc A C1 B E1 E1 C1) as [Z [HZ1 HZ2]]; Circle.
      apply bet_inc2__inc with C1 C2; Circle; apply onc__inc, 等长的传递性 with C D; Cong.
      apply bet_inc2__inc with E1 E2; Circle; apply onc__inc, 等长的传递性 with E F; Cong.
    exists Z; repeat split; Cong.
      apply 等长的传递性 with A C1; Cong.
      apply 等长的传递性 with B E1; Cong.
Qed.

Lemma triangle_inequality1 : forall A B C D E, SumS A B B C D E -> Le A C D E.
Proof.
  intros A B C D E HSum.
  destruct (由一点往一方向构造等长线段 A B B C) as [D' [HBet HCong]].
  apply (l5_6_等长保持小于等于关系 A C A D'); Cong.
    apply triangle_inequality with B; Cong.
  apply (sums2__cong56 A B B C); trivial.
  exists A, B, D'; repeat split; Cong.
Qed.

Lemma euclid_22__circle_circle : euclid_s_prop_1_22 -> circle_circle.
Proof.
  intros p22 A B C D P Q HPOn HQOn HPIn HQOut.
  assert (HXYZ : exists X Y Z : Tpoint, Cong X Y A C /\ Cong X Z A B /\ Cong Y Z C D).
  { destruct (ex_sums A B C D) as [L1 [R1]].
    destruct (ex_sums A C C D) as [L2 [R2]].
    destruct (ex_sums A C A B) as [L3 [R3]].
    apply p22 with L1 R1 L2 R2 L3 R3; trivial.
    - destruct (ex_sums C A A P) as [R [S]].
      apply 长度小于等于的传递性 with R S.
        apply (l5_6_等长保持小于等于关系 C P R S); Cong; apply triangle_inequality1 with A; trivial.
        apply le2_sums2__le with C A A P A C A B; Le.
    - apply 长度小于等于的传递性 with A Q; Le.
      apply (triangle_inequality1 A C Q).
      apply (cong3_sums__sums A C C D L2 R2); Cong.
    - destruct (ex_sums A P P C) as [R [S]].
      apply 长度小于等于的传递性 with R S.
        apply triangle_inequality1 with P; trivial.
      apply le2_sums2__le with A P P C A B C D; Le.
  }
  destruct (两点重合的决定性 A C).
  { subst C.
    exists B; split; Circle.
    apply 长度小于等于的反对称性.
      apply 长度小于等于的传递性 with A Q; Le.
      apply 长度小于等于的传递性 with A P; Le.
  }
  destruct (两点重合的决定性 A B).
  { subst B.
    exists P; split; trivial.
    apply inc_eq in HPIn; subst; Circle.
  }
  destruct HXYZ as [X [Y [Z [HAC [HAB HCD]]]]].
  assert_diffs.
  assert (HZ0 : exists Z0, 等角 Y X Z C A Z0 /\ Cong X Z A Z0).
  { destruct (angle_construction_3 Y X Z C A) as [Z']; auto.
    assert_diffs.
    destruct (由一点往一方向构造等长线段_3 A Z' X Z) as [Z0 []]; auto.
    exists Z0; split; Cong.
    apply l11_10 with Y Z C Z'; [|apply out_trivial..|apply l6_6]; auto.
  }
  destruct HZ0 as [Z0 []].
  exists Z0.
  destruct (l11_49 Y X Z C A Z0); trivial.
  split.
    apply 等长的传递性 with X Z; Cong.
    apply 等长的传递性 with Y Z; Cong.
Qed.

Theorem equivalent_variants_of_circle_circle :
  all_equiv
    (circle_circle::
     circle_circle_two::
     circle_circle_bis::
     circle_circle_axiom::
     euclid_s_prop_1_22::
     nil).
Proof.
  assert (V := circle_circle_bis__circle_circle_axiom).
  assert (W := circle_circle__circle_circle_bis).
  assert (X := circle_circle__circle_circle_two).
  assert (Y := circle_circle_bis__euclid_22).
  assert (Z := euclid_22__circle_circle).
  apply all_equiv__equiv; unfold all_equiv'; simpl; repeat split; tauto.
Qed.

Theorem equivalent_variants_of_line_circle :
  all_equiv
    (segment_circle::
     one_point_line_circle::
     two_points_line_circle::
     nil).
Proof.
  apply all_equiv__equiv; unfold all_equiv'; simpl; repeat split.
    rewrite segment_circle__one_point_line_circle, one_point_line_circle__two_points_line_circle; trivial.
    rewrite segment_circle__one_point_line_circle; trivial.
    rewrite one_point_line_circle__two_points_line_circle; trivial.
Qed.

End Elementary_Continuity_Props.
