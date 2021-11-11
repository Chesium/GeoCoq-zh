Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.circles.

Section Dedekind_circle_circle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** This proof is inspired by Franz Rothe's proof of Theorem 8.5 in Several topics from geometry *)

Lemma circle_circle_aux : (forall A B C D P Q,
  在圆上 P C D -> 在圆上 Q C D -> 在圆内 P A B -> 在圆外 Q A B ->
  OS A C P Q \/ (Col P A C /\ ~ Col Q A C) \/ (~ Col P A C /\ Col Q A C ) ->
  exists Z : Tpoint, 在圆上 Z A B /\ 在圆上 Z C D) ->
  circle_circle.
Proof.
  intro Haux.
  cut (forall A B C D P Q,
  在圆上 P C D -> 在圆上 Q C D -> 在圆内 P A B -> 在圆外 Q A B ->
  共面 A C P Q -> (~ Col P A C \/ ~ Col Q A C) ->
  exists Z : Tpoint, 在圆上 Z A B /\ 在圆上 Z C D).
  - intros Haux' A B C D P Q HPOn HQOn HPIn HQOut.
    assert (HQ' : exists Q', 在圆上 Q' C D /\ 在圆上或圆外 Q' A B /\ Col Q' A C).
    { destruct (由一点往一方向构造等长线段 A C C D) as [Q' []].
      exists Q'.
      repeat split; Col.
      apply 长度小于等于的传递性 with A Q; trivial.
      apply triangle_inequality with C; trivial.
      apply 等长的传递性 with C D; Cong.
    }
    clear dependent Q.
    destruct HQ' as [Q [HQOn [HQOut HCol]]].
    destruct (等长的决定性 A P A B).
      exists P; split; trivial.
    destruct (等长的决定性 A B A Q).
      exists Q; Circle.
    assert (HPInS : 在圆内 P A B) by (split; trivial).
    assert (HQOutS : 在圆外 Q A B) by (split; trivial).
    assert (A <> C).
    { intro; subst C.
      apply (两长度不可能互相小于对方 A B A P); split; trivial.
      apply (等长保持小于关系 A B A Q); Cong.
      apply 等长的传递性 with A D; Cong.
    }
    assert (C <> D).
      intro; treat_equalities; apply (两长度不可能互相小于对方 A C A B); split; trivial.
    destruct (共线的决定性 P A C); [|apply Haux' with P Q; Cop].
    destruct (exists_cong_per A C C D) as [R [HR1 HR2]].
    统计不重合点.
    apply 成直角三点不共线 in HR1; auto.
    destruct (点与圆的位置关系的决定性 A B R) as [HOn|HNOn].
      exists R; split; trivial.
    destruct HNOn; [apply Haux' with R Q|apply Haux' with P R]; Col; Cop.

  - intros A B C D P Q HPOn HQOn HPIn HQOut HCop HDij.
    destruct (共线的决定性 P A C) as [HCol|HNCol].
    { destruct HDij.
        contradiction.
      apply Haux with P Q; auto.
    }
    destruct (共线的决定性 Q A C).
      apply Haux with P Q; auto.
    destruct (cop__one_or_two_sides A C P Q); trivial; [|apply Haux with P Q; auto].
    destruct (l10_2_existence A C P) as [P' HP'].
    统计不重合点.
    apply Haux with P' Q; trivial.
      apply 等长的传递性 with C P; trivial.
      apply 等长的交换性, (is_image_col_cong A C); Col.
      apply 等长保持小于关系 with A P A B; Cong.
      apply 等长的对称性, 等长的交换性, (is_image_col_cong A C); Col.
    left.
    exists P; split; Side.
    apply l10_14; auto.
    intro; subst; apply HNCol, l10_8, HP'.
Qed.

Lemma fod__circle_circle : first_order_dedekind -> circle_circle.
Proof.
  intro dedekind.
  apply circle_circle_aux.
  intros A B C D P Q HPOn HQOn HPIn HQOut HDij.
  assert (A <> C).
  { intro; subst C.
    apply (两长度不可能互相小于对方 A B A P); split; trivial.
    apply (等长保持小于关系 A B A Q); Cong.
    apply 等长的传递性 with A D; Cong.
  }
  assert (P <> Q) by (intro; apply (两长度不可能互相小于对方 A P A B); subst; split; trivial).
  assert (C <> D) by (intro; treat_equalities; auto).
  assert (HOS : forall X Y, Bet P X Q -> Bet P Y Q -> X <> P -> X <> Q -> Y <> P -> Y <> Q -> OS A C X Y).
  { intros X Y; intros.
    destruct HDij as [HOS|[[HP HQ]|[HQ HP]]].
    - apply one_side_transitivity with P; [apply one_side_symmetry|]; apply l9_17 with Q; trivial.
    - apply one_side_transitivity with Q; [apply one_side_symmetry|];
      apply out_one_side_1 with P; Col; apply l6_6, bet_out; auto.
    - apply one_side_transitivity with P; [apply one_side_symmetry|];
      apply out_one_side_1 with Q; Col; apply l6_6, bet_out; Between.
  }
  assert (HNTS : forall X Y, Bet P Y Q -> Bet P X Y -> ~ TS A C X Y).
  { intros X Y HX HY HTS.
    absurd (TS A C P Q).
    - destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]]; [apply l9_9_bis; trivial|intro..].
        apply (two_sides_not_col A C P Q); Col.
        apply (two_sides_not_col A C Q P); Col; Side.
    - apply bet_ts__ts with Y; trivial.
      apply l9_2, bet_ts__ts with X; Side; Between.
  }
  assert (HLta : 角度小于 A C P A C Q).
  { apply t18_19; Cong.
      intro; treat_equalities; auto.
      apply 等长的传递性 with C D; Cong.
      apply 长度小于的交换性, 长度小于的传递性 with A B; trivial.
  }
  assert (HNCol1 : ~ Col P Q C).
  { intro.
    destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]];
      [|apply HNCol; ColR..].
    destruct HLta as [_ HN等角].
    apply HN等角, out2__conga.
      apply out_trivial; auto.
    apply col_one_side_out with A; Col; Side.
  }

  assert (Haux : forall X Y X0 Y0, Bet P Y Q -> X <> Y ->
    在圆上 X0 C D -> Out C X X0 -> 在圆上 Y0 C D -> Out C Y Y0 -> Bet P X Y -> Lt A X0 A Y0).
  { intros X Y X0 Y0; intros.
    apply t18_18 with C C; Cong.
      apply 等长的传递性 with C D; Cong.
    apply 角度小于的交换性, (conga_preserves_lta A C X A C Y).
      apply out2__conga; [apply out_trivial|apply l6_6]; auto.
      apply out2__conga; [apply out_trivial|apply l6_6]; auto.
    split.
    { apply inangle__lea.
      统计不重合点.
      apply l11_24_在角内的对称性, in_angle_trans with P.
        repeat split; auto; exists X; split; Between; right; apply out_trivial; auto.
      apply in_angle_trans2 with Q.
        repeat split; auto.
        exists Y; split; Between.
        right; apply out_trivial; auto.
      destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]].
      - apply l11_24_在角内的对称性, lea_in_angle; [Lea|Side].
      - apply out341__inangle; auto.
        apply not_bet_out; Col.
        intro; apply (lta__nlea A C P A C Q); Lea.
      - apply 任何点都在平角内; auto.
        apply 中间性的对称性, not_out_bet; Col.
        intro; apply (lta__nlea A C P A C Q); trivial.
        apply l11_31_1_任何角小于等于平角_Out表述; auto.
    }
    intro.
    destruct (conga_cop__or_out_ts A C X Y); trivial.
    - assert (Col P Q X) by ColR.
      apply coplanar_pseudo_trans with P Q C; [assumption| |Cop..].
      destruct HDij as [|[[]|[]]]; Cop.
    - absurd (X = Y); trivial; 统计不重合点; apply (l6_21_两线交点的唯一性 P Q C X); ColR.
    - apply (HNTS X Y); trivial.
  }

  assert (HR : exists R, forall X Y,
    (Bet P X Q /\ (exists X0, 在圆上 X0 C D /\ Out C X X0 /\ 在圆上或圆内 X0 A B)) ->
    (Bet P Y Q /\ (exists Y0, 在圆上 Y0 C D /\ Out C Y Y0 /\ 在圆上或圆外 Y0 A B)) ->
    Bet X R Y).
  { apply dedekind; [repeat constructor..|].
    exists P.
    intros X Y [HX [X0]] [HY [Y0]].
    destruct (l5_3 P X Y Q); trivial.
    destruct (两点重合的决定性 X Y).
      subst; Between.
    exfalso.
    分离合取式.
    apply (小于推出反向不小于等于 A Y0 A X0).
      apply (Haux Y X); auto.
    apply 长度小于等于的传递性 with A B; trivial.
  }
  assert (HP : exists X0, 在圆上 X0 C D /\ Out C P X0 /\ 在圆上或圆内 X0 A B).
    exists P; repeat (split; Circle); apply out_trivial; 统计不重合点; auto.
  assert (HQ : exists Y0, 在圆上 Y0 C D /\ Out C Q Y0 /\ 在圆上或圆外 Y0 A B).
    exists Q; repeat (split; Circle); apply out_trivial; 统计不重合点; auto.
  destruct HR as [R HR].
  assert (HBet : Bet P R Q) by (apply HR; split; Between).
  assert (R <> C) by (intro; subst; apply HNCol1; Col).
  destruct (onc_exists C D R) as [Z [HZ1 HZ2]]; auto.
  exists Z; split; trivial.
  assert (A <> B) by (apply (小于推出不重合 A P), HPIn).
  destruct (点与圆的位置关系的决定性 A B Z) as [|[Habs|Habs]]; trivial; exfalso.


  - assert (Q <> R).
    { intro; subst R.
      assert (Q = Z) by (apply (inc_onc2_out__eq C D C); Circle).
      subst.
      apply 在圆外等价于不在圆上或圆内 in HQOut; Circle.
    }
    assert (HNCol2 : ~ Col C Q R) by (intro; apply HNCol1; ColR).
    assert (HT : exists T, 在圆上 T A B /\ Bet A Z T).
    { destruct (两点重合的决定性 Z A).
        subst; exists B; split; Circle; Between.
      destruct (onc_exists A B Z) as [T [HT1 HT2]]; auto.
      exists T; split; trivial.
      apply l6_13_1; trivial.
      apply (l5_6_等长保持小于等于关系 A Z A B); Cong; Le.
    }
    destruct HT as [T [HT1 HT2]].
    assert (T <> Z).
      intro; subst; apply 在圆内等价于不在圆上或圆外 in Habs; apply Habs; Circle.
    destruct (ex_四点成首末边等长双直角S形则对边等长 C R Z Q T Z) as [I [HI1 [HI2 HI3]]]; Col.
    统计不重合点.
    assert (HNCol3 : ~ Col I Z C) by (apply 成直角三点不共线; auto).
    destruct (onc_exists C D I) as [X0 [HX0On HX0Out]]; auto.
    assert (HLt : Lt C X0 C I).
    { destruct (l11_46 I Z C) as [_ HLt]; auto.
        apply (等长保持小于关系 Z C I C); trivial.
          apply 等长的传递性 with C D; Cong.
          Cong.
    }
    assert (X0 <> I) by (intro; apply (nlt C I); subst; assumption).
    assert (HNCol4 : ~ Col I X0 Z) by (intro; apply (one_side_not_col123 C R I Q); ColR).
    assert (HLt1 : Lt X0 Z I Z).
    { 统计不重合点.
      destruct (l11_46 I X0 Z); auto.
      right.
      apply acute_bet__obtuse with C; auto.
        apply l6_13_1; [apply l6_6|]; Le.
      统计不重合点; apply cong__acute; auto.
      apply 等长的传递性 with C D; Cong.
    }

    assert (HX0In : 在圆内 X0 A B).
    { destruct (le_bet Z T Z X0) as [M [HM1 HM2]].
        apply (l5_6_等长保持小于等于关系 X0 Z I Z); Cong; Le.
      assert (HMT : M <> T).
      { intro.
        apply (nlt Z M).
        apply (等长保持小于关系 X0 Z I Z); trivial; [|subst M; apply 等长的传递性 with T Z]; Cong.
      }
      apply 长度小于等于_小于_传递性 with A M.
      - apply triangle_inequality with Z; Cong; eBetween.
      - apply (等长保持小于关系 A M A T); Cong.
        assert (Bet A M T) by eBetween.
        split; Le.
        intro.
        apply HMT, (between_cong A); assumption.
    }
    统计不重合点.
    assert (HX : 在角内 X0 R C Q).
    { apply l11_25 with X0 Z Q; try (apply out_trivial); auto.
      apply lea_in_angle.
      - apply t18_19; auto.
          apply 等长的传递性 with C D; Cong.
          Cong.
        apply 长度小于_小于等于_传递性 with I Z; trivial.
        apply (l5_6_等长保持小于等于关系 T Z Q Z); Cong.
        assert (HLe : Le A T A Q) by (apply (l5_6_等长保持小于等于关系 A B A Q); Cong; Le).
        destruct (两点重合的决定性 A Z).
          subst; Le.
        destruct (l5_5_1 A T A Q) as [M [HM1 HM2]]; trivial.
        assert (Bet A Z M) by eBetween.
        apply 长度小于等于的传递性 with M Z.
          apply bet__le2313; eBetween.
        apply 长度小于等于的交换性, (triangle_reverse_inequality A); Cong.
        apply bet_out; auto.
      - apply invert_one_side, col_one_side with R; Col.
        apply one_side_transitivity with I; Side.
        apply out_one_side; trivial.
        left; apply one_side_not_col123 with Q; trivial.
    }
    destruct HX as [_ [_ [_ [X [HX1 [HX2|HX2]]]]]].
      subst; apply HNCol2; Col.
    assert (X = R).
      apply 双中间性推出点重合 with Q; trivial.
      apply HR; split; [eBetween|..]; Between.
      exists X0; repeat (split; Circle).
    subst; apply HNCol4; ColR.


  - assert (P <> R).
    { intro; subst R.
      assert (P = Z) by (apply (inc_onc2_out__eq C D C); Circle).
      subst.
      apply 在圆内等价于不在圆上或圆外 in HPIn; Circle.
    }
    assert (HNCol2 : ~ Col C P R) by (intro; apply HNCol1; ColR).
    destruct (onc_exists A B Z) as [T [HT1 HT2]]; auto.
      apply (小于推出不重合 A B), 长度小于的右交换性, Habs.
    assert (HT3 : Bet A T Z).
    { apply l6_13_1.
        apply l6_6, HT2.
      apply (l5_6_等长保持小于等于关系 A B A Z); Cong; Le.
    }
    assert (T <> Z).
      intro; subst; apply 在圆外等价于不在圆上或圆内 in Habs; apply Habs; Circle.
    destruct (ex_四点成首末边等长双直角S形则对边等长 C R Z P T Z) as [I [HI1 [HI2 HI3]]]; Col.
    统计不重合点.
    assert (HNCol3 : ~ Col I Z C) by (apply 成直角三点不共线; auto).

    destruct (onc_exists C D I) as [Y0 [HY0On HY0Out]]; auto.
    assert (HLt : Lt C Y0 C I).
    { destruct (l11_46 I Z C) as [_ HLt]; auto.
        apply (等长保持小于关系 Z C I C); trivial.
          apply 等长的传递性 with C D; Cong.
          Cong.
    }
    assert (Y0 <> I) by (intro; apply (nlt C I); subst; assumption).
    assert (HNCol4 : ~ Col I Y0 Z) by (intro; apply (one_side_not_col123 C R I P); ColR).
    assert (HLt1 : Lt Y0 Z I Z).
    { 统计不重合点.
      destruct (l11_46 I Y0 Z); auto.
      right.
      apply acute_bet__obtuse with C; auto.
        apply l6_13_1; [apply l6_6|]; Le.
      统计不重合点; apply cong__acute; auto.
      apply 等长的传递性 with C D; Cong.
    }

    assert (HY0OutC : 在圆外 Y0 A B).
    { destruct (le_bet Z T Z Y0) as [M [HM1 HM2]].
        apply (l5_6_等长保持小于等于关系 Y0 Z I Z); Cong; Le.
      assert (HTM : T <> M).
      { intro.
        apply (nlt Z M).
        apply (等长保持小于关系 Y0 Z I Z); trivial; [|subst M; apply 等长的传递性 with T Z]; Cong.
      }
      apply 长度小于_小于等于_传递性 with A M.
      - apply (等长保持小于关系 A T A M); Cong.
        assert (Bet A T M) by eBetween.
        split; Le.
        intro.
        apply HTM, (between_cong A); assumption.
      - apply (triangle_reverse_inequality Z); Cong.
        统计不重合点; apply l6_6, bet_out; eBetween.
    }
    统计不重合点.
    assert (HY : 在角内 Y0 P C R).
    { apply l11_25 with Y0 P Z; try (apply out_trivial); auto.
      apply l11_24_在角内的对称性, lea_in_angle.
      - apply t18_19; auto.
          apply 等长的传递性 with C D; Cong.
          Cong.
        apply 长度小于_小于等于_传递性 with I Z; trivial.
        apply (l5_6_等长保持小于等于关系 T Z P Z); Cong.
        destruct (le_bet A T A P) as [M [HM1 HM2]].
          apply (l5_6_等长保持小于等于关系 A P A B); Cong; Le.
        assert (Bet A M Z) by eBetween.
        destruct (两点重合的决定性 M A).
          treat_equalities; Le.
        apply 长度小于等于的传递性 with M Z.
          apply bet__le2313; eBetween.
        apply 长度小于等于的交换性, (triangle_reverse_inequality A); Cong.
        apply l6_6, bet_out; auto.
      - apply invert_one_side, col_one_side with R; Col.
        apply one_side_transitivity with I; Side.
        apply out_one_side; trivial.
        left; apply one_side_not_col123 with P; trivial.
    }
    destruct HY as [_ [_ [_ [Y [HY1 [HY2|HY2]]]]]].
      subst; apply HNCol2; Col.
    assert (Y = R).
      apply 双中间性推出点重合 with P; apply 中间性的对称性; trivial.
      apply HR; split; [Between..| |]; [eBetween|].
      exists Y0; repeat (split; Circle).
    subst; apply HNCol4; ColR.
Qed.

End Dedekind_circle_circle.