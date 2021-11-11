Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section original_spp_inverse_projection_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma original_spp__inverse_projection_postulate :
  alternative_strong_parallel_postulate -> inverse_projection_postulate.
Proof.
  intros ospp A B C P Q Hacute Hout HPQ HPer HCop.
  统计不重合点.
  assert_cols.
  elim(共线的决定性 A B C).
  { intro.
    exists P.
    split; Col.
    apply (l6_7 _ _ A); auto.
    apply not_bet_out; Col.
    intro.
    destruct Hacute as [x [y [z [HPer2 Hlta]]]].
    统计不重合点.
    assert(HN := 两角度不可能互相小于对方 A B C x y z).
    apply HN.
    split; auto.
    split.
    apply l11_31_1_任何角小于等于平角_Bet表述; Between.
    intro; destruct Hlta; 等角.
  }
  intro HNCol1.
  assert(HNCol2 : ~ Col B P Q) by (apply 成直角三点不共线; auto).
  assert(HQ0 := cop_not_par_same_side A B Q P P C).
  destruct HQ0 as [Q0 []]; Col; Cop.
    intro; apply HNCol2; ColR.
  assert(HNCol3 : ~ Col A B Q0) by (apply (one_side_not_col123 _ _ _ C); Side).
  assert(P<>Q0) by (intro; subst; Col).
  assert (HSuma := 和角的存在性 C B P B P Q0).
  destruct HSuma as [D [E [F]]]; auto.

  assert(HY := ospp C B P Q0 D E F).
  destruct HY as [Y []]; auto.
    apply (col_one_side _ A); Side.
  { intro.
    assert(Hlta : 角度小于 A B C C B P).
    { apply acute_per__lta; auto.
      apply (一角加上直角为平角则该角为直角 _ _ _ B P Q0 D E F); auto.
      apply 直角的对称性.
      apply (l8_3_直角边共线点也构成直角1 Q); Perp; Col.
    }
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    apply 等角的右交换性.
    apply l6_6 in Hout.
    apply out2__conga; try (apply out_trivial); auto.
  }

  exists Y.
  split; [|ColR].
  assert(HB0 := l10_15 A B B C).
  destruct HB0 as [B0 []]; Col.
  assert(HNCol4 : ~ Col A B B0) by (apply (one_side_not_col123 _ _ _ C); Side).
  assert(HNCol5 : ~ Col B C P) by (intro; apply HNCol1; ColR).
  统计不重合点.
  assert(P<>Y) by (intro; subst; auto).
  apply (col_one_side_out _ B0); auto.
  apply (one_side_transitivity _ _ _ P).
  apply (one_side_transitivity _ _ _ A).
  - apply invert_one_side.
    apply 角内点和一端点在角另一边同侧; Col.
    { intro.
      assert(HInter := l8_16_1_共线四点和一垂直推另一直角 B0 B A C B).
      destruct HInter; Col; Perp.
      assert(Habs : 角度小于 A B C A B C) by (apply acute_per__lta; auto).
      destruct Habs; 等角.
    }
    apply l11_24_在角内的对称性.
    apply lea_in_angle; Side.
    apply 角度小于蕴含角度小于等于.
    apply acute_per__lta; auto.
    apply L形垂直转直角1; Perp.

  - apply out_one_side; Col.

  - apply l12_6.
    assert(HPar : Par B B0 P Y).
    { apply (l12_9 _ _ _ _ A B); Perp; Cop.
      apply coplanar_trans_1 with C; Col; Cop.
      apply 垂直的右交换性.
      apply (垂线共线点也构成垂直2 _ _ _ P); Col.
      apply 垂直的对称性.
      apply (垂线共线点也构成垂直2 _ _ _ Q); Perp; ColR.
    }
    destruct HPar; auto.
    exfalso.
    分离合取式.
    apply HNCol2; ColR.
Qed.

End original_spp_inverse_projection_postulate.