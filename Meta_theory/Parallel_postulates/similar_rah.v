Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section similar_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(**
This is an adaptation of the proof of Martin's Theorem 23.6.
It is more complicated because Martin use the properties of the deflect of a triangle,
which are difficult to handle in our formalization.
*)

Lemma similar__rah_aux : forall A B C D E F,
  ~ Col A B C -> 等角 A B C D E F -> 等角 B C A E F D -> 等角 C A B F D E ->
  角度小于等于 B C A A B C -> Lt D E A B -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HNCol HCongaB HCongaC HCongaA Hlea Hlt.
  assert_diffs.
  destruct (由一点往一方向构造等长线段_3 A B D E) as [G []]; auto.
  rename H into HFD.
  destruct (由一点往一方向构造等长线段_3 A C D F) as [H []]; auto.
  apply (等长保持小于关系 _ _ _ _ A G A B) in Hlt; Cong.
  assert(Bet A G B) by (apply (l6_13_1); Le; apply l6_6; auto).
  assert(B <> G) by (intro; subst; destruct Hlt; Cong).
  assert(HCongaA' : 等角 C A B H A G) by (apply out2__conga; apply l6_6; auto).
  destruct(l11_49 F D E H A G) as [_ [HConga1 HConga2]]; Cong.
    apply (角等的传递性 _ _ _ C A B); 等角.
  apply (角等的传递性 _ _ _ _ _ _ A G H) in HCongaB; auto.
  apply (角等的传递性 _ _ _ _ _ _ G H A) in HCongaC; 等角.
  clear dependent D; clear dependent E; clear dependent F.
  rename HCongaA' into HCongaA.

  assert(HNCol1 : ~ Col A G H) by (apply (不共线三点构成的角的等角三点也不共线 A B C); auto).
  assert(HNCol2 : ~ Col B G H) by (intro; apply HNCol1; ColR).
  assert(严格平行 G H B C).
  { apply (par_not_col_strict _ _ _ _ B); Col.
    apply par_symmetry.
    apply (l12_22_b _ _ _ _ A); 等角.
    apply out_one_side; auto.
  }
  assert(HNCol3 : ~ Col G H C) by (apply (par_strict_not_col_4 _ _ B); auto).
  assert(HNCol4 : ~ Col B C G) by (apply (par_strict_not_col_3 _ H); auto).
  assert(HNCol5 : ~ Col H B C) by (apply (par_strict_not_col_2 G); auto).
  assert_diffs.
  assert(Out C H A).
  { apply (col_one_side_out _ B); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ G).
      apply l12_6; Par.
      apply out_one_side; Col; apply bet_out; Between.
  }
  assert(Bet A H C) by (apply out2__bet; apply l6_6; auto).
  assert(角度之和小于平角 B G H H C B).
  { apply (sams_chara _ _ _ _ _ _ A); Between.
    apply (l11_30_等角保持小于等于 B C A A B C); auto; apply 等角的右交换性; auto.
    apply out2__conga; [apply out_trivial|]; auto.
  }
  assert(等角 A G H G B C).
    apply (l11_10 A G H A B C); try (apply out_trivial); 等角; apply bet_out; Between.
  assert(等角 G H A B C H).
    apply (l11_10 G H A B C A); try (apply out_trivial); 等角.
  assert(角度之和小于平角 B G H C B G) by (apply (conga2_sams__sams B G H H G A); 等角; 和角).
  assert(角度之和小于平角 C H G B C H) by (apply (conga2_sams__sams C H G G H A); 等角; 和角).
  destruct(和角的存在性 B C G C G B) as [I [J [K]]]; auto.
  destruct(和角的存在性 H C G C G H) as [L [M [N]]]; auto.
  suma.assert_diffs.
  destruct(和角的存在性 I J K G B C) as [O [P [Q]]]; auto.
  destruct(和角的存在性 L M N G H C) as [R [S [T]]]; auto.
  destruct(和角的存在性 I J K L M N) as [U [V [W]]]; auto.
  suma.assert_diffs.
  assert(HInter : 角度之和小于平角 I J K L M N /\ 和角 H G B B C H U V W).
  { assert(TS G C B H).
    { apply invert_two_sides, l9_31; Side.
      apply (col_one_side _ A); Col.
      apply invert_one_side; apply out_one_side; try (apply l6_6); Col.
    }
    assert(角度之和小于平角 H G B B C G).
    { apply (sams_lea2__sams _ _ _ _ _ _ H G B B C H); try (apply 任何角小于等于自己); 和角.
      apply inangle__lea.
      apply os_ts__inangle; Side.
    }
    destruct(和角的存在性 B C G H G B) as [X [Y [Z]]]; auto.
    assert(和角 B G C C G H H G B) by 和角.
    assert(角度之和小于平角 B G C C G H).
    { apply os_ts__sams; trivial.
      apply (col_one_side _ A); Col.
      apply invert_one_side, out_one_side; Col.
    }
    assert(角度之和小于平角 I J K C G H) by (apply (sams_assoc B C G C G B _ _ _ _ _ _ H G B); 和角).
    assert(和角 I J K C G H X Y Z) by (apply (suma_assoc B C G C G B _ _ _ _ _ _ _ _ _ H G B); 和角).
    assert(角度之和小于平角 B C G H C G) by (apply sams_right_comm, os_ts__sams; Side).
    assert(和角 B C G H C G H C B) by 和角.
    split.
    - assert(角度之和小于平角 X Y Z H C G) by (apply (sams_assoc H G B B C G _ _ _ _ _ _ H C B); 和角).
      apply (sams_assoc _ _ _ C G H H C G X Y Z); 和角.
    - assert(和角 X Y Z H C G U V W) by (apply (suma_assoc I J K C G H _ _ _ _ _ _ _ _ _ L M N); 和角).
      apply (suma_assoc _ _ _ B C G H C G _ _ _ X Y Z); 和角.
  }
  destruct HInter.

  elim(saccheri_s_three_hypotheses).
  - intro aah.
    exfalso.
    apply(nlta U V W).
    apply (sams_lta2_suma2__lta I J K L M N _ _ _ H G B B C H); 和角.
    { destruct (t22_14__sams_nbet aah C G B I J K O P Q) as [HIsi HNBet]; Col.
      apply (sams_lea_lta789_suma2__lta123 _ _ _ G B C O P Q _ _ _ G B C A G B); Lea.
        split; Lea; intro; apply HNBet; apply (bet_conga__bet A G B); 等角.
        apply (等角保持和角 B G H H G A A G B); 等角; 和角.
    }
    destruct (t22_14__sams_nbet aah C G H L M N R S T) as [HIsi HNBet]; Col.
    apply (sams_lea_lta789_suma2__lta123 _ _ _ G H C R S T _ _ _ G H C A H C); Lea.
      split; Lea; intro; apply HNBet; apply (bet_conga__bet A H C); 等角.
      apply (等角保持和角 A H G G H C A H C); 等角; 和角.

  - intro HUn.
    destruct HUn as [|oah]; auto.
    exfalso.
    apply(nlta U V W).
    apply (sams_lta2_suma2__lta H G B B C H _ _ _ I J K L M N); 和角; apply nlea__lta; auto; intro.
    { apply (t22_14__nsams oah C G B I J K); Col.
      apply (sams_lea2__sams _ _ _ _ _ _ H G B G B C); Lea; 和角.
    }
    apply (t22_14__nsams oah C G H L M N); Col.
    apply (sams_lea2__sams _ _ _ _ _ _ B C H G H C); Lea; 和角.
Qed.

Lemma similar__rah : postulate_of_existence_of_similar_triangles -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro similar.
  destruct similar as [A [B [C [D [E [F]]]]]].
  spliter.
  assert_diffs.
  elim (lea_total B C A A B C); auto; intro; [elim (长度小于等于的决定性 D E A B)|elim (长度小于等于的决定性 D F A C)].
  - intro.
    apply (similar__rah_aux A B C D E F); auto.
    split; Cong.

  - intro.
    apply (similar__rah_aux D E F A B C); 等角.
      apply (不共线三点构成的角的等角三点也不共线 A B C); auto.
      apply (l11_30_等角保持小于等于 B C A A B C); auto.
      split; auto.

  - intro.
    apply (similar__rah_aux A C B D F E); Col; 等角.
      apply 角度小于等于的交换性; trivial.
    split; auto; intro; destruct(l11_50_1 A C B D F E); Col; 等角; Cong.

  - intro.
    apply (similar__rah_aux D F E A C B); 等角.
      apply (不共线三点构成的角的等角三点也不共线 A C B); Col; 等角.
      apply (l11_30_等角保持小于等于 A B C B C A); 等角.
      split; auto; intro; destruct(l11_50_1 A C B D F E); Col; 等角; Cong.
Qed.

End similar_rah.