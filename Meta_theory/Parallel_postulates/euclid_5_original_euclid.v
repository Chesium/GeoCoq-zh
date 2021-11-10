Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section euclid_5_original_euclid.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma euclid_5__original_euclid : euclid_5 -> euclid_s_parallel_postulate.
Proof.
  intros eucl A B C D P Q R Hos HIsi HSuma HNBet.
  assert(HM := 中点的存在性 B C).
  destruct HM as [M].
  assert(HD' := 构造对称点 D C).
  destruct HD' as [D'].
  assert(HE := 构造对称点 D' M).
  destruct HE as [E].
  assert(Hdiff := HSuma).
  apply 和角推出不重合 in Hdiff.
  spliter.
  统计不重合点.
  assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
  assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
  assert(HNCol3 : ~ Col M C D) by (intro; apply HNCol2; ColR).
  assert(HNCol4 : ~ Col M C D') by (intro; apply HNCol3; ColR).
  统计不重合点.
  assert(HNCol5 : ~ Col D' C B) by (intro; apply HNCol4; ColR).
  assert(HNCol6 : ~ Col M C E) by (intro; apply HNCol4; ColR).
  assert(HSAS := l11_49 C M D' B M E).
  destruct HSAS as [HCong HSAS]; Cong.
    apply l11_14; Between.
  destruct HSAS as [HConga1 HConga2]; auto.
  统计不重合点.
  assert (Hts : TS C B D D') by (apply bet__ts; Between; Col).
  assert(HA' : 在角内 A C B E).
  { apply lea_in_angle; auto.
    - apply (l11_30_等角保持小于等于 A B C B C D').
        apply (用角度小于等于特征化和角不大于平角 D); Between; 和角.
        apply 角ABC等于角CBA; auto.
      apply (l11_10 M C D' M B E); Out.

    - exists D'.
      split.
      { repeat split; auto.
          intro; apply HNCol4; ColR.
        exists M.
        split; [Col|Between].
      }
      apply (l9_8_2 _ _ D); Side.
  }
  destruct HA' as [_ [_ [_ [A' [HBet [Habs|Hout]]]]]].
  { subst.
    exfalso.
    apply HNCol5; ColR.
  }

  assert(HY := eucl B C E D' M A').
  destruct HY as [Y HY]; Col; Cong; repeat split; Between.
    intro; subst; apply HNCol1; ColR.
  { intro.
    subst.
    apply HNBet.
    apply (bet_conga__bet D' C D); Between.
    apply (和角的唯一性 A B C B C D); auto.
    apply l6_6 in Hout.
    apply (等角保持和角性质 D' C B B C D D' C D); try (apply 同角相等); 和角.
    apply (l11_10 D' C M E B M); Out; 等角.
  }
  unfold BetS in HY.
  spliter.
  exists Y.
  split.
    apply (l6_7 _ _ A'); Out.
  apply (l6_2 _ _ D'); Between.
Qed.

End euclid_5_original_euclid.