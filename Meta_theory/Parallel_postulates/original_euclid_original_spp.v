Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section original_euclid_original_spp.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma original_euclid__original_spp : euclid_s_parallel_postulate -> alternative_strong_parallel_postulate.
Proof.
  intros oe A B C D P Q R Hos HSuma HNBet.
  assert(HA' := 构造对称点 A B).
  destruct HA' as [A'].
  assert(HD' := 构造对称点 D C).
  destruct HD' as [D'].
  assert (Hdiff := HSuma).
  apply 和角推出不重合 in Hdiff.
  spliter.
  统计不重合点.
  elim(lea_total B C D C B A'); auto.
  { intro.
    assert(HY := oe A B C D P Q R).
    destruct HY as [Y []]; auto.
      apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ A'); Between.
    exists Y; split; Col.
  }

  intro.
  assert(和角不大于平角 D' C B C B A') by (apply (用角度小于等于特征化和角不大于平角 _ _ _ _ _ _ D); Between).
  assert(HSuma' := 和角的存在性 A' B C B C D').
  destruct HSuma' as [P' [Q' [R' HSuma']]]; auto.
  assert(Hdiff := HSuma').
  apply 和角推出不重合 in Hdiff.
  spliter.
  assert(HY := oe A' B C D' P' Q' R').
  destruct HY as [Y []]; 和角; [..|exists Y; split; ColR].
  { assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
    assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
    exists D.
    split.
    - apply l9_2; apply (l9_8_2 _ _ A); auto.
      apply bet__ts; Between; Col.
    - apply l9_2, invert_two_sides, bet__ts; Between; Col.
  }
  intro.
  apply HNBet.
  apply (补角和为平角 A B C B C D); trivial.
  assert (互为补角 A' B C B C D') by (apply 和角为平角则为补角 with P' Q' R'; assumption).
  apply (conga2_suppa__suppa B C D' A' B C).
    apply (suppa2__conga456 A' B C); trivial; apply suppa_right_comm, bet__suppa; Between.
    apply suppa2__conga123 with B C D'; trivial; apply suppa_left_comm, bet__suppa; Between.
    apply suppa_sym; assumption.
Qed.

End original_euclid_original_spp.