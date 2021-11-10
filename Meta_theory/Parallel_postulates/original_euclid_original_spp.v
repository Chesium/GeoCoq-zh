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
  apply suma_distincts in Hdiff.
  spliter.
  assert_diffs.
  elim(lea_total B C D C B A'); auto.
  { intro.
    assert(HY := oe A B C D P Q R).
    destruct HY as [Y []]; auto.
      apply (sams_chara _ _ _ _ _ _ A'); Between.
    exists Y; split; Col.
  }

  intro.
  assert(角度之和小于平角 D' C B C B A') by (apply (sams_chara _ _ _ _ _ _ D); Between).
  assert(HSuma' := 和角的存在性 A' B C B C D').
  destruct HSuma' as [P' [Q' [R' HSuma']]]; auto.
  assert(Hdiff := HSuma').
  apply suma_distincts in Hdiff.
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
  apply (suma_suppa__bet A B C B C D); trivial.
  assert (互为补角 A' B C B C D') by (apply bet_suma__suppa with P' Q' R'; assumption).
  apply (conga2_suppa__suppa B C D' A' B C).
    apply (suppa2__conga456 A' B C); trivial; apply suppa_right_comm, bet__suppa; Between.
    apply suppa2__conga123 with B C D'; trivial; apply suppa_left_comm, bet__suppa; Between.
    apply suppa_sym; assumption.
Qed.

End original_euclid_original_spp.