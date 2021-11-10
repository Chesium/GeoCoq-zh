Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch11_angles.

Section thales_postulate_thales_converse_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** This comes from the proof of Martin's Theorem 23.7 (N -> O) *)

Lemma thales_postulate__thales_converse_postulate : thales_postulate -> thales_converse_postulate.
Proof.
  intros thales A B C M HM HPer.
  destruct (共线的决定性 A B C) as [|HNCol].
    destruct (l8_9_直角三点共线则必有两点重合 A C B); Col; subst; Cong.
  统计不重合点.
  assert(M <> C) by (intro; subst; apply HNCol; Col).
  destruct (由一点往一方向构造等长线段_3 M C M A) as [C' [HC' HCong]]; auto.
  apply 等长的对称性 in HCong.
  elim(两点重合的决定性 C C').
    intro; subst; assumption.
  intro.
  exfalso.
  统计不重合点.
  assert(~ Col A B C') by (intro; apply HNCol; ColR).
  assert(~ Col A C C') by (intro; apply HNCol; ColR).
  assert(~ Col B C C') by (intro; apply HNCol; ColR).
  统计不重合点.
  assert(等角 A C B A C' B).
    apply l11_16_直角相等; auto; apply (thales _ _ _ M); assumption.
  assert(OS A B C C') by (apply (out_one_side_1 _ _ _ _ M); Col).
  destruct HC' as [_ [_ [HMCC'|HMC'C]]].
  - assert(Hlta : 角度小于 A C' B A C B); [|destruct Hlta; 等角].
    apply os3__lta; Side;
    apply (one_side_transitivity _ _ _ M).
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.

  - assert(Hlta : 角度小于 A C B A C' B); [|destruct Hlta; 等角].
    apply os3__lta; Side;
    apply (one_side_transitivity _ _ _ M).
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
Qed.

End thales_postulate_thales_converse_postulate.