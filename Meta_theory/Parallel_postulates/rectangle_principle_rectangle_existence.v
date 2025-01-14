Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rectangle_principle_rectangle_existence.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rectangle_principle__rectangle_existence : postulate_of_right_lambert_quadrilaterals -> postulate_of_existence_of_a_right_lambert_quadrilateral.
Proof.
  intros rectangle.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  destruct (中点的存在性 B C) as [M HM].
  destruct (中点的存在性 A D) as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  exists N; exists M; exists B; exists A.
  split.
    assumption.
    apply (rectangle N); assumption.
Qed.

End rectangle_principle_rectangle_existence.