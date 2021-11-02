Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rectangle_existence_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rectangle_existence__rah : postulate_of_existence_of_a_right_lambert_quadrilateral -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros HABCD.
  destruct HABCD as [A [B [C [D []]]]].
  apply (lam_per__rah A B C D); assumption.
Qed.

End rectangle_existence_rah.