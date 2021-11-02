Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_rectangle_principle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__rectangle_principle : postulate_of_right_saccheri_quadrilaterals -> postulate_of_right_lambert_quadrilaterals.
Proof.
  intros rah A B C D HLam.
  apply (lam_per__rah A); assumption.
Qed.

End rah_rectangle_principle.