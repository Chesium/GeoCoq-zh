Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_triangle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__triangle : postulate_of_right_saccheri_quadrilaterals -> triangle_postulate.
Proof.
  intros rah A B C D E F.
  apply (t22_14__bet rah).
Qed.

End rah_triangle.