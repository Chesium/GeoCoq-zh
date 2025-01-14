Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section existential_triangle_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma existential_triangle__rah : postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro et.
  destruct et as [A [B [C [D [E [F]]]]]].
  分离合取式.
  apply (t22_14__rah A B C D E F); auto.
Qed.

End existential_triangle_rah.