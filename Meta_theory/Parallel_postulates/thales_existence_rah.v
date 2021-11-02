Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section thales_existence_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.


Lemma thales_existence__rah : existential_thales_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro thales.
  destruct thales as [A [B [C [M]]]].
  spliter.
  apply (t22_17__rah A B C M); assumption.
Qed.

End thales_existence_rah.