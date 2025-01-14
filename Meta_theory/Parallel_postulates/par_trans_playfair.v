Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_trans_playfair.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma par_trans_implies_playfair :
  postulate_of_transitivity_of_parallelism -> playfair_s_postulate.
Proof.
intros HPT A1; intros.
assert (Par C1 C2 B1 B2) by (apply HPT with A1 A2; Par).
induction H3.
exfalso; apply H3; exists P; Col.
分离合取式; split; Col.
Qed.

End par_trans_playfair.