Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_perp_perp_par_perp_2_par.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma par_perp_perp_implies_par_perp_2_par :
  perpendicular_transversal_postulate ->
  postulate_of_parallelism_of_perpendicular_transversals.
Proof.
intros HPPP; intros A1 A2 B1 B2 C1 C2 D1 D2 HParAB HPerpAC HPerpBD.
intros HCop1 HCop2 HCop3 HCop4.
apply l12_9 with A1 A2; Perp; try (apply 垂直的对称性, HPPP with B1 B2; Par; Perp).
elim (垂直推出不共线 _ _ _ _ HPerpAC); intro; CopR.
Qed.

End par_perp_perp_par_perp_2_par.