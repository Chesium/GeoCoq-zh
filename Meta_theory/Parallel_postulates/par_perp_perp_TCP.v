Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_perp_perp_TCP.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma inter_dec_plus_par_perp_perp_imply_triangle_circumscription :
  decidability_of_intersection ->
  perpendicular_transversal_postulate ->
  triangle_circumscription_principle.
Proof.
intros HID HPTP A B C HNC.
assert (HAB := perp_bisect_existence_cop A B C);
destruct HAB as [C1 [C2 [HAB HCop1]]]; try (assert_diffs; assumption).
assert (HAC := perp_bisect_existence_cop A C B);
destruct HAC as [B1 [B2 [HAC HCop2]]]; try (assert_diffs; assumption).
assert (HInter := HID B1 B2 C1 C2).
elim HInter; clear HInter; intro HInter.

  destruct HInter as [CC [HCol1 HCol2]].

    exists CC; split.

      elim (两点重合的决定性 CC C1); intro HEq; try subst.

        apply perp_bisect_cong_1 with C2; assumption.

        apply perp_bisect_cong_1 with C1.
        apply perp_bisect_sym_1.
        apply perp_bisect_equiv_def in HAB.
        destruct HAB as [I [HPerp HMid]].
        apply perp_bisect_equiv_def.
        exists I; split; try assumption.
        apply 垂直于的对称性.
        apply 垂线共线点也构成垂直_垂直于 with C2; Col.
        apply 垂直于的对称性.
        assumption.

      split.

        elim (两点重合的决定性 CC B1); intro HEq; try subst.

          apply perp_bisect_cong_1 with B2; assumption.

          apply perp_bisect_cong_1 with B1.
          apply perp_bisect_sym_1.
          apply perp_bisect_equiv_def in HAC.
          destruct HAC as [I [HPerp HMid]].
          apply perp_bisect_equiv_def.
          exists I; split; try assumption.
          apply 垂直于的对称性.
          apply 垂线共线点也构成垂直_垂直于 with B2; Col.
          apply 垂直于的对称性.
          assumption.

        destruct HCop1 as [HCop1 HCop3].
        destruct HAB as [[_ HE] HAB].
        elim HE; clear HE; intro; [assert_diffs|exfalso; auto].
        apply col_cop2__cop with C1 C2; Col; Cop.

  exfalso; apply HNC.
  assert (HPar : Par B1 B2 C1 C2).

    unfold Par; left.
    split.

      spliter; CopR.

      intro HInter'; apply HInter.
      destruct HInter' as [I HInter'].
      exists I; assumption.

  clear HInter.
  apply perp_bisect_perp in HAB; apply perp_bisect_perp in HAC.
  assert (HPerp := HPTP B1 B2 C1 C2 A C HPar HAC).
  apply par_id.
  spliter.
  apply l12_9 with C1 C2; Perp; Cop; try CopR.
  apply 垂直的对称性, HPerp; CopR.
Qed.

End par_perp_perp_TCP.