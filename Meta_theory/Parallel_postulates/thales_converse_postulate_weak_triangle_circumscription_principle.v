Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section thales_converse_postulate_weak_triangle_circumscription_principle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma thales_converse_postulate__weak_triangle_circumscription_principle :
  thales_converse_postulate -> weak_triangle_circumscription_principle.
Proof.
intros HP A B C A1 A2 B1 B2 HNC HPer HPerpB1 HPerpB2 HCop1 HCop2 HCop3 HCop4.
destruct (中点的存在性 A B) as [M HM]; exists M.
assert (H := HP A B C M HM HPer).
assert_diffs.
split; [apply cong_cop2_perp_bisect_col with B C|apply cong_cop2_perp_bisect_col with A C]; Cong;
try (apply coplanar_perm_3, col2_cop__cop with A B; Col; Cop).
apply 等长的传递性 with M A; Cong.
Qed.

End thales_converse_postulate_weak_triangle_circumscription_principle.