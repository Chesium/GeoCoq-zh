Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section playfair_midpoints.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma playfair_s_postulate_implies_midpoint_converse_postulate :
  playfair_s_postulate ->
  midpoint_converse_postulate.
Proof.
intros HP A; intros.
destruct (中点的存在性 A C) as [X HAC].
assert (X = Q).
 assert (严格平行 A B X P).
  apply triangle_mid_par with C; assumption.
 统计不重合点.
 assert_cols.
 apply l6_21_两线交点的唯一性 with A C P Q.
  intro.
  assert (Col A B C) by ColR.
  contradiction.
  auto.
  Col.
  Col.
  destruct (HP A B Q P X P P) as [HCol1 HCol2]; Col; apply par_strict_par; Par.
  Col.
treat_equalities; assumption.
Qed.

End playfair_midpoints.