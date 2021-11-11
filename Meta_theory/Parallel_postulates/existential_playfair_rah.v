Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section existential_playfair_rah.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma existential_playfair__rah :
  existential_playfair_s_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
intro HP; destruct HP as [A1 [A2 [P [HNC1 HP]]]].
destruct (l8_18_过一点垂线之垂点的存在性 A1 A2 P) as [Q [HCcol1 HPerp1]]; Col.
assert (HA3 : exists A3, Col A1 A2 A3 /\ A3 <> Q).
{
  destruct (两点重合的决定性 A1 Q).
    subst; exists A2; 统计不重合点; split; Col.
    exists A1; split; Col.
}
destruct HA3 as [A3 []].
destruct (ex_perp_cop P Q P A3) as [R [HPerp2 HCop]].
  统计不重合点; auto.
assert (HPar1 : Par A1 A2 P R).
{
  统计不重合点.
  apply l12_9 with P Q; Perp.
    Cop.
    apply 等价共面ACDB, col_cop__cop with A3; Cop; ColR.
    Cop.
    apply 等价共面ACDB, col_cop__cop with A3; Cop; ColR.
}
assert (HCop1 : 共面 A1 A2 P R) by (apply 平行蕴含共面, HPar1).
assert (HNC2 : 严格平行 A1 A2 P R)
  by (apply par_not_col_strict with P; Col).
apply par_strict_not_col_4 in HNC2.
destruct (l8_18_过一点垂线之垂点的存在性 A1 A2 R) as [S [HCcol2 HPerp3]]; Col.
assert (HPar2 : Par P Q R S) by (apply l12_9 with A1 A2; Perp; Cop).
assert (HNC3 : ~ Col P Q R) by (apply L形垂直推出不共线; Perp).
assert (HNC4 : 严格平行 P Q R S) by (apply par_not_col_strict with R; Col).
apply par_strict_not_col_3 in HNC4.
destruct (l8_18_过一点垂线之垂点的存在性 R S P) as [R' [HC共线的传递性4 HPerp4]]; Col.
assert (HPar3 : Par A1 A2 P R').
{
  统计不重合点.
  apply l12_9 with R S; Perp.
    apply 等价共面ADCB, col_cop__cop with A2; Col; Cop.
    exists R'; left; split; Col.
    apply 等价共面ADCB, col_cop__cop with A1; Col; Cop.
    exists R'; left; split; Col.
}
destruct (HP P R P R') as [_ HCol4]; Col.
assert (R = R') by (统计不重合点; apply l6_21_两线交点的唯一性 with P R S R; Col).
assert (HPs : 严格平行 P Q R S) by (apply par_not_col_strict with R; Col).
treat_equalities; rewrite <- (lam_per__rah P Q S R).

  {
  apply 垂直于转直角1 with S S; apply l8_14_2_1b_bis_交点是垂点; Col.
  统计不重合点; apply 与垂线共线之线也为垂线2 with A1 A2; Col.
  }

  {
  统计不重合点.
  repeat split; auto; [Perp..| |Cop].
  apply L形垂直转直角1, 垂直的左交换性, 与垂线共线之线也为垂线1 with A1 A2; Col.
  }
Qed.

End existential_playfair_rah.