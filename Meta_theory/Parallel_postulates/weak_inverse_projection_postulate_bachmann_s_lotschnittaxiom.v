Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux :
  weak_inverse_projection_postulate -> forall A1 A2 B1 B2 C1 C2 Q P R M,
  Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Col A1 A2 Q -> Col B1 B2 Q ->
  Col A1 A2 P -> Col C1 C2 P -> Col B1 B2 R ->
  共面 Q P R C1 -> 共面 Q P R C2 -> ~ Col Q P R ->
  在角内 M P Q R -> 等角 M Q P M Q R ->
  严格平行 B1 B2 C1 C2 /\ exists S, Out Q M S /\ Col C1 C2 S.
Proof.
intro hrap.
intros A1 A2 B1 B2 C1 C2 Q P R M HPerpAB HPerpAC.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCop1 HCop2 HNC HM1 HM2.
统计不重合点.
assert (HNCol1 : ~ Col A1 A2 R) by (intro; apply HNC, (共线的传递性4 A1 A2); auto).
assert (HNCol2 : ~ Col B1 B2 P) by (intro; apply HNC, (共线的传递性4 B1 B2); auto).
assert (HPar : 严格平行 B1 B2 C1 C2).
  {
  apply par_not_col_strict with P; Col.
  assert (Col A1 P Q /\ Col A2 P Q /\ Col B1 R Q /\ Col B2 R Q)
    by (repeat split; [apply 共线的传递性2 with A2|apply (共线的传递性3 A1)
                      |apply 共线的传递性2 with B2|apply (共线的传递性3 B1)]; auto).
  spliter.
  assert (共面 Q P R A1) by Cop.
  assert (共面 Q P R A2) by Cop.
  assert (共面 Q P R B1) by Cop.
  assert (共面 Q P R B2) by Cop.
  apply l12_9 with A1 A2; Perp; apply coplanar_pseudo_trans with Q P R; assumption.
  }
split; [assumption|].
assert (HNCol3 : ~ Col Q C1 C2) by (apply par_not_col with B1 B2; Par; Col).
assert (Per P Q R).
  {
  apply L形垂直转直角2, 与垂线共线之线也为垂线2 with A1 A2; Col;
  apply 垂直的对称性, 与垂线共线之线也为垂线2 with B1 B2; Col; Perp.
  }
assert (HSuma : 和角 P Q M P Q M P Q R).
  统计不重合点; apply 等角保持和角性质 with P Q M M Q R P Q R; 等角; 和角.
assert (H为锐角 : 为锐角 P Q M).
{ apply 一角的倍角不大于平角则该角为锐角 with P Q R; auto.
    intro; apply HNC; Col.
  assert (角度小于等于 P Q M P Q R) by Lea.
  apply 角度小于等于保持和角不大于平角性质 with P Q R P Q R; 和角.
}
assert (HC3 : exists C3, Col C1 C2 C3 /\ OS P Q R C3).
{ destruct (每组共线三点都有另一共线点 C1 C2 P) as [C0]; Col; spliter.
  destruct (cop_not_par_same_side P Q C0 P P R) as [C3 []]; Col.
    intro; apply HNCol3; ColR.
    apply coplanar_perm_1, col_cop2__cop with C1 C2; Col; Cop.
  exists C3; split; [ColR|assumption].
}
destruct HC3 as [C3 [HCol6 HOS]].
destruct (hrap P Q M P Q R P C3) as [S [HS1 HS2]]; trivial;
  [apply out_trivial; auto|apply os_distincts in HOS; spliter; auto|
  |apply coplanar_trans_1 with R; Col; Cop|].
{ assert (HP := HPerpAC); destruct HP as [P' [_ [_ [HP1 [HP2 HP3]]]]].
  assert (P = P'); [|treat_equalities; apply HP3; Col].
  elim (垂直推出不共线 _ _ _ _ HPerpAC); intro;
  [apply l6_21_两线交点的唯一性 with A1 A2 C1 C2|apply l6_21_两线交点的唯一性 with A1 A2 C2 C1]; Col.
}
exists S; split; [assumption|ColR].
Qed.

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom :
  weak_inverse_projection_postulate -> bachmann_s_lotschnittaxiom.
Proof.
intro hrap.
apply bachmann_s_lotschnittaxiom_aux.
intros A1 A2 B1 B2 C1 C2 D1 D2 Q P R HQP HQR HPerpAB HPerpAC HPerpBD.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
assert (HNC : ~ Col P Q R).
  apply 成直角三点不共线; auto; apply L形垂直转直角1, (与垂直两线分别共线的两线垂直 A1 A2 B1 B2); auto.
destruct (angle_bisector P Q R) as [M [HM1 HM2]]; auto.
assert (HSuma : 和角 P Q M P Q M P Q R).
  统计不重合点; apply 等角保持和角性质 with P Q M M Q R P Q R; 等角; 和角.
assert (H为锐角 : 为锐角 P Q M).
  {
  apply 一角的倍角不大于平角则该角为锐角 with P Q R; auto.
    intro; apply HNC; Col.
  assert (角度小于等于 P Q M P Q R) by Lea.
  assert (Per P Q R)
    by (apply L形垂直转直角2, 与垂线共线之线也为垂线2 with A1 A2; Col; apply 垂直的对称性, 与垂线共线之线也为垂线2 with B1 B2; Col; Perp).
  apply 角度小于等于保持和角不大于平角性质 with P Q R P Q R; 和角.
  }
destruct (weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux
    hrap A1 A2 B1 B2 C1 C2 Q P R M) as [HParB [S [HS1 HS2]]]; Col.
destruct (weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom_aux
    hrap B1 B2 A1 A2 D1 D2 Q R P M) as [HParA [T [HT1 HT2]]]; [trivial..|]; [Perp|Cop..|Col| |等角|].
  apply l11_24_在角内的对称性, HM1.
destruct (共线的决定性 C1 C2 T).
  exists T; split; Col.
destruct (共线的决定性 D1 D2 S).
  exists S; split; Col.
assert (HOut : Out Q S T) by (apply l6_7 with M; Out).
clear dependent M.
destruct HOut as [HSQ [HTQ [HBet|HBet]]].
- assert (HTS : TS C1 C2 R T).
  { apply l9_8_2 with Q.
      repeat split; [apply par_not_col with B1 B2; Par| |exists S; split]; Col.
    apply l12_6, par_strict_col2_par_strict with B1 B2; Par; Col.
  }
  destruct HTS as [_ [_ [I [HI1 HI2]]]].
  assert (T <> R).
    intro; treat_equalities; Col.
  exists I; split; ColR.
- assert (HTS : TS D1 D2 P S).
  { apply l9_8_2 with Q.
      repeat split; [apply par_not_col with A1 A2; Par| |exists T; split]; Col.
    apply l12_6, par_strict_col2_par_strict with A1 A2; Par; Col.
  }
  destruct HTS as [_ [_ [I [HI1 HI2]]]].
  assert (P <> S).
    intro; treat_equalities; Col.
  exists I; split; ColR.
Qed.

End weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.