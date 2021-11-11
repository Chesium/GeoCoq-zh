Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section universal_posidonius_postulate_perpendicular_transversal_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma universal_posidonius_postulate__perpendicular_transversal_postulate_aux :
  universal_posidonius_postulate -> forall E F G H R P,
  Perp E G R P -> 共面 F H P R -> Col E G R -> 萨凯里四边形 E F H G ->
  Perp F H P R.
Proof.
intros HP E F G H R P HPerp HCop HCol HSacc.
assert (HPerp1 : Perp E G E F) by (apply 垂直的对称性, sac__perp1214 with H, HSacc).
assert (HPar : 严格平行 E G F H) by (apply sac__pars1423, HSacc).
统计不重合点.
assert (HRAH : postulate_of_right_saccheri_quadrilaterals).
  {
  destruct (中点的存在性 E G) as [M1 HM1].
  destruct (中点的存在性 F H) as [M2 HM2].
  assert (HLamb := mid2_sac__lam6521 _ _ _ _ _ _ HSacc HM2 HM1).
  unfold Lambert四边形 in HLamb; 分离合取式.
  assert (萨凯里四边形 M1 M2 F E).
    {
    repeat split; Perp.
      apply 等长的对称性, 等长的左交换性, HP with E G F H; Col; Par.
      apply 与垂线共线之线也为垂线2 with E M1; Perp; Col.
    apply l12_6, (par_strict_col4__par_strict E G F H); Col.
    }
  apply per_sac__rah with M1 M2 F E; auto.
  }
destruct (两点重合的决定性 E R) as [|HER].
  {
  subst R.
  assert (Col F P E) by (apply (cop_per2__col G); Perp; CopR).
  apply 垂直的对称性, 垂直的左交换性, 垂线共线点也构成垂直1 with F; Col.
  apply 直角转L形垂直; auto; apply HRAH with G, HSacc.
  }
assert (HP' : forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD, IAB <> IAC -> IAB <> IBD ->
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        Col A1 A2 IAB -> Col B1 B2 IAB ->
        Col A1 A2 IAC -> Col C1 C2 IAC ->
        Col B1 B2 IBD -> Col D1 D2 IBD ->
        共面 IAB IAC IBD C1 -> 共面 IAB IAC IBD C2 ->
        共面 IAB IAC IBD D1 -> 共面 IAB IAC IBD D2 ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).
  {
  apply bachmann_s_lotschnittaxiom_aux.
  apply weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom.
  apply thales_converse_postulate__weak_triangle_circumscription_principle.
  apply thales_postulate__thales_converse_postulate.
  apply rah__thales_postulate; assumption.
  }
assert (共面 F H E R) by (apply col_cop__cop with G; Col; Cop).
assert (~ Col F H R) by (intro; apply HPar; exists R; split; Col).
destruct (HP' E G E F P R F H E R F) as [S [HC7 HC8]]; Col; [Perp| |CopR|Cop..|].
  apply HRAH in HSacc; Perp.
assert (S <> R) by (intro; apply HPar; exists R; subst; split; Col).
assert (HSacc2 : 萨凯里四边形 E F S R).
  {
  repeat split.
    apply 直角边共线点也构成直角2 with G; Perp; Col.
    apply L形垂直转直角1; apply (与垂直两线分别共线的两线垂直 E G R P); Col.
    apply 等长的右交换性, HP with E G F H; Col; Par.
    apply 垂直的对称性, 垂线共线点也构成垂直1 with P; Perp; Col.
  apply l12_6, par_strict_col_par_strict with H; Col;
  [|apply par_strict_symmetry, par_strict_col_par_strict with G; Col; Par].
  intro; treat_equalities.
  assert (~ Col G E F) by (apply 成直角三点不共线; Perp).
  assert (Col E P R) by (apply col_cop2_perp2__col with F E G; Perp; Col; Cop).
  apply HER, l6_21_两线交点的唯一性 with E G F E; ColR.
  }
统计不重合点.
apply 垂线共线点也构成垂直1 with S; Col.
assert (Hd := HSacc2).
apply sac_distincts in Hd; 分离合取式.
apply 垂直的对称性, 垂直的交换性, 垂线共线点也构成垂直1 with S; Col.
apply 直角转L形垂直; auto.
apply HRAH with E, sac_perm, HSacc2.
Qed.


Lemma universal_posidonius_postulate__perpendicular_transversal_postulate :
  universal_posidonius_postulate -> perpendicular_transversal_postulate.
Proof.
intros HP A B C D P Q HPar.
revert P Q.
cut (forall P Q, Perp A B P Q -> 共面 C D P Q -> ~ Col A B P -> Perp C D P Q).
  {
  intros Haux P Q HPerp HCop.
  destruct (垂直推出不共线 A B P Q HPerp); [|apply 垂直的右交换性]; apply Haux; Perp; Cop.
  }
intros P Q HPerp HCop HNCol.
assert (HH := HPar).
destruct HH as [HPars|]; [|分离合取式; apply (与垂线共线之线也为垂线2 A B); auto; ColR].
assert (HH := HPerp); destruct HH as [R HR];
apply 垂点是交点 in HR; destruct HR as [HR1 HR2].
destruct (l8_18_过一点垂线之垂点的存在性 A B C) as [E [HE1 HE2]].
  apply par_strict_not_col_1 with D, HPars.
destruct (l8_18_过一点垂线之垂点的存在性 A B D) as [G [HG1 HG2]].
  apply par_strict_not_col_4 with C, HPars.
assert (E <> G).
  {
  intro; subst G.
  assert (Col C D E) by (apply col_cop2_perp2__col with E A B; [Perp..|Col|Cop|Cop]).
  apply HPars; exists E; split; Col.
  }
assert (萨凯里四边形 E C D G).
  {
  repeat split.
    apply L形垂直转直角1, 与垂线共线之线也为垂线1 with A B; Perp.
    apply L形垂直转直角1, 与垂线共线之线也为垂线2 with A B; Perp.
    apply 等长的右交换性, HP with A B C D; Perp; Col.
  apply l12_6, par_strict_symmetry, par_strict_col2_par_strict with A B; Par.
  }
assert (P <> Q) by (apply 垂直推出不重合 in HPerp; apply HPerp).
apply 垂直的对称性, 垂线共线点也构成垂直1 with R; Col.
apply 垂直的对称性.
assert (P <> R) by (intro; subst; apply HNCol, HR1).
apply par_distinct in HPar; 分离合取式.
apply universal_posidonius_postulate__perpendicular_transversal_postulate_aux with E G; trivial.
  apply 与垂线共线之线也为垂线2 with A B; Col; apply 垂直的对称性, 垂直的左交换性, 垂线共线点也构成垂直1 with Q; Perp.
  apply col_cop__cop with Q; trivial.
  apply (共线的传递性4 A B); auto.
Qed.

End universal_posidonius_postulate_perpendicular_transversal_postulate.