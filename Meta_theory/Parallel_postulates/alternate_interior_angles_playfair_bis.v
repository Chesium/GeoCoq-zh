Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section alternate_interior_angles_playfair_bis.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma alternate_interior__playfair_aux : alternate_interior_angles_postulate ->
   forall A1 A2 B1 B2 C1 C2 P,
   Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> 共面 A1 A2 B1 B2 ->
   Par A1 A2 C1 C2 -> Col P C1 C2 ->
   Col C1 B1 B2. (** "half" of playfair_bis *)
Proof.
  intros aip A1 A2 B1 B2 C1 C2 P HPerp2 HNC1 HPB HCop HParAC HPC.
  elim(两点重合的决定性 P C1).
    intro; subst C1; auto.
  intro.
  assert(HParAB : 严格平行 A1 A2 B1 B2)
    by (apply (col_cop_perp2__pars_bis P); Col).
  apply (par_not_col_strict _ _ _ _ P) in HParAC; Col.
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpBP]]]].
  assert(HQ := HPerpAP); auto.
  destruct HQ as [Q [_ [_ [HQP[HQL _]]]]].
  assert(HP' := HPerpBP); auto.
  destruct HP' as [P' HPerpP].
  assert(P'=P) by (apply (l8_14_2_1b_垂点是交点 _ P1 P2 B1 B2); Col).
  subst P'.
  destruct HPerpP as [_ [_ [HPP _]]].
  assert(P<>Q) by (intro; subst Q; Col).
  apply (与垂线共线之线也为垂线1 _ _ _ _ P Q) in HPerpAP; Col.
  apply (与垂线共线之线也为垂线1 _ _ _ _ P Q) in HPerpBP; Col.
  clear dependent P1.
  clear dependent P2.

  assert (HNC2 : ~ Col Q C1 P)
    by (apply (par_not_col A1 A2); auto;
        apply (par_strict_col_par_strict _ _ _ C2); Col).
  统计不重合点.
  assert(HB3 : exists B3, Col B1 B2 B3 /\ B3 <> P).
  { elim(两点重合的决定性 B1 P).
    intro; subst B1; exists B2; Col.
    intro; exists B1; Col.
  }
  destruct HB3 as [B3 []].
  assert(Col P C1 B3); [|ColR].
  统计不重合点.
  apply (cop_perp2__col _ _ _ P Q); [clear HNC2; CopR| |apply (与垂线共线之线也为垂线2 B1 B2); Col].
  apply 垂直的左交换性.
  apply 直角转L形垂直; auto.

  assert(HA3 : exists A3, Col A1 A2 A3 /\ TS P Q C1 A3).
  { elim(共线的决定性 P Q A1);
    [|intro; apply (cop_not_par_other_side _ _ _ _ Q); Col; clear HNC2; CopR].
    intro.
    assert(HA3 := cop_not_par_other_side P Q A2 A1 Q C1).
    destruct HA3 as [A3 []]; Col; [intro; apply HNC1; ColR|clear HNC2; CopR|].
    exists A3; Col.
  }

  destruct HA3 as [A3 [HA3 Hts]].
  assert(~ Col A3 P Q) by (destruct Hts as [_ []]; auto).
  统计不重合点.
  apply (l11_17_等于直角的角是直角 A3 Q P).
    apply L形垂直转直角1, (与垂线共线之线也为垂线2 A1 A2); Col.
  apply 等角的对称性.
  apply aip; auto.
  apply (par_col4__par C1 C2 A1 A2); Col.
  apply par_strict_par; Par.
Qed.

Lemma alternate_interior__playfair_bis : alternate_interior_angles_postulate -> alternative_playfair_s_postulate.
Proof.
intros aia.
intros A1 A2 B1 B2 C1 C2 P HPerp2 HPB HCop HParAC HPC.
split.
apply (alternate_interior__playfair_aux aia A1 A2 _ _ _ C2 P); auto.
apply (alternate_interior__playfair_aux aia A1 A2 _ _ _ C1 P); Col; Par.
Qed.

End alternate_interior_angles_playfair_bis.