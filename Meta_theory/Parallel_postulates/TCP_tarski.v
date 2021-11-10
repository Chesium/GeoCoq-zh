Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.tarski_s_euclid_remove_degenerated_cases.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section TCP_tarski.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma impossible_case_1 :
  forall A B C x y,
  Bet A B x ->
  Bet C y A ->
  严格平行 B C x y ->
  False.
Proof.
intros A B C x y.
intros HABx HACy HPar.
apply 中间性的对称性 in HABx.
assert (HI := 帕施公理 x C A B y HABx HACy); destruct HI as [I [HBCI HIxy]].
apply HPar; exists I; split; Col.
Qed.

Lemma impossible_case_2 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Col A B x ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet y A C ->
  Bet x T y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HABx HADT HBCT HBDC HACy HxTy.
assert (HAy : A <> y) by (intro; apply HBCT; ColR).
revert HABx.
apply one_side_not_col124 with T.
apply bet_ts__os with y; Between.
apply l9_2, l9_8_2 with C.
  apply bet__ts; Between.
assert (HOS : OS A B C D) by (apply invert_one_side, out_one_side; [Col|Out]).
apply one_side_transitivity with D; Side.
apply one_side_not_col124 in HOS.
apply out_one_side; Out.
Qed.

Lemma impossible_case_3 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B x A ->
  Bet x T y ->
  严格平行 B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HADT HBCT HBDC HABx HxTy HPar.
apply l12_6 in HPar.
absurd (TS B C x y); Side.
apply bet_ts__ts with T; trivial.
apply l9_8_2 with A.
  repeat split; Col; exists D; split; Col.
统计不重合点; apply out_one_side; [Col|Out].
Qed.

Lemma impossible_case_4_1 :
  forall A B C D T x y,
  A <> D ->
  C <> D ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Out A B x ->
  Bet T y x ->
  False.
Proof.
intros A B C D T x y.
intros HAD HCD.
intros HABC HACy HADT HBCT HBDC HABx HTyx.
revert HACy.
apply one_side_not_col124 with T.
apply l9_17 with x; trivial.
assert (HOS : OS A C B D) by (apply invert_one_side, out_one_side; [Col|Out]).
apply one_side_transitivity with D.
  apply one_side_not_col124 in HOS; apply out_one_side; Out.
apply one_side_transitivity with B; [Side|].
assert (HACA : Col A C A) by Col.
assert (HABx' : Col B x A) by Col.
assert (H := l9_19 A C B x A HACA HABx'); rewrite H.
split; Col.
Qed.

Lemma impossible_case_4_2 :
  forall A B C D T x y,
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B A x ->
  Bet T y x ->
  严格平行 B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
assert (HTS : TS B C A T) by (repeat split; [..|exists D; split]; Col).
assert (HOS : OS B C A x).
{
  assert (HBCB : Col B C B) by Col.
  assert (HABx' : Col A x B) by Col.
  assert (H := l9_19 B C A x B HBCB HABx'); rewrite H.
  apply 不共线则不重合 in HABC; spliter.
  split; [Out|Col].
}
assert (HTS' : TS B C x T) by (apply l9_8_2 with A; assumption);
clear HTS; clear HOS; destruct HTS' as [_ [_ [I [HBCI HITx]]]].
assert (HTx : T <> x) by (intro; treat_equalities; apply HBCT; Col).
assert (HPar' : 严格平行 B C x T) by (apply par_strict_col_par_strict with y; Col).
apply HPar'; exists I; split; Col.
Qed.

Lemma impossible_case_4 :
  forall A B C D T x y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col A B x ->
  Bet T y x ->
  严格平行 B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAD HBD HCD HDT.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
revert HABx.
destruct (or_bet_out B A x) as [HABx|[HABx|HABx]]; [intro..|Col].

  apply (impossible_case_4_2 A B C D T x y); auto.

  apply (impossible_case_4_1 A B C D T x y); auto.
Qed.

Lemma impossible_two_sides_not_col : forall A B C D T Y,
  A <> D ->
  B <> D ->
  C <> D ->
  D <> T ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B Y T ->
  ~ Col A C Y.
Proof.
intros A B C D T Y HAD HBD HCD HDT.
intros HABC HADT HBCT HBDC HBYT.
apply one_side_not_col124 with B.
apply l9_17 with T; trivial.
assert (HOS : OS A C B D).
  apply invert_one_side, out_one_side; [Col|Out].
apply one_side_transitivity with D; trivial.
apply one_side_not_col124 in HOS.
apply out_one_side; Out.
Qed.

(*
Lemma triangle_circumscription_aux : forall A B C P,
  Cong A P B P -> Cong A P C P -> exists CC, Cong A CC B CC /\ Cong A CC C CC /\ 共面 A B C CC.
Proof.
  intros A B C D HCong1 HCong2.
  destruct (cop_dec A B C D).
    exists D; repeat split; assumption.
  destruct (l11_62_existence A B C D) as [CC [HCop HCC]].
  exists CC.
  assert (CC <> D) by (intro; subst; Cop).
  assert (Per B CC D) by Cop.
  assert (A <> CC).
  { intro; subst CC.
    destruct (l11_46 B A D) as [_ []]; auto.
    统计不重合点; apply 成直角三点不共线; auto.
  }
  assert (Per A CC D) by Cop.
  repeat split; trivial.
  - destruct (cong2_per2__cong_conga2 A CC D B CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A B D) as [_ []]; Cong.
    统计不重合点; apply 成直角三点不共线; auto.
  - assert (Per C CC D) by Cop.
    destruct (cong2_per2__cong_conga2 A CC D C CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A C D) as [_ []]; Cong.
    apply 成直角三点不共线; auto.
Qed.
*)

Lemma triangle_circumscription_implies_tarski_s_euclid_aux1 :
  forall A B C D T X Y Z M1 Z1,
  triangle_circumscription_principle ->
  B <> D ->
  C <> D ->
  D <> T ->
  T <> X ->
  ~ Col A B C ->
  Col A B M1 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  exists x, Col A B x /\ 严格平行 B C x T /\ Cong X x Y x.
Proof.
intros A B C D T X Y Z M1 Z1; intro HTC.
intros HBD HCD HDT HTX.
intros HABC HABM1 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HCong1 HCong2 HPerp1 HPerp2.
assert (A <> D) by (intro; subst; apply HABC; Col).
统计不重合点.
assert (HCopA : 共面 B C T A) by (exists D; left; split; Col).
assert (HCopB : 共面 B C T B) by Cop.
assert (HCopC : 共面 B C T C) by Cop.
assert (HCopT : 共面 B C T T) by Cop.
assert (HCopZ : 共面 B C T Z) by Cop.
assert (HCopY : 共面 B C T Y) by (apply col_cop__cop with Z; Col).
assert (HCopX : 共面 B C T X) by (apply col_cop__cop with Y; Col).
assert (HXYZ1 : ~ Col X Y Z1).
  {
  intro; apply HABC, 等价共线BAC, par_id.
  assert (Col T Z Z1) by ColR.
  assert (共面 B C Y Z1) by (apply col2_cop__cop with T Z; Col).
  apply l12_9 with Y Z1; [Cop..| |Perp|].
    apply coplanar_pseudo_trans with B C T; auto; apply col_cop__cop with Z; auto.
  apply 垂直的对称性, 与垂线共线之线也为垂线2 with T Z; Perp; Col.
  }
destruct (HTC X Y Z1 HXYZ1) as [x [HCong3 [HCong4 HCop1]]]; exists x.
assert (HYM1 : Y <> M1) by (intro; treat_equalities; auto).
assert (HCopZ1 : 共面 B C T Z1).
  {
  assert (~ Col A B Y)
    by (intro; destruct (垂直推出不共线 A B Y Z1) as [|HNCol]; Perp; apply HNCol; ColR).
  apply coplanar_pseudo_trans with A B Y; [| |apply coplanar_pseudo_trans with B C T..|]; Cop.
  }
assert (HCopx : 共面 B C T x).
  apply coplanar_pseudo_trans with X Y Z1; trivial; apply coplanar_pseudo_trans with B C T; assumption.
assert (Col A B x).
  {
  apply cong_cop2_perp_bisect_col with Y Z1; trivial.
    apply coplanar_pseudo_trans with B C T; assumption.
    apply coplanar_pseudo_trans with B C T; assumption.
    apply 等长的传递性 with X x; Cong.
  repeat split; Perp.
  exists M1; repeat split; Between; Cong.
  }
do 2 (split; trivial).
apply par_not_col_strict with T; Col.
apply l12_9 with X Y; [apply coplanar_pseudo_trans with B C T; assumption..| |].
  apply 垂直的对称性, 与垂线共线之线也为垂线2 with T Z; Perp; ColR.
apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong; [|Cop].
intro; subst; apply HABC; ColR.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid_aux :
  forall A B C D T X Y Z M1 Z1 M2 Z2,
  triangle_circumscription_principle ->
  B <> D ->
  C <> D ->
  D <> T ->
  T <> X ->
  ~ Col A B C ->
  Col A B M1 ->
  Col A C M2 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Bet Y M2 Z2 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Cong Y M2 M2 Z2 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  Perp A C Y Z2 ->
  exists x, exists y, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intros A B C D T X Y Z M1 Z1 M2 Z2; intro HTC.
intros HBD HCD HDT HTX.
intros HABC HABM1 HACM2 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HYM2Z2 HCong5 HCong6 HCong7 HPerp1 HPerp2 HPerp3.
assert (Hx := triangle_circumscription_implies_tarski_s_euclid_aux1 A B C D T X Y Z M1 Z1).
destruct Hx as [x [HABx [Hx1 Hx2]]]; [assumption..|]; exists x.
assert (Hy := triangle_circumscription_implies_tarski_s_euclid_aux1 A C B D T X Y Z M2 Z2).
destruct Hy as [y [HACy [Hy1 Hy2]]]; [Between; Col; Perp..|]; exists y.
assert (HxTy : Col x T y).
  {
  elim (两点重合的决定性 T x); intro; [|elim (两点重合的决定性 T y); intro]; [subst; Col..|].
  统计不重合点.
  apply 等价共线BAC, cop_perp2__col with X Y;
    [|apply perp_bisect_perp, cong_cop_perp_bisect; Cong; Cop..].
  assert (共面 B C T Y) by (apply col_cop__cop with Z; Col; Cop).
  assert (共面 B C T X) by (apply col_cop__cop with Y; Col).
  apply coplanar_pseudo_trans with B C T; Cop.
  }
assert (HPar : 严格平行 B C x y).
  {
  apply par_strict_col_par_strict with T; Col.
  intro; subst y.
  destruct HPerp3 as [_ [HAC _]].
  assert (A = x) by (apply (l6_21_两线交点的唯一性 A B C A); Col).
  subst; apply Hx1; exists D; split; Col.
  }
assert (A <> D) by (intro; subst; apply HABC; Col).

elim HxTy; clear HxTy; intro HxTy.

  elim HABx; clear HABx; intro HABx.

    elim HACy; clear HACy; intro HACy; auto.
    exfalso; elim HACy; clear HACy; intro HACy.

      apply (impossible_case_1 A B C x y); assumption.

      apply (impossible_case_2 A B C D T x y); Col.

    exfalso; elim HABx; clear HABx; intro HABx.

      apply (impossible_case_3 A B C D T x y); assumption.

      apply (impossible_case_2 A C B D T y x); Col; Between.

  exfalso; elim HxTy; clear HxTy; intro HxTy.

    apply (impossible_case_4 A B C D T x y); assumption.

    apply (impossible_case_4 A C B D T y x); Between; Col; Par.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid :
  triangle_circumscription_principle ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HTC; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC HBCT.
clear HAT HBT HCT.
assert (HY := l8_18_过一点垂线之垂点的存在性 B C T HBCT); destruct HY as [Y [HBCY HPerp]].
revert B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp.
cut (forall B C, A <> B -> A <> C -> B <> C -> B <> D -> C <> D -> ~ Col A B C ->
                 Bet B D C -> ~ Col B C T -> Col B C Y -> Perp B C T Y -> B <> Y ->
                 exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y).
  {
  intros Haux B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp.
  elim (两点重合的决定性 B Y); auto.
  intro HBY.
  elim (两点重合的决定性 C Y); intro HCY.
    subst; exfalso; apply HBC; reflexivity.
  apply 中间性的对称性 in HBDC.
  apply 垂直的左交换性 in HPerp.
  destruct (Haux C B) as [y [x [HACy [HABx HxTy]]]]; Col.
  exists x, y; repeat split; Between.
  }
intros B C HAB HAC HBC HBD HCD HABC HBDC HBCT HBCY HPerp HBY.
elim (两点重合的决定性 C Y); intro HCY.

  {
  treat_equalities.
  assert (HCT : C <> T) by (apply 不共线则不重合 in HBCT; spliter; auto).
  assert (HY := 中点的存在性 C T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; apply HABC; ColR).
  assert (H := 严格中点组推论1 Y C T HCT HY); destruct H as [HCY HTY];
  apply not_eq_sym in HCY; apply not_eq_sym in HTY.
  assert (HBY : B <> Y) by (intro; subst; apply HBCT; Col).
  destruct HY as [HCTY HCYTY].
  assert (HACY : ~ Col A B Y) by (apply impossible_two_sides_not_col with C D T; Between; Col).
  assert (HX := 构造对称点 Y T); destruct HX as [X HX].
  assert (H := 严格中点组推论2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; [|contradiction]; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; [|contradiction]; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim HZ2; clear HZ2; intro HZ2; [|treat_equalities; exfalso; apply HABC; ColR].
  elim HZ1; clear HZ1; intro HZ1; [|treat_equalities; contradiction].
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y C M1 Z1 M2 Z2; Col.
  }

  {
  assert (HX := 构造对称点 Y T); destruct HX as [X HX].
  assert (H := 垂直推出不重合 B C T Y HPerp); destruct H as [Hclear HTY]; clear Hclear.
  assert (H := 严格中点组推论2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; [|contradiction]; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; [|contradiction]; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  assert (HABY : ~ Col A B Y) . (intro; apply HBY; apply l6_21_两线交点的唯一性 with A B C B; Col).
  assert (HACY : ~ Col A C Y) by (intro; apply HCY; apply l6_21_两线交点的唯一性 with A C B C; Col).
  elim HZ1; clear HZ1; intro HZ1; [|treat_equalities; contradiction].
  elim HZ2; clear HZ2; intro HZ2; [|treat_equalities; contradiction].
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y Y M1 Z1 M2 Z2; Col.
  }
Qed.

End TCP_tarski.