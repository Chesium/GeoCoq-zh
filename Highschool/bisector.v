Require Export GeoCoq.Tarski_dev.Ch13_1.
Require Export GeoCoq.Highschool.triangles.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section Bisector.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Existence of the interior bisector of an angle. *)

Lemma 角平分线的存在性 : forall A B C,  A <> B -> B <> C ->
exists E,  在角内 E A B C /\ 等角 A B E E B C.
Proof.
intros A B C HAB HBC.
destruct (共线的决定性 A B C) as [HCOL | HNCOL].
(*case 1: Out B A C*)
destruct (out_dec B A C) as [HOUT | HNOUT].
exists C.
split.
Side.
apply (l11_21_b A B C C B C);auto.
apply (out_trivial B C);auto.
(*Case 2 Bet A B C*)
assert (Bet A B C) by(apply (not_out_bet A B C);auto).
destruct (垂点的存在性 B A C) as [E HPerp].
intro HEQAC.
subst.
elim HAB.
apply (中间性的同一律 C B); auto.
exists E.
split.
assert_diffs.
repeat split; auto.
exists B.
split;auto.
assert (Perp B E A B) by (apply (垂线共线点也构成垂直2 B E A C B);Col).
assert (Perp B E C B) by (assert_diffs;apply (垂线共线点也构成垂直2 B E C A B);Perp;Col).
assert (Per E B A) by (apply (L形垂直转直角1 B E A);assumption).
assert (Per E B C) by (apply (L形垂直转直角2 B E C);Perp).
assert (等角 E B A E B C) by (assert_diffs;apply (l11_16_直角相等 E B A E B C);auto).
等角.
(*case 3: ~ Col A B C. *)
destruct (由一点往一方向构造等长线段 B A B C ) as [C'[ HC'1 HC'2]].
destruct (由一点往一方向构造等长线段 B C B A ) as [A' [HA'1 HA'2]].
destruct (中点的存在性 A' C') as [I HI].
assert (Cong B C' A' B) by (apply 两组连续三点分段等则全体等 with A C;Cong;Between).
assert_diffs.
assert (等角 A' C' B C' A' B).
 {
 apply  (等腰三角形底角相等 C' B A');auto.
 {
 intro.
 subst.
 treat_equalities.
 assert_cols.
 apply HNCOL.
  ColR. }
  unfold 等腰三角形. Cong.
 }
assert (HTRI : Cong I B I B /\ (I <> B -> 等角 C' I B A' I B /\ 等角 C' B I A' B I)).
{ apply (l11_49 I C' B I A' B); Cong.
 assert_diffs.
 apply (l11_10 A' C' B C' A' B I B I B);Out.
}
exists I.
destruct HTRI as [HCONGIB HIBO].
assert (I <> B) by (intro;elim HNCOL;ColR).
assert (等角 A B I I B C).
{ apply (l11_10 C' B I I B A' A I I C);Out.
  apply 等角的右交换性.
  apply HIBO;auto.
}
split.
unfold 在角内.
repeat split; auto.
destruct (帕施公理 A' B C' I A) as [x1 HIN1].
apply (midpoint_bet A' I C');auto.
Between.
destruct HIN1 as [HIN11 HIN12].
destruct (帕施公理 A B A' x1 C) as [x2 HIN2];auto.
exists x2.
destruct HIN2 as [HIN21 HIN22].
split.
apply (中间性的各排列情况 A x2 C).
right;auto.
right.
apply (bet_out B x2 I).
intro.
elim HNCOL;ColR.
apply 中间性的交换传递性2 with x1; Between.
assumption.
Qed.

Lemma not_col_bfoot_not_equality : forall A B C I H1 H2, ~ Col A B C -> 共面 A B C I ->
Col A B H1 -> Col B C H2 -> 等角 A B I I B C->
Perp A B I H1 -> Perp B C I H2 -> H1 <> B /\ H2 <> B.
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOL1 HCOL2 HCONGA HORTHA HORTHC.
split.
intro.
subst.
assert (Per A B I) by (apply (L形垂直转直角1 B A I);Perp).
assert (Col A C B).
{  apply cop_per2__col with I;Cop.
  assert_diffs;auto.
  apply (直角的对称性 I B C);auto.
  apply (l11_17_等于直角的角是直角 A B I I B C);auto. }
elim HNCOL;Col.
intro;subst.
assert (Per C B I) by (apply (L形垂直转直角1 B C I);auto).
assert (Per I B C) by (apply (直角的对称性 C B I);auto).
assert (Col A C B).
{ apply cop_per2__col with I;Cop.
  assert_diffs; auto.
 apply (l11_17_等于直角的角是直角 I B C A B I);等角. }
elim HNCOL; Col.
Qed.

Lemma bisector_foot_out_out : forall A B C I H1 H2, ~ Col A B C ->
共面 A B C I -> Col B C H2-> 等角 A B I I B C->
Perp A B I H1 -> Perp B C I H2 -> Out B H1 A -> Out B H2 C.
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOL2 HCONGA HORTHA HORTHC HOUT1.
destruct (not_col_bfoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];Col.
assert (为锐角 H1 B I). 
{ apply (perp_out_acute H1 B I H1);auto. 
  apply (out_trivial B H1);auto.
  apply (与垂线共线之线也为垂线2 A B H1 B I H1);Col. }
assert (等角 H1 B I I B C).
{ assert_diffs;apply (l11_10 A B I I B C H1 I I C);Out. }
assert (为锐角 I B C) by (apply (acute_conga__acute H1 B I I B C);auto).
apply (acute_col_perp__out I B C H2);auto.
Qed.

Lemma not_col_efoot_not_equality : forall A B C I H1 H2, ~ Col A B C -> 共面 A B C I ->
Col A B H1 -> Col B C H2-> Cong I H1 I H2->
Perp A B I H1 -> Perp B C I H2 -> H1 <> B /\ H2 <> B.
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOLH1 HCOLH2 HCONG HPERH1 HPERH2.
assert (H1 <> B).
intro.
subst.
assert (H2 <> B).
{  intro.
  subst.
  assert (Col B A C).
   apply (cop_perp2__col B A C I B);auto.
  Cop.
  Perp.
  elim HNCOL.
  Col.
}
assert (Perp B H2 I H2).
  apply (垂线共线点也构成垂直1 B C I H2 H2);auto.
assert (Per B H2 I).
{  apply (L形垂直转直角1 H2 B I);auto.
   Perp.
}
assert (Per H2 B I).
{
  apply (l11_17_等于直角的角是直角 B H2 I H2 B I);auto.
  apply (等腰三角形底角相等 H2 I B);auto.
  assert_diffs;auto.
  unfold 等腰三角形;Cong.
}
assert (H2 = B).
{
  apply (ABC和ACB均直角则B与C重合 I H2 B);auto.
  apply (直角的对称性 B H2 I);auto.
  apply (直角的对称性 H2 B I);auto.
}
contradiction.
split;auto.
intro.
subst.
assert (Perp B H1 I H1) by (apply (垂线共线点也构成垂直1 B A I H1 H1);auto;Perp;Col).
assert (Per B H1 I) by (apply (L形垂直转直角1 H1 B I);auto;Perp).
assert (Per H1 B I).
{
  apply (l11_17_等于直角的角是直角 B H1 I H1 B I);auto.
  apply (等腰三角形底角相等 H1 I B);auto.
  assert_diffs;auto.
  unfold 等腰三角形;Cong.
}
assert (H1 = B).
{
  apply (ABC和ACB均直角则B与C重合 I H1 B);auto.
  apply (直角的对称性 B H1 I);auto.
  apply (直角的对称性 H1 B I);auto.
}
contradiction.
Qed.

End Bisector.


Ltac col_with_conga := 
match goal with
   | H: (等角 ?A ?B ?I ?I ?B ?C) |- Col ?A ?B ?C => first [
      assert (Col A B I) by ColR; assert (Col I B C) by (apply (共线三点构成的角的等角三点也共线 A B I I B C);assumption)|
      assert (Col I B C) by ColR; assert (等角 I B C A B I) by (apply (等角的对称性 A B I I B C H));
        assert (Col A B I) by (apply (共线三点构成的角的等角三点也共线 I B C A B I);assumption) ];
      ColR
   | H :(等角 ?A ?B ?I ?C ?B ?I) |- Col ?A ?B ?C => 
      assert (等角 A B I I B C) by (apply (等角的右交换性 A B I C B I H)); col_with_conga
   | H :(等角 ?I ?B ?A ?I ?B ?C) |- Col ?A ?B ?C => 
      assert (等角 A B I I B C) by (apply (等角的左交换性 I B A I B C H)); col_with_conga
   | H :(等角 ?I ?B ?A ?C ?B ?I) |- Col ?A ?B ?C => 
      assert (等角 A B I C B I) by (apply (等角的左交换性 I B A C B I H)); col_with_conga
   | H :(等角 ?I ?B ?C ?A ?B ?I) |- Col ?A ?B ?C =>
      assert (等角 A B I I B C) by (apply (等角的对称性 I B C A B I H)); col_with_conga
   | H :(等角 ?C ?B ?I ?A ?B ?I) |- Col ?A ?B ?C =>
      assert (等角 A B I C B I) by (apply (等角的对称性 C B I A B I H)); col_with_conga
   | H :(等角 ?I ?B ?C ?I ?B ?A) |- Col ?A ?B ?C =>
      assert (等角 I B A I B C) by (apply (等角的对称性 I B C I B A H)); col_with_conga
   | H: (等角 ?C ?B ?I ?I ?B ?A) |- Col ?A ?B ?C =>
      assert (等角 I B A C B I) by (apply (等角的对称性 C B I I B A H)); col_with_conga
end.

Section Bisector_2.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Lemma equality_foot_out_out : forall A B C I H1 H2, 
 ~ Col A B C -> 在角内 I A B C ->
 Col B C H2 -> Cong I H1 I H2->
 Perp A B I H1 -> Perp B C I H2 -> 
 Out B H1 A -> Out B H2 C.
Proof.
intros A B C I H1 H2 HNCOL HINANGLE HCOLH2 HCONG HPERH1 HPERH2 HOUTH1.
destruct (not_col_efoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];Col.
 Cop.
assert(HMY : Cong H1 B H2 B /\ 等角 H1 B I H2 B I /\ 等角 H1 I B H2 I B).
{  assert_diffs.
   apply (l11_52 B H1 I B H2 I);Cong.
   apply (l11_16_直角相等 B H1 I B H2 I);auto.
   apply (L形垂直转直角1 H1 B I).
   assert (Perp B H1 I H1) by (apply (垂线共线点也构成垂直1 B A I H1 H1);auto;Perp;Col).
   Perp.
   apply (L形垂直转直角1 H2 B I).
   assert (Perp B H2 I H2) by (apply (垂线共线点也构成垂直1 B C I H2 H2);auto;Perp;Col).
   Perp.
   apply (l11_46 B H1 I); auto.
   left.
   apply (L形垂直转直角1 H1 B I).
   assert (Perp B H1 I H1) by (apply (垂线共线点也构成垂直1 B A I H1 H1);auto;Perp;Col).
   Perp.  }
destruct HMY as [HSH1BH2B [HAH1BI HAH1IB]].
assert (TS I B A C).
{  apply (角端点在角内点与顶点连线两侧 A B C I);auto.
   intro.
   assert (Col H1 B H2) by (col_with_conga).
   elim HNCOL; ColR.
   intro.
   assert (Col H2 B H1) by (col_with_conga).
   elim HNCOL;ColR. }
destruct (conga_cop__or_out_ts I B H1 H2) as [HOUTH1H2 | HTSH1H2].
CopR.
等角.
elim HNCOL;ColR.
assert (TS I B A H2) by (apply (l9_5 I B H1 H2 B A);auto;Col).
assert (OS I B H2 C).
{ apply (l9_8_1 I B H2 C A);auto.
 apply (l9_2 I B A H2);auto.
 apply (l9_2 I B A C);auto. }
apply (col_one_side_out B I H2 C).
Col.
apply (invert_one_side I B H2 C);auto.
Qed.

(** The points on the bisector of an angle are at equal distances of the two sides. *)
(* 角平分线定理：BI平分∠ABC IH₁⊥AB IH₂⊥BC -> IH₁=IH₂*)
Lemma 角平分线定理 : forall A B C I H1 H2, 共面 A B C I ->
 Col B H1 A -> Col B H2 C ->
 Perp A B I H1 -> Perp B C I H2 ->
 等角 A B I I B C ->  Cong I H1 I H2.
Proof.
intros A B C I H1 H2 HCOP HCABH HCCBH HPH1 HPH2 HCONGA.
destruct (共线的决定性 A B C) as [HCOL | HNCOL].
assert (Perp A B I H2) by (assert_diffs;apply (与垂线共线之线也为垂线2 B C A B I H2);Col).
assert (H1 = H2).
{ apply (l8_14_2_1b_垂点是交点 H1 A B I H1 H2);auto.
 apply (l8_14_2_1b_bis_交点是垂点 A B I H1 H1);Col.
 ColR.
 assert (Perp I H1 A B) by Perp.
 assert (Perp I H2 A B) by Perp.
 assert (Col I H1 H2) by (apply (cop_perp2__col I H1 H2 A B); Cop).
 Col. }
subst;Cong.
(*for Col A B C End*)
destruct (not_col_bfoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
 Col.
 Col.
destruct (out_dec B H1 A) as [HOUT | HNOUT].
assert (Out B H2 C) by (apply (bisector_foot_out_out A B C I H1 H2);Col).
apply (l11_50_2 I B H1 I B H2).
{ intro.
  elim HNCOL.
  col_with_conga. }
{ assert_diffs.
  apply (l11_16_直角相等 B H1 I B H2 I);auto.
  apply (L形垂直转直角1 H1 B I).
  apply (与垂线共线之线也为垂线2 A B H1 B I H1);Col.
  assert (Perp B H2 I H2) by (apply (垂线共线点也构成垂直1 B C I H2 H2);Col).
  apply (L形垂直转直角1 H2 B I);Perp. }
assert (等角 H1 B I I B H2).
{ assert_diffs.
  apply (l11_10 A B I I B C H1 I I H2);Out. }
等角.
Cong.

destruct (构造对称点 A B) as [A' HCONHA'].
destruct (构造对称点 C B) as [C' HCONHC'].
assert (Bet A B A') by (apply (midpoint_bet A B A');auto).
assert (Bet C B C') by (apply (midpoint_bet C B C');auto).
assert (Out B H1 A').
{
  assert (Bet A B H1).
   apply (not_out_bet A B H1);auto.
   Col.
  intro.
  elim HNOUT.
  apply (l6_6 B A H1);auto.
  apply (l6_3_2 H1 A' B);auto.
  assert_diffs.
  repeat split;auto.
  exists A.
  repeat split;Between. }
assert (Out B H2 C').
{ assert_diffs.
  apply (bisector_foot_out_out A' B C' I H1 H2);auto.
  intro.
  elim HNCOL.
  ColR.
  CopR.
  ColR.
  apply (等角的右交换性 A' B I C' B I);auto.
  apply (l11_13 A B I C B I A' C');等角.
  apply (与垂线共线之线也为垂线2 A B A' B I H1);Col.
  apply (与垂线共线之线也为垂线2 B C B C' I H2);Col. }
apply (l11_50_2 I B H1 I B H2).
{ intro;elim HNCOL.
  col_with_conga. }
assert (Per B H1 I).
{  apply (L形垂直转直角1 H1 B I).
   apply (与垂线共线之线也为垂线2 A B H1 B I H1);Col. }
assert (Per B H2 I) by (apply (L形垂直转直角1 H2 B I);
    assert (Perp B H2 I H2) by (apply (垂线共线点也构成垂直1 B C I H2 H2);Col);Perp).
assert_diffs.
apply (l11_16_直角相等 B H1 I B H2 I);auto.
assert (等角 H1 B I I B H2).
{ assert_diffs.
  apply (l11_10 A' B I I B C' H1 I I H2);Out.
  assert (等角 A' B I C' B I) by (apply (l11_13 A B I C B I A' C');等角).
  等角. }
等角.
Cong.
Qed.


(** The points which are at equal distance of the two side of an angle are on the bisector. *)
(* BI平分∠ABC，H₁与H₂为垂足 *)
Lemma 角平分线定理的逆定理 : forall A B C I H1 H2,  ~ Col A B C ->
 在角内 I A B C -> Col B H1 A -> 
 Col B H2 C -> Perp A B I H1 -> Perp B C I H2 -> Cong I H1 I H2 ->
 等角 A B I I B C.
Proof.
intros A B C I H1 H2 HNCOL HINANGLE HCOLH1 HCOLH2 HPERPH1 HPERPH2 HCONG.
destruct (not_col_efoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
 Cop.
 Col.
 Col.
assert(HMY : Cong H1 B H2 B /\ 等角 H1 B I H2 B I /\ 等角 H1 I B H2 I B).
 apply (l11_52 B H1 I B H2 I).
{ assert_diffs.
  apply (l11_16_直角相等 B H1 I B H2 I); auto.
  apply (L形垂直转直角1 H1 B I).
  assert (Perp B H1 I H1) by (apply (垂线共线点也构成垂直1 B A I H1 H1);Perp;Col).
  Perp.
  apply (L形垂直转直角1 H2 B I).
  assert (Perp B H2 I H2) by (apply (垂线共线点也构成垂直1 B C I H2 H2);Perp;Col).
  Perp. }
Cong.
Cong.
{  assert_diffs.
   apply (l11_46 B H1 I); auto.
   left.
   apply (L形垂直转直角1 H1 B I).
   assert (Perp B H1 I H1) by (apply (垂线共线点也构成垂直1 B A I H1 H1);Perp;Col).
   Perp. }
destruct HMY as [HSH1BH2B [HAH1BI HAH1IB]].
destruct (out_dec B A H1) as [HOUT | HBET].
assert (Out B H2 C) by (apply (equality_foot_out_out A B C I H1 H2);Col;apply (l6_6 B A H1);auto).
assert (等角 A B I C B I).
{ assert_diffs.
 apply (l11_10 H1 B I H2 B I A I C I);Out. }
等角.
assert (~ Out B C H2).
{  intro.
   assert (Out B H1 A).
   { apply (equality_foot_out_out C B A I H2 H1);auto.
     intro.
     elim HNCOL;Col.
     apply (l11_24_在角内的对称性 I A B C);auto.
     Col.
     Col.
     Cong.
     Perp.
     Perp.
     apply (l6_6 B C H2);auto. }
  elim HBET.
  apply (l6_6 B H1 A);auto.  }
assert (Bet A B H1) by (apply (not_out_bet A B H1);auto;Col).
assert (Bet C B H2) by (apply (not_out_bet C B H2);auto;Col).
assert_diffs.
assert (等角 A B I C B I) by (apply (l11_13 H1 B I H2 B I A C);Between).
等角.
Qed.

End Bisector_2.
