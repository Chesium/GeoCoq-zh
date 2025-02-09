Require Export GeoCoq.Tarski_dev.Ch09_plane.

Section 防升维公理.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Definition 防升维公理_axiom := forall A B C P Q : Tpoint,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).

Definition all_coplanar_axiom := forall A B C D, 共面 A B C D.

Lemma 防升维公理_implies_per2__col :
  防升维公理_axiom ->
  (forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X).
Proof.
intros HUD A B C X HPer1 HDiff HPer2.
destruct HPer1 as [C' HPer1].
destruct HPer2 as [C'' HPer2].
assert (C' = C'') by (apply 中点组的唯一性1 with C X; 分离合取式; auto); treat_equalities.
unfold 防升维公理_axiom in HUD.
分离合取式; 统计不重合点; unfold 中点 in *; 分离合取式; apply HUD with C C'; Cong.
Qed.

Lemma 防升维公理_implies_col_perp2__col :
  防升维公理_axiom ->
  (forall A B X Y P,
   Col A B P ->
   Perp A B X P ->
   Perp P A Y P ->
   Col Y X P).
Proof.
intro HUP; intros.
assert (P <> A).
eapply 垂直推出不重合1.
apply H1.
eapply 防升维公理_implies_per2__col; auto.
apply L形垂直于转直角.
apply 垂直于的对称性.
apply L形垂直转垂直于.
apply H1.
assumption.
apply L形垂直于转直角.
apply 垂直于的对称性.
apply L形垂直转垂直于.
apply 垂直的左交换性.
eapply 垂线共线点也构成垂直1.
auto.
apply H0.
assumption.
Qed.

Lemma 防升维公理_implies_perp2__col :
  防升维公理_axiom ->
  (forall X Y Z A B,
   Perp X Y A B ->
   Perp X Z A B ->
   Col X Y Z).
Proof.
intro HUP; intros.
induction(共线的决定性 A B X).
  induction(两点重合的决定性 X A).
    subst A.
    assert(X <> B).
      apply 垂直推出不重合 in H.
      分离合取式.
      assumption.
    apply 垂直的右交换性 in H.
    apply L形垂直转垂直于 in H.
    apply 垂直于的交换性 in H.
    apply L形垂直于转直角 in H.
    apply 垂直的右交换性 in H0.
    apply L形垂直转垂直于 in H0.
    apply 垂直于的交换性 in H0.
    apply L形垂直于转直角 in H0.
    apply 等价共线CAB.
    eapply (防升维公理_implies_per2__col).
      assumption.
      apply H.
      assumption.
    assumption.
  assert(Perp A X X Y ).
    eapply 垂线共线点也构成垂直1.
      auto.
      apply 垂直的对称性.
      apply H.
    assumption.
  assert(Perp A X X Z).
    eapply 垂线共线点也构成垂直1.
      auto.
      apply 垂直的对称性.
      apply H0.
    assumption.
  apply 等价共线CAB.
  apply 防升维公理_implies_per2__col with A.
    assumption.
    apply L形垂直于转直角.
    apply 垂直于的交换性.
    apply L形垂直转垂直于.
    apply 垂直的对称性.
    eapply 垂线共线点也构成垂直1.
      auto.
      apply 垂直的对称性.
      apply H.
    assumption.
    assumption.
  apply L形垂直于转直角.
  apply 垂直于的交换性.
  apply L形垂直转垂直于.
  apply 垂直的对称性.
  eapply 垂线共线点也构成垂直1.
    auto.
    apply 垂直的对称性.
    apply H0.
  assumption.
assert(HH0:=H).
assert(HH1:=H0).
unfold Perp in H.
unfold Perp in H0.
ex_and H Y0.
ex_and H0 Z0.
assert(HH2:=H).
assert(HH3:=H2).
apply 垂点是交点 in H.
apply 垂点是交点 in H2.
分离合取式.
assert(Perp X Y0 A B).
  eapply 垂线共线点也构成垂直1.
    intro.
    subst Y0.
    contradiction.
    apply HH0.
  assumption.
assert(Perp X Z0 A B).
  eapply 垂线共线点也构成垂直1.
    intro.
    subst Z0.
    contradiction.
    apply HH1.
  assumption.
assert(Y0 = Z0).
  eapply l8_18_过一点垂线之垂点的唯一性.
    apply H1.
    assumption.
    apply 垂直的对称性.
    assumption.
    assumption.
  apply 垂直的对称性.
  assumption.
subst Z0.
eapply (共线的传递性2 _ Y0).
  intro.
  subst Y0.
  contradiction.
  Col.
Col.
Qed.

Lemma 防升维公理_implies_not_two_sides_one_side_aux :
  防升维公理_axiom ->
  (forall A B X Y PX,
   A <> B -> PX <> A ->
   Perp A B X PX ->
   Col A B PX ->
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
intro HUD; intros.
assert(exists P, exists T, Perp PX A P PX /\ Col PX A T /\ Bet Y T P).
apply 十字上的中间性.
assumption.
ex_elim H6 P.
ex_and H7 T.
assert(HH:= 防升维公理_implies_col_perp2__col HUD A B X P PX H2 H1 H6).
assert(~Col P A B).
apply L形垂直推出不共线 in H6.
intro.
apply H6.
ColR.
assert(TS PX A P Y).
repeat split.
intro.
apply H9.
ColR.
intro.
apply H4.
ColR.
exists T.
split.
apply 等价共线CAB.
assumption.
apply 中间性的对称性.
assumption.
assert(X <> PX).
apply 垂直推出不重合2 in H1.
assumption.
assert(P <> PX).
apply 垂直推出不重合2 in H6.
assumption.
assert(HA:= (or_bet_out X PX P)).
induction HA.
assert(TS PX A P X).
repeat split; try assumption.
intro.
apply H9.
ColR.
intro.
apply H3.
ColR.
exists PX.
split.
apply AAB型共线.
apply 中间性的对称性.
assumption.
eapply l9_8_1.
apply l9_2.
eapply (col_two_sides _ PX).
apply 等价共线ACB.
assumption.
assumption.
apply invert_two_sides.
apply H14.
eapply (col_two_sides _ PX).
apply 等价共线ACB.
assumption.
assumption.
apply invert_two_sides.
apply l9_2.
assumption.
induction H13.
assert(TS A B P Y).
eapply (col_two_sides _ PX).
Col.
assumption.
apply  invert_two_sides.
assumption.
assert(HO:= out_two_sides_two_sides A B X Y P PX (sym_not_eq H0) H2 H13 H14).
contradiction.
apply 等价共线BCA in HH.
contradiction.
Qed.

Lemma 防升维公理_implies_not_two_sides_one_side :
  防升维公理_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
    intro HUD; intros.
    assert (A <> B) by (intro; subst; Col).
    assert(exists PX, Col A B PX /\ Perp A B X PX).
      apply l8_18_过一点垂线之垂点的存在性.
      intro.
      apply H.
      apply 等价共线CAB.
      assumption.
    ex_and H3 PX.
    induction(两点重合的决定性 PX A).
      subst PX.
      apply invert_one_side.
      eapply (防升维公理_implies_not_two_sides_one_side_aux HUD _ _ _ _ A); auto.
        apply 垂直的左交换性.
        assumption.
        Col.
        intro.
        apply H.
        Col.
        intro.
        apply H0.
        Col.
      intro.
      apply H1.
      apply invert_two_sides.
      assumption.
    apply (防升维公理_implies_not_two_sides_one_side_aux HUD _ _ _ _ PX); auto.
Qed.

Lemma 防升维公理_implies_not_one_side_two_sides :
  防升维公理_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ OS A B X Y ->
   TS A B X Y).
Proof.
    intro HUD; intros.
    intros.
    induction(two_sides_dec A B X Y).
      assumption.
    apply 防升维公理_implies_not_two_sides_one_side in H2; try assumption.
    contradiction.
Qed.

Lemma 防升维公理_implies_one_or_two_sides :
  防升维公理_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   TS A B X Y \/ OS A B X Y).
Proof.
intro HUD; intros.
induction(two_sides_dec A B X Y).
left.
assumption.
right.
apply 防升维公理_implies_not_two_sides_one_side in H1; try assumption.
Qed.

Lemma 防升维公理_implies_all_coplanar : 防升维公理_axiom -> all_coplanar_axiom.
Proof.
intro HUD; unfold all_coplanar_axiom; intros.
elim (共线的决定性 A B C); Cop; intro HABC.
elim (共线的决定性 A B D); Cop; intro HABD.
elim (共线的决定性 A C D); Cop; intro HACD.
elim (防升维公理_implies_one_or_two_sides HUD A B C D); Col; [apply 异侧蕴含共面|apply os__coplanar].
Qed.

Lemma all_coplanar_implies_防升维公理 : all_coplanar_axiom -> 防升维公理_axiom.
Proof.
intros HAC A B C P Q.
apply cong3_cop2__col; apply HAC.
Qed.

Lemma all_coplanar_防升维公理 : all_coplanar_axiom <-> 防升维公理_axiom.
Proof.
split; [apply all_coplanar_implies_防升维公理|apply 防升维公理_implies_all_coplanar].
Qed.

Lemma 防升维公理_stab : ~ ~ 防升维公理_axiom -> 防升维公理_axiom.
Proof.
  intros nnupper A B C P Q HPQ H1 H2 H3.
  destruct (共线的决定性 A B C) as [|HNCol]; auto.
  exfalso.
  apply nnupper.
  intro upper.
  apply HNCol.
  apply upper with P Q; auto.
Qed.

End 防升维公理.