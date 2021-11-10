Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Axioms.continuity_axioms.

Section Tangency.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Euclid Book III, Prop 11 and Prop 12
 We do not need to distinguish between internal or external tangency. *)

(** If two circles are tangent, the common point is on the line joining the centers. *)

Lemma 两圆相切_Col : forall A B C D X,
 两圆相切 A B C D ->
 在圆上 X A B ->
 在圆上 X C D ->
 Col X A C.
Proof.
intros.

unfold 两圆相切 in *.

induction(两点重合的决定性 A C).
subst C.
Col.

assert(HS:=ex_sym1 A C X H2).
ex_and HS Y.
ex_and H4 M.

assert(Cong X A Y A).
apply(is_image_col_cong A C X Y A H2 H6); Col.
assert(Cong X C Y C).
apply(is_image_col_cong A C X Y C H2 H6); Col.

destruct H.
unfold unique in H.

assert(x =X).
apply H.
split; auto.
subst x.
assert(在圆上 Y A B).
unfold 在圆上 in *.
apply 等长的传递性 with A X; Cong.
assert(在圆上 Y C D).
unfold 在圆上 in *.
apply 等长的传递性 with C X; Cong.
assert(X = Y).
apply H.
split; auto.
subst Y.

unfold 对称 in H6.
induction H6.
spliter.
unfold 严格对称 in *.
spliter.
ex_and H11 Z.

assert(Z = X).
apply M是AA中点则M与A重合; auto.
subst Z.
Col.
spliter.
contradiction.
Qed.

Lemma tangent_neq : forall A B O P,
 O<>P -> 圆的切线 A B O P -> A<>B.
Proof.
intros.
intro.
subst B.
unfold 圆的切线 in *.
unfold unique in *.
ex_and H0 T.
assert(HH:=构造对称点 T O).
ex_and HH T'.
assert(在圆上 T' O P).
apply (圆上点关于圆心的对称点也在圆上 T T' O P); auto.
assert(T = T').
apply H1.
split; Col.
subst T'.
apply H.
apply M是AA中点则M与A重合 in H3.
subst T.
unfold 在圆上 in H2.
treat_equalities; tauto.
Qed.

(** A line going through the center is not tangent to the circle. *)

Lemma diam_not_tangent : forall O P A B, 
  P <> O -> Col O A B -> ~ 圆的切线 A B O P.
Proof.
intros O P A B HOP HCol HTan.
destruct HTan as [Q [[HQCol HQOn] HQUnique]].
destruct(两点重合的决定性 A B).
  subst B.
  destruct (由一点往一方向构造等长线段 Q O O P) as [Q' [HQ'1 HQ'2]].
  assert (HQQ' : Q <> Q') by (intro; treat_equalities; auto).
  apply HQQ', HQUnique; split; Col.
destruct (每组共线三点都有另一共线点 A B O) as [C [HOC [HAC [HBC HColC]]]]; Col.
destruct (存在两端点在圆心两侧的直径 O P C) as [Q1 [Q2 [HBet [HQ1Q2C [HQ1On HQ2On]]]]].
assert (HQ1Q2 : Q1 <> Q2).
  intro; treat_equalities; auto.
assert(Q = Q1) by (apply HQUnique; split; ColR).
assert(Q = Q2) by (apply HQUnique; split; ColR).
treat_equalities; auto.
Qed.

(** Every point on the tangent different from the point of tangency is strictly outside the circle. *)

Lemma tangent_out : forall A B O P T X,
  X <> T -> Col A B X -> 圆的切线切于 A B O P T -> 在圆外 X O P.
Proof.
intros.
unfold 圆的切线切于 in *.
spliter.

induction(两点重合的决定性 O P).
subst P.
unfold 在圆外.
unfold Lt.

split.
apply AA小于等于CD.
intro.
unfold 在圆上 in *.
assert(T = O).
apply 等长的同一性 with O; Cong.
assert(X = O).
apply 等长的同一性 with O; Cong.
subst O.
contradiction.

assert(在圆上或圆内 X O P -> X = T).
intro.

assert(HH:= 由圆上圆内两点补全一弦 O P T X H3 H5).
ex_and HH T'.
assert(A <> B).
apply (tangent_neq A B O P); auto.
unfold 圆的切线 in *.
unfold unique in *.
ex_and H1 TT.
assert(TT= T).
apply H9.
split; auto.
subst TT.
assert(T = T').
apply H9.
split; auto.
apply 中间性蕴含共线1 in H7.

assert(Col A X T); ColR.
subst T'.
apply 中间性的同一律 in H7.
subst X.
tauto.

assert(~在圆上或圆内 X O P).
intro.
apply H5 in H6.
contradiction.
apply 不在圆上或圆内就是在圆外.
assumption.
Qed.

(** If line AB is tangent to a circle of center O at a point T, then OT is perpendicular to AB.
This is Euclid Book III, Prop 18 *)

Lemma tangentat_perp : 
forall A B O P T, O <> P -> 圆的切线切于 A B O P T -> Perp A B O T.
Proof.
intros.
assert(TA:=H0).
unfold 圆的切线切于 in H0.
spliter.
assert(A <> B).
apply (tangent_neq A B O P); auto.
assert(~Col A B O).
intro.
assert(~圆的切线 A B O P).
apply(diam_not_tangent); Col.
contradiction.

assert(HH:= l8_18_过一点垂线之垂点的存在性 A B O H4).
ex_and HH R.

induction(两点重合的决定性 T R).
subst R.
auto.

assert(HH:= (构造对称点 T R)).
ex_and HH T'.

induction(两点重合的决定性 A R).
subst A.
assert(Perp T R R O).
apply 垂直的交换性.
apply (垂线共线点也构成垂直1 R B O R T); Col.
assert(垂直于 R T R R O).
apply 垂直于的交换性.
apply L形垂直转垂直于.
Perp.
assert(Per O R T).
apply 直角的对称性.
apply L形垂直于转直角; auto.
unfold Per in *.
ex_and H11 T''.
assert(T' = T'').
apply (中点组的唯一性1 T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply M是AA中点则M与A重合; auto.

assert(在圆上 T' O P).
unfold 在圆上 in *.
apply 等长的传递性 with O T; Cong.

assert(在圆外 T' O P).
apply (tangent_out R B O P T T'); ColR.
unfold 在圆外 in *.
unfold Lt in *.
spliter.
unfold 在圆上 in H14.
apply False_ind.
apply H16.
Cong.


assert(Perp T R R O).
apply 垂直的交换性.
apply (垂线共线点也构成垂直1 R A O R T); Col.
apply 垂直的左交换性.
eapply (垂线共线点也构成垂直1 A B O R R); auto.
unfold 中点 in *.
spliter.
apply 中间性蕴含共线1 in H8.
ColR.
assert(垂直于 R T R R O).
apply 垂直于的交换性.
apply L形垂直转垂直于.
Perp.


assert(Per O R T).
apply 直角的对称性.
apply L形垂直于转直角; auto.
unfold Per in *.
ex_and H12 T''.
assert(T' = T'').
apply (中点组的唯一性1 T R T' T''); auto.
subst T''.

assert(T <> T').
intro.
subst T'.
apply H7.
apply sym_equal.
apply M是AA中点则M与A重合; auto.

assert(在圆上 T' O P).
unfold 在圆上 in *.
apply 等长的传递性 with O T; Cong.

assert(在圆外 T' O P).
unfold 中点 in *.
spliter.
apply 中间性蕴含共线1 in H12.
apply (tangent_out A B O P T T'); auto.
ColR.
unfold 在圆外 in *.
unfold Lt in *.
spliter.
unfold 在圆上 in H14.
apply False_ind.
apply H17.
Cong.
Qed.

(** AB is tangent to the circle (O,P) iff they intersect at a point X
such that AB is perpendicular to OX. *)

Lemma tangency_chara : forall A B O P, P <> O ->
 (exists X, 在圆上 X O P /\ 垂直于 X A B O X) <-> 圆的切线 A B O P.
Proof.
intros.

split.
intro.
ex_and H0 T.
unfold 圆的切线.
unfold unique.
exists T.
split.
split; auto.
apply 垂点是交点 in H1.
tauto.
intros.
spliter.
assert(Col A B T).
apply 垂点是交点 in H1.
tauto.

induction(两点重合的决定性 T x').
auto.
apply False_ind.

assert(Perp T x' O T).
apply (与垂线共线之线也为垂线2 A B); auto.
apply 垂直于转垂直 in H1.
auto.

assert(垂直于 T T x' O T).
apply L形垂直转垂直于; auto.

assert(Per x' T O).
apply 垂直于的交换性 in H7.
apply L形垂直于转直角; auto.

assert(~Col x' T O).
apply L形垂直推出不共线 in H6.
ColR.

assert(Lt T x' x' O /\ Lt T O x' O).
assert_diffs.
apply(l11_46 x' T O); auto.
unfold 在圆上 in *.
unfold Lt in H10.
spliter.
apply H12.
apply 等长的传递性 with O P; Cong.

intros.
assert(HT:=H0).
unfold 圆的切线 in H0.
unfold unique in H0.
ex_and H0 T.

assert(圆的切线切于 A B O P T).
unfold 圆的切线切于.
repeat split; auto.
exists T.
split; auto.
assert(HH:=tangentat_perp A B O P T).
assert(Perp A B O T).
apply HH; auto.

apply(l8_14_2_1b_bis_交点是垂点 A B O T T H4); Col.
Qed.


Lemma tangency_chara2 : forall A B O P Q,
 在圆上 Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> X = Q \/ 在圆外 X O P) <-> 圆的切线 A B O P).
Proof.
intros.
split.
intros.
unfold 圆的切线.
unfold unique.
exists Q.
repeat split; Col.
intros.
spliter.
assert(HH:=(H1 x' H2)).
induction HH.
auto.
unfold 在圆上 in *.
unfold 在圆外 in *.
unfold Lt in *.
spliter.
apply False_ind.
apply H5; Cong.

intros.
assert(圆的切线切于 A B O P Q).
unfold 圆的切线切于.
repeat split; Col.

induction(两点重合的决定性 X Q).
left; auto;

unfold 圆的切线 in H1.
right.

apply(tangent_out A B O P Q X); auto.
Qed.


Lemma tangency_chara3 : forall A B O P Q, A <> B ->
 在圆上 Q O P -> Col Q A B -> 
 ((forall X, Col A B X -> 在圆上或圆外 X O P) <-> 圆的切线 A B O P).
Proof.

intros.
split.
intros.

assert(HT:= (tangency_chara2 A B O P Q H0 H1)); auto.
apply HT.
intros.
induction(两点重合的决定性 X Q).
left; auto.
right.
assert(在圆上或圆外 X O P).
apply H2; Col.

unfold 在圆外.
unfold 在圆上或圆外 in H5.
unfold Lt.
split; auto.
intro.

assert(HH:=中点的存在性 X Q).
ex_and HH M.
assert(在圆内 M O P).
apply(bet_inc2__incs O P Q X M); Circle.
intro.
subst M.

apply M是AB中点则M是BA中点 in H7.
apply A是AB中点则A与B重合 in H7.
subst X; tauto.
intro.
subst M.
apply A是AB中点则A与B重合 in H7.
contradiction.
unfold 中点 in H7.
spliter.
Between.

assert(Col A B M).
unfold 中点 in *.
spliter.
ColR.
assert(HH:=(H2 M H9)).
unfold 在圆内 in *.
unfold 在圆上或圆外 in *.

apply 长度小于等于推出反向不小于 in HH.
contradiction.

intros.
assert(圆的切线切于 A B O P Q).
unfold 圆的切线切于.
repeat split; Col.

induction(两点重合的决定性 X Q).
subst X.
unfold 圆的切线切于 in *.
spliter.
apply 在圆上蕴含在圆上或圆外; auto.

assert(在圆外 X O P).
apply(tangent_out A B O P Q X); auto.
unfold 在圆外 in *.
unfold 在圆上或圆外.
unfold Lt in H6.
tauto.
Qed.

(** Euclid Book III Prop 5 
 If two circles cut one another, then they do not have the same center. *)

Lemma intercc__neq :  forall A B C D,
 两圆相交 A B C D -> A<>C.
Proof.
intros.
unfold 两圆相交 in *.
ex_and H P.
ex_and H0 Q.
unfold 两圆相交于 in *.
spliter.
unfold 在圆上 in *.
intro.
subst C.
apply H.
unfold 同圆.
unfold 在圆上 in *.
assert(Cong A B A D) by (apply 等长的传递性 with A P; Cong).
intro.
split.
intro.
apply 等长的传递性 with A B; Cong.
intro.
apply 等长的传递性 with A D; Cong.
Qed.

(** Euclid Book III Prop 6 
If two circles touch one another, then they do not have the same center.
*)

Lemma tangentcc__neq: forall A B C D,
 A<>B ->
 两圆相切 A B C D ->
 A<>C.
Proof.
intros.
unfold 两圆相切 in *.
unfold unique in *.
ex_and H0 T.
intro.
subst C.
unfold 在圆上 in *.
assert(Cong A B A D) by (apply 等长的传递性 with A T; Cong).
assert(T = B).
apply(H1 B); Cong.
subst T.
assert(HH:=构造对称点 B A).
ex_and HH B'.
unfold 中点 in *.
spliter.
assert(B = B').
  apply(H1 B'); split; Cong.
  apply 等长的传递性 with A B; Cong.
subst B'.
treat_equalities; tauto.
Qed.

Lemma interccat__neq : forall A B C D P Q, 两圆相交于 A B C D P Q -> A <> C.
Proof.
intros.
apply intercc__neq  with B D.
unfold 两圆相交.
exists P; exists Q;auto.
Qed.

(** Prop 17 construction of the tangent to a circle at a given point *)

Lemma tangent_construction : forall O P X, segment_circle -> 在圆上或圆外 X O P 
                                                  -> exists Y, 圆的切线 X Y O P.
Proof.
intros.
induction(两点重合的决定性 O P).
subst P.
exists O.
unfold 圆的切线.
unfold unique.
unfold 在圆上 in *.
exists O.
repeat split; Col; Cong.
intros.
spliter.
treat_equalities; auto.

assert(O <> X).
{
  intro.
  rewrite H2 in *;clear H2.
  treat_equalities.
  intuition.
}

assert(HH:=点与圆的位置关系的决定性 O P X).
induction HH.

assert(HH:= 垂点的存在性 X O X H2).
ex_and HH Y.
unfold 在圆上 in *.
exists Y.
apply tangency_chara; auto.
exists X.
apply L形垂直转垂直于 in H4.
split; Circle.

induction H3.
unfold 在圆上或圆外 in *.
unfold 在圆内 in *.
apply 小于推出反向不小于等于 in H3; contradiction.


assert(exists Q : Tpoint, 在圆上 Q O P /\ Out O X Q).
{
  apply(onc_exists); auto.
}

ex_and H4 U.

assert(Bet O U X).
{
  unfold Out in H5.
  spliter.
  induction H7.
  unfold 在圆外 in *.
  unfold 在圆上 in *.
  assert(Le O X O U).
  {
    unfold Le.
    exists X.
    split; Cong.
  }
  assert(Lt O U O X).
  {
    apply(等长保持小于关系 O P O X); Cong.
  }
  apply 长度小于等于推出反向不小于 in H8.
  contradiction.
  assumption.
}

assert(exists X : Tpoint, Perp U X O U).
{
  apply(垂点的存在性 U O U).
  intro.
  unfold 在圆上 in H4.
  treat_equalities; tauto.
}
ex_and H7 R.
assert(HP:=构造对称点 X O).
ex_and HP W.
unfold 中点 in *.
spliter.
assert(exists X0 : Tpoint, (Bet U R X0 \/ Bet U X0 R) /\ Cong U X0 W X).
{
  apply(由一点往一方向构造等长线段_2 R U W X).
  apply 垂直推出不重合 in H8.
  spliter.
  auto.
}

ex_and H10 T.

assert(在圆内 U O X).
{
  unfold 在圆内.
  unfold 在圆外 in H3.
  unfold 在圆上 in H4.
  apply(等长保持小于关系 O P O X); Cong.
}

assert(在圆外 T O X).
{
  apply(diam_cong_在圆内等价的在圆外 O X X W U T); auto.
  unfold 直径.
  unfold 在圆上.
  repeat split; Cong.
  Cong.
}
unfold segment_circle in H.
assert(exists Z : Tpoint, Bet U Z T /\ 在圆上 Z O X).
{
  apply(H O X U T).
  apply 在圆内蕴含在圆上或圆内; auto.
  apply 在圆外蕴含在圆上或圆外; auto.
}

ex_and H14 Y.
assert(exists Q : Tpoint, 在圆上 Q O P /\ Out O Y Q).
{
  apply(onc_exists O P Y); auto.
  intro.
  unfold 在圆上 in H15.
  treat_equalities; tauto.
}
ex_and H16 V.

exists V.

assert(Bet O V Y).
{
  unfold Out in H17.
  spliter.
  induction H19.
  unfold 在圆外 in H3.
  assert(Lt O V O Y).
  {
    apply (等长保持小于关系 O P O X); Cong.
  }
  unfold 在圆上 in *.
  assert(Le O Y O V).
  {
    unfold Le.
    exists Y.
    split; Cong.
  }
  apply 长度小于等于推出反向不小于 in H21.
  contradiction.
  assumption.
}

assert(Cong O X O Y) by Cong.
assert(Cong O U O V) by (apply 等长的传递性 with O P; Cong).


assert(等角 X O V Y O U).
{
  unfold 在圆上 in *.
  apply(l11_10 U O Y Y O U X V Y U).
  apply 等角的左交换性.
  apply 同角相等; intro;treat_equalities; tauto.
  repeat split; try(intro;treat_equalities; tauto).
  right; auto.
  repeat split; try(intro;treat_equalities; tauto).
  left; auto.
  apply out_trivial; intro;treat_equalities; tauto.
  apply out_trivial; intro;treat_equalities; tauto.
}

assert(Cong V X U Y).
{

  apply(等角两边等长则端点间距相等 V O X U O Y); Cong.
  等角.
}

assert(等角 O U Y O V X).
{
  unfold 在圆上 in *.
  apply(三角形全等推角等2 O U Y O V X).
  intro;treat_equalities; tauto.
  intro;treat_equalities.
  unfold 在圆外 in *.
  unfold Lt in *.
  spliter.
  Cong.
  repeat split; Cong.
}

assert(Per O V X).
{
  apply(l11_17_等于直角的角是直角 O U Y O V X).
  apply(垂线共线点也构成垂直1 _ _ _ _ Y) in H8.

  apply L形垂直转垂直于 in H8.
  apply 垂直于的交换性 in H8.
  apply L形垂直于转直角.
  apply 垂直于的对称性.
  apply 垂直于的交换性.
  assumption.
  intro.
  treat_equalities.
  unfold 等角 in H23.
  tauto.
  induction H10;
  ColR.
  assumption.
}

apply tangency_chara; auto.
exists V.
split; auto.
apply 直角转L形垂直于 in H24; Cong.
apply 垂直于的左交换性.
apply 垂直于的对称性.
assumption.
unfold 在圆上 in *.
intro.
treat_equalities; tauto.
intro.
treat_equalities.
unfold 等角 in H23.
tauto.
Qed.

Lemma interccat__ncol : forall A B C D P Q,
 两圆相交于 A B C D P Q -> ~ Col A C P.
Proof.
intros.
intro.
assert (HH := H).
unfold 两圆相交于 in HH.
spliter.
apply H2.
apply (l4_18 A C).
apply interccat__neq in H.
auto.
assumption.
apply 等长的传递性 with A B; Cong.
apply 等长的传递性 with C D; Cong.
Qed.

(** Euclid Book III Prop 10
 A circle does not cut a circle at more than two points.
 *)
Lemma cop_onc2__oreq : forall A B C D P Q,
 两圆相交于 A B C D P Q -> 共面 A C P Q ->
 forall Z, 在圆上 Z A B -> 在圆上 Z C D -> 共面 A C P Z -> Z=P \/ Z=Q.
Proof.
intros.
assert(HIC := H).
unfold 两圆相交于 in H.
spliter.
induction (两点重合的决定性 Z Q).
  right; auto.
left.
assert(HH:=中点的存在性 Q P).
ex_and HH M.
assert(Per A M Q).
apply(弦中点与圆心连线形成直角 A B Q P M); auto.
assert(Per C M Q).
apply(弦中点与圆心连线形成直角 C D Q P M); auto.

assert(HH:=中点的存在性 Z Q).
ex_and HH N.

assert(Per A N Q).
apply(弦中点与圆心连线形成直角 A Z Q Z).
apply 等长的传递性 with A B; Cong.
Circle.
中点.


assert(Per C N Q).
apply(弦中点与圆心连线形成直角 C Z Q Z).
apply 等长的传递性 with C D; Cong.
Circle.
中点.

assert(Col A C M).
apply cop_per2__col with Q; auto.
induction(共线的决定性 P Q A).
exists M.
left.
split; ColR.
apply coplanar_perm_12, col_cop__cop with P; Col; Cop.
assert_diffs;auto.

assert(A <> C).
apply(interccat__neq A B C D P Q); auto.

assert(Col A C N).
apply cop_per2__col with Q; auto.
apply coplanar_perm_12, col_cop__cop with Z; Col.
apply coplanar_trans_1 with P; Cop.
apply interccat__ncol in HIC.
Col.
assert_diffs;auto.

assert(Perp A C Q P).
induction(两点重合的决定性 A M).
subst M.
apply 直角转L形垂直于 in H12; auto.
apply 垂直于的交换性 in H12.

apply 垂直于转垂直 in H12.
apply 垂直的对称性.
apply (垂线共线点也构成垂直1 Q A A C P); Perp.
ColR.
assert_diffs;auto.

apply 直角转L形垂直于 in H11; auto.
apply 垂直于的交换性 in H11.
apply 垂直于转垂直 in H11.
apply 垂直的交换性 in H11.
apply (垂线共线点也构成垂直1 A M M Q C) in H11; Col.
apply 垂直的对称性 in H11.
apply 垂直的交换性 in H11.
apply (垂线共线点也构成垂直1 Q M C A P) in H11; Col.
Perp.
assert_diffs;auto.

assert(Col Q N Z).
ColR.

assert(Perp A C Q Z).
induction(两点重合的决定性 A N).
subst N.
apply 直角转L形垂直于 in H15; auto.
apply 垂直于的交换性 in H15.
apply 垂直于转垂直 in H15.
apply 垂直的对称性.
apply (垂线共线点也构成垂直1 Q A A C Z); Perp.
assert_diffs;auto.

apply 直角转L形垂直于 in H14; auto.
apply 垂直于的交换性 in H14.
apply 垂直于转垂直 in H14.
apply 垂直的交换性 in H14.
apply (垂线共线点也构成垂直1 A N N Q C) in H14; Col.
apply 垂直的对称性 in H14.
apply 垂直的交换性 in H14.
apply (垂线共线点也构成垂直1 Q N C A Z) in H14; Col.
Perp.
assert_diffs;auto.

apply 垂直的对称性 in H21.
apply 垂直的对称性 in H19.
assert (HH : Par Q P Q Z).
apply (l12_9 _ _ _ _ A C); auto.
Cop.
apply coplanar_trans_1 with P; Cop.
apply interccat__ncol in HIC.
Col.
induction HH.
unfold 严格平行 in H22.
spliter.
apply False_ind.
apply H23.
exists Q.
split; ColR.
spliter.
assert(Z = P \/ Z = Q).
apply(圆交一线于至多两点 A B P Q Z H4); auto.
induction H26; tauto.
Qed.

End Tangency.

Section Tangency_2D.

Context `{T2D:Tarski_2D}.

Lemma onc2__oreq : forall A B C D P Q,
 两圆相交于 A B C D P Q ->
 forall Z, 在圆上 Z A B -> 在圆上 Z C D  -> Z=P \/ Z=Q.
Proof.
intros.
assert(HCop := all_coplanar A C P Q).
assert(HCop1 := all_coplanar A C P Z).
apply(cop_onc2__oreq A B C D); assumption.
Qed.

End Tangency_2D.