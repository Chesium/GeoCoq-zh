Require Export GeoCoq.Tarski_dev.Ch12_parallel.

Section Circle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma A在圆AB上或内 : forall A B,
 在圆上或圆内 A A B.
Proof.
  unfold 在圆上或圆内.
  Le.
Qed.

Lemma B在圆AB上 : forall A B,
 在圆上 B A B.
Proof.
  unfold 在圆上.
  Cong.
Qed.

Lemma 在圆上的对称性 : forall A B P, 在圆上 P A B -> 在圆上 B A P.
Proof.
  unfold 在圆上.
  Cong.
Qed.

Lemma 不在圆上或圆内就是在圆外 : forall X O P, ~ 在圆上或圆内 X O P -> 在圆外 X O P.
Proof.
intros.
unfold 在圆外.
unfold 在圆上或圆内 in *.
apply 不小于等于推出反向小于 in H; auto.
Qed.

Lemma 在圆内或圆上等价的在圆外或圆上 : forall A B P, 在圆上或圆内 P A B <-> 在圆上或圆外 B A P.
Proof.
  split; trivial.
Qed.

Lemma 在圆内等价的在圆外 : forall A B P, 在圆内 P A B <-> 在圆外 B A P.
Proof.
  split; trivial.
Qed.

Lemma 在圆上蕴含在圆上或圆内 : forall A B P, 在圆上 P A B -> 在圆上或圆内 P A B.
Proof.
unfold 在圆上, 在圆上或圆内.
Le.
Qed.

Lemma 在圆上蕴含在圆上或圆外 : forall A B P, 在圆上 P A B -> 在圆上或圆外 P A B.
Proof.
unfold 在圆上, 在圆上或圆外.
Le.
Qed.

Lemma 在圆上或圆内且在圆上或圆外则在圆上 : forall A B P, 在圆上或圆内 P A B -> 在圆上或圆外 P A B -> 在圆上 P A B.
Proof.
  intros A B P HIn HOut.
  apply 长度小于等于的反对称性; trivial.
Qed.

Lemma 在圆内蕴含在圆上或圆内 : forall A B P, 在圆内 P A B -> 在圆上或圆内 P A B.
Proof.
unfold 在圆内, 在圆上或圆内.
Le.
Qed.

Lemma 在圆外蕴含在圆上或圆外 : forall A B P, 在圆外 P A B -> 在圆上或圆外 P A B.
Proof.
unfold 在圆外, 在圆上或圆外.
Le.
Qed.

Lemma 在圆内等价于不在圆上或圆外 : forall A B P, 在圆内 P A B <-> ~ 在圆上或圆外 P A B.
Proof.
intros.
split; intro; [apply 小于推出反向不小于等于|apply 不小于等于推出反向小于]; assumption.
Qed.

Lemma 在圆外等价于不在圆上或圆内 : forall A B P, 在圆外 P A B <-> ~ 在圆上或圆内 P A B.
Proof.
intros.
split; intro; [apply 小于推出反向不小于等于|apply 不小于等于推出反向小于]; assumption.
Qed.

Lemma 在圆上或圆内等价于不在圆外 : forall A B P, 在圆上或圆内 P A B <-> ~ 在圆外 P A B.
Proof.
intros.
split; intro; [apply 长度小于等于推出反向不小于|apply 不小于推出反向小于等于]; assumption.
Qed.

Lemma 在圆上或圆外等价于不在圆内 : forall A B P, 在圆上或圆外 P A B <-> ~ 在圆内 P A B.
Proof.
intros.
split; intro; [apply 长度小于等于推出反向不小于|apply 不小于推出反向小于等于]; assumption.
Qed.

Lemma 在圆AA上或内推出与A重合 : forall A P, 在圆上或圆内 P A A -> A = P.
Proof.
intros A B HIn.
apply AB小于等于CC推出A与B重合 with A; assumption.
Qed.

Lemma 圆心在圆上或圆内则圆缩为一点 : forall A B, 在圆上或圆外 A A B -> A = B.
Proof.
intros A B HOut.
apply AB小于等于CC推出A与B重合 with A; assumption.
Qed.

Lemma 在同圆上的两点与圆心等距 : forall O P A B, 在圆上 A O P -> 在圆上 B O P -> Cong O A O B.
Proof.
unfold 在圆上.
intros O P A B H1 H2.
apply 等长的传递性 with O P; Cong.
Qed.

End Circle.


Hint Resolve A在圆AB上或内 B在圆AB上 在圆上的对称性 在圆内或圆上等价的在圆外或圆上 在圆上蕴含在圆上或圆内 在圆上蕴含在圆上或圆外
             在圆上或圆内且在圆上或圆外则在圆上 在圆内蕴含在圆上或圆内 在圆外蕴含在圆上或圆外 : circle.

Ltac Circle := auto with circle.

Ltac treat_equalities :=
treat_equalities_aux;
repeat
  match goal with
   | H : Cong ?X3 ?X3 ?X1 ?X2 |- _ =>
      apply 等长的对称性 in H; apply 等长的同一性 in H; smart_subst X2
   | H : Cong ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply 等长的同一性 in H;smart_subst X2
   | H : Bet ?X1 ?X2 ?X1 |- _ =>
      apply 中间性的同一律 in H;smart_subst X2
   | H : Le ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply AB小于等于CC推出A与B重合 in H;smart_subst X2
   | H : 中点 ?X ?Y ?Y |- _ => apply M是AA中点则M与A重合 in H; smart_subst Y
   | H : 中点 ?A ?B ?A |- _ => apply A是BA中点则A与B重合 in H; smart_subst A
   | H : 中点 ?A ?A ?B |- _ => apply A是AB中点则A与B重合 in H; smart_subst A
   | H : 在圆上 ?A ?A ?B |- _ =>
      apply 等长的反向同一性 in H;smart_subst B
   | H : 在圆上 ?B ?A ?A |- _ =>
      apply 等长的同一性 in H;smart_subst B
   | H : 在圆上或圆内 ?B ?A ?A |- _ =>
      apply AB小于等于CC推出A与B重合 in H;smart_subst B
   | H : 在圆上或圆外 ?A ?A ?B |- _ =>
      apply AB小于等于CC推出A与B重合 in H;smart_subst B
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in assert (T : A=B) by (apply (双中间性推出点重合 A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in assert (T : B=C) by (apply (双中间性推出点重合2 A B C); Between);
                       smart_subst B
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in assert (T : A=B) by (apply (双中间性推出点重合 A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in assert (T : B=C) by (apply (双中间性推出点重合2 A B C); Between);
                       smart_subst A
   | H : 中点 ?P ?A ?P1, H2 : 中点 ?P ?A ?P2 |- _ =>
     let T := fresh in assert (T := 中点组的唯一性1 A P P1 P2 H H2); smart_subst P1
   | H : 中点 ?A ?P ?X, H2 : 中点 ?A ?Q ?X |- _ =>
     let T := fresh in assert (T := 中点组的唯一性2 P Q A X H H2); smart_subst P
   | H : 中点 ?A ?P ?X, H2 : 中点 ?A ?X ?Q |- _ =>
     let T := fresh in assert (T := 中点组的唯一性3 P Q A X H H2); smart_subst P
   | H : 中点 ?A ?P ?P', H2 : 中点 ?B ?P ?P' |- _ =>
     let T := fresh in assert (T := 中点的唯一性1 P P' A B H H2); smart_subst A
   | H : 中点 ?A ?P ?P', H2 : 中点 ?B ?P' ?P |- _ =>
     let T := fresh in assert (T := 中点的唯一性2 P P' A B H H2); smart_subst A
end.

Ltac CongR :=
 let tpoint := constr:(Tpoint) in
 let cong := constr:(Cong) in
   treat_equalities; unfold 在圆上, 中点 in *; spliter; Cong; Cong_refl tpoint cong.

Section Circle_2.


Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** If a point is strictly inside a segment of a disk, it is strictly inside the circle. *)

Lemma bet_inc2__incs : forall O P U V X,
 X <> U -> X <> V -> Bet U X V ->
 在圆上或圆内 U O P -> 在圆上或圆内 V O P ->
 在圆内 X O P.
Proof.
intros O P U V X HUX HVX HBet HUIn HVIn.
destruct (长度小于等于的决定性 O U O V).
- apply 长度小于_小于等于_传递性 with O V; trivial.
  apply 长度小于的交换性, (bet_le__lt U); Le.
- apply 长度小于_小于等于_传递性 with O U; trivial.
  apply 长度小于的交换性, (bet_le__lt V); Between; Le.
Qed.

Lemma bet_incs2__incs : forall O P U V X,
 Bet U X V -> 在圆内 U O P -> 在圆内 V O P ->
 在圆内 X O P.
Proof.
intros O P U V X HBet HUIn HVIn.
destruct (两点重合的决定性 X U).
  subst; assumption.
destruct (两点重合的决定性 X V).
  subst; assumption.
apply bet_inc2__incs with U V; Circle.
Qed.

(** If A and B are two points inside the circle, then all points on the segment AB are also
    in the circle, i.e. a circle is a convex figure.
*)

Lemma bet_inc2__inc : forall A B U V P, 在圆上或圆内 U A B -> 在圆上或圆内 V A B -> Bet U P V ->
  在圆上或圆内 P A B.
Proof.
  intros A B U V P HU HV HBet.
  destruct (两点重合的决定性 P U).
    subst P; assumption.
  destruct (两点重合的决定性 P V).
    subst P; assumption.
  apply 在圆内蕴含在圆上或圆内, bet_inc2__incs with U V; assumption.
Qed.

(** Given two points U and V on a circle, the points of the line UV which are inside the circle are
    between U and V. *) 

Lemma col_inc_onc2__bet : forall A B U V P, U <> V -> 在圆上 U A B -> 在圆上 V A B ->
  Col U V P -> 在圆上或圆内 P A B -> Bet U P V.
Proof.
  intros A B U V P HUV HU HV HCol HIn.
  destruct (两点重合的决定性 P U); [subst; Between|].
  destruct (两点重合的决定性 P V); [subst; Between|].
  assert (Cong A U A V) by (apply (在同圆上的两点与圆心等距 A B); assumption).
  apply out2__bet; apply not_bet_out; Col; intro.
  - apply (bet_le__lt P V A U); Cong.
    apply (l5_6_等长保持小于等于关系 A P A B); Cong.
  - apply (bet_le__lt P U A V); Between; Cong.
    apply (l5_6_等长保持小于等于关系 A P A B); Cong.
Qed.

(** Given two points U and V on a circle, all points of line UV which are outside the segment UV are
    outside the circle. *)

Lemma onc2_out__outcs : forall A B U V P, U <> V -> 在圆上 U A B -> 在圆上 V A B -> Out P U V ->
  在圆外 P A B.
Proof.
  intros A B U V P HUV HUOn HVOn HOut.
  apply 在圆外等价于不在圆上或圆内.
  intro HIn.
  apply (not_bet_and_out U P V).
  split; trivial.
  apply (col_inc_onc2__bet A B); Col.
Qed.

(** Given two points U and V inside a circle, all points of line UV which are outside the circle are
    outside the segment UV. *)

Lemma col_inc2_outcs__out : forall A B U V P, 在圆上或圆内 U A B -> 在圆上或圆内 V A B ->
  Col U V P -> 在圆外 P A B -> Out P U V.
Proof.
  intros A B U V P HUIn HVIn HCol HOut.
  apply not_bet_out; Col.
  intro HBet.
  apply 在圆外等价于不在圆上或圆内 in HOut.
  apply HOut, bet_inc2__inc with U V; trivial.
Qed.

(** If the center of a circle belongs to a chord, then it is the midpoint of the chord. *)

Lemma 若圆心在一弦上则其平分该弦 : forall A B U V, U <> V -> 在圆上 U A B -> 在圆上 V A B ->
  Col U V A -> 中点 A U V.
Proof.
  intros A B U V HUV HU HV HCol.
  split.
    apply (col_inc_onc2__bet A B); Circle.
    apply 等长的传递性 with A B; Cong.
Qed.

(** Given a point U on a circle and a point P inside the circle, there is a point V such as
    UV is a chord of the circle going through P. *)

Lemma 由圆上圆内两点补全一弦 : forall A B U P, 在圆上 U A B -> 在圆上或圆内 P A B ->
  exists V, 在圆上 V A B /\ Bet U P V.
Proof.
  intros A B U P HOn HIn.
  destruct (两点重合的决定性 U A).
    unfold 在圆上, 在圆上或圆内 in *|-.
    treat_equalities; exists U; split; Circle; Between.
  assert (HA' : exists A', U <> A' /\ Col U P A' /\ Per A A' U).
  { destruct (共线的决定性 U P A) as [HCol|HNCol].
      exists A; split; Col; Perp.
    destruct (l8_18_过一点垂线之垂点的存在性 U P A) as [A' [HCol HPerp]]; trivial.
    assert (U <> A').
    { intro; treat_equalities.
      assert_diffs.
      destruct (l11_46 P U A) as [_ HLt]; auto.
        left; Perp.
      apply 小于推出反向不小于等于 in HLt.
      apply HLt.
      apply (l5_6_等长保持小于等于关系 A P A B); Cong.
    }
    exists A'; repeat split; trivial.
    apply 直角的对称性, L形垂直转直角1.
    apply 垂直的左交换性, 垂线共线点也构成垂直1 with P; trivial.
  }
  destruct HA' as [A' [HUA' [HCol HPer]]].
  destruct (构造对称点 U A') as [V HV].
  assert_diffs.
  assert (HCong := 直角端点和其关于顶点的对称点与另一端点等距 A A' U V HPer HV).
  assert (HVOn : 在圆上 V A B).
    unfold 在圆上 in *.
    apply 等长的传递性 with A U; Cong.
  exists V; split; trivial.
  apply (col_inc_onc2__bet A B); trivial.
  ColR.
Qed.

(** Given a circle, there is a point strictly outside the circle. *)

Lemma 严格在圆外的点的存在性 : forall O P, exists Q, 在圆外 Q O P.
Proof.
intros.
induction(两点重合的决定性 O P).
subst P.
assert(HH:=每个点均有不同点 O).
ex_and HH Q.
exists Q.
unfold 在圆外.
apply BC不重合则AA小于BC;auto.

assert(HH:=由一点往一方向构造等长线段 O P O P).
ex_and HH Q.
exists Q.
split.
exists P.
split; Cong.
intro.
assert (P=Q) by eauto using between_cong.
treat_equalities;intuition.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly outside the circle. *)

Lemma 严格在圆外的点的存在性_另一表述 : forall O P X, X <> O -> exists Q, Out O X Q /\ 在圆外 Q O P.
Proof.
intros O P X HOX.
destruct (由一点往一方向构造等长线段 O X O P) as [Q [HQ1 HQ2]].
exists Q; split.
  apply bet_out; auto.
split.
- apply 长度小于等于的交换性.
  exists X.
  split; Between; Cong.
- intro.
  apply HOX.
  apply between_cong with Q; Between.
  apply 等长的传递性 with O P; Cong.
Qed.

(** Given a circle there is a point which is strictly inside. *)

Lemma 严格在非退化圆内的点的存在性 : forall O P, O <> P -> exists Q, 在圆内 Q O P.
Proof.
intros.
exists O.
apply BC不重合则AA小于BC;auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray
    which is also strictly inside the circle. *)

Lemma 严格在非退化圆内的点的存在性_另一表述 : forall O P X, X <> O -> P <> O -> exists Q, Out O X Q /\ 在圆内 Q O P.
Proof.
intros O P X HOX HOP.
destruct (中点的存在性 O P) as [M HM].
destruct (由一点往一方向构造等长线段_3 O X O M) as [Q [HQ1 HQ2]]; auto.
  intro; treat_equalities; auto.
exists Q; split; auto.
apply (等长保持小于关系 O M O P); Cong.
apply 严格中点组半段小于全段; auto.
Qed.

(** Given a circle of center O and a ray OX, there is a point on the ray which is also on the circle. *)

Lemma onc_exists : forall O P X,  X <> O -> O <> P -> exists Q, 在圆上 Q O P /\ Out O X Q.
Proof.
intros.
assert(HH:=由一点往一方向构造等长线段_2 X O O P H).
ex_and HH Q.
exists Q.
split.
unfold 在圆上.
Cong.
unfold Out.
repeat split; auto.
intro.
subst Q.
treat_equalities; tauto.
Qed.

(** Given a circle of center O and a line OX, O is between two points of the line
    which are also on the circle. *)

Lemma 存在两端点在圆心两侧的直径 : forall O P X, exists Q1 Q2,
  Bet Q1 O Q2 /\ Col Q1 Q2 X /\ 在圆上 Q1 O P /\ 在圆上 Q2 O P.
Proof.
intros O P X.
destruct (两点重合的决定性 X O).
  subst X.
  destruct (由一点往一方向构造等长线段 P O O P) as [P' [HP'1 HP'2]].
  exists P, P'; repeat split; Col; Circle.
destruct (两点重合的决定性 O P).
  subst P.
  exists O, O; repeat split; finish.
assert(HH:= onc_exists O P X H H0).
ex_and HH Q1.
assert(HH:= 由一点往一方向构造等长线段 Q1 O O Q1).
ex_and HH Q2.
exists Q1, Q2.
repeat split; Col.
ColR.
apply 等长的传递性 with O Q1; Cong.
Qed.

(** The symmetric of a point on a circle relative to the center is also on the circle. *)

Lemma 圆上点关于圆心的对称点也在圆上 : forall X Y O P, 
 中点 O X Y -> 在圆上 X O P -> 在圆上 Y O P.
Proof.
intros.
apply 等长的传递性 with O X; Cong.
Qed.


(** The middle of a chord together with the center of the circle and one end of the chord
    form a right angle *)
(* 垂径定理 *)
Lemma 弦中点与圆心连线形成直角 : forall O P U V X,
 在圆上 U O P -> 在圆上 V O P -> 中点 X U V -> Per O X U.
Proof.
intros.
unfold Per.
exists V.
unfold 在圆上 in *.
split; trivial.
apply 等长的传递性 with O P; Cong.
Qed.

(** Euclid Book III Prop 3 (two lemmas).
 If a straight line passing through the center of a circle 
 bisects a straight line not passing through the center,
 then it also cuts it at right angles; and if it cuts it at right angles, then it also bisects it.
*)

(** The line from the center of a circle to the midpoint of a chord is perpendicular to the chord. *)

Lemma 弦中点与圆心连线垂直于弦 : forall O P A B X,
 O <> X -> A <> B -> 在圆上 A O P -> 在圆上 B O P -> 中点 X A B -> Perp O X A B.
Proof.
intros.
assert(Per O X A).
apply (弦中点与圆心连线形成直角 O P A B X); auto.
unfold 中点 in *.
spliter.

apply 直角转L形垂直于 in H4; auto.
apply 垂直于转垂直 in H4.
apply 垂直的对称性.

apply (垂线共线点也构成垂直1 _ X); Perp.
Col.
intro.
subst X.
treat_equalities; tauto.
Qed.

(** If a line passing through the center of a circle is perpendicular to a chord,
    then they intersect at the middle of the chord *)

Lemma 垂直于弦的直径平分弦 : forall O P A B X,
 O<>X -> A<>B -> Col A B X -> 在圆上 A O P -> 在圆上 B O P -> Perp O X A B -> 中点 X A B.
Proof.
  intros O P A B X HOX HAB HCol HAOn HBOn HPerp.
  destruct (中点的存在性 A B) as [M HM].
  cut (X = M).
    intro; subst; trivial.
  assert (HNCol : ~ Col A B O) by (destruct (垂直推出不共线 A B O X); Perp; Col).
  apply (l8_18_过一点垂线之垂点的唯一性 A B O); Col; Perp.
  apply 垂直的对称性, 弦中点与圆心连线垂直于弦 with P; auto.
  intro; subst; apply HNCol; Col.
Qed.

(** If two circles intersect at a point which is not on the line joining the center,
    then they intersect on any half-plane delimited by that line. *)

Lemma circle_circle_os : forall A B C D I P,
  在圆上 I A B -> 在圆上 I C D -> ~ Col A C I -> ~ Col A C P ->
  exists Z, 在圆上 Z A B /\ 在圆上 Z C D /\ OS A C P Z.
Proof.
  intros A B C D I P HI1 HI2 HNCol1 HNCol2.
  destruct (l8_18_过一点垂线之垂点的存在性 A C I) as [X []]; trivial.
  destruct (l10_15 A C X P) as [Z0 []]; trivial.
  assert_diffs.
  destruct (l6_11_existence X X I Z0) as [Z []]; auto.
  exists Z.
  assert (Perp A C X Z).
    assert_diffs; apply 垂直的对称性, 垂线共线点也构成垂直1 with Z0; Perp; Col.
  assert (OS A C P Z).
    apply one_side_transitivity with Z0; trivial.
    apply out_one_side_1 with X; [apply one_side_not_col124 with P| |apply l6_6]; trivial.
  clear dependent Z0.
  repeat split; auto.
  - apply 等长的传递性 with A I; trivial.
    destruct (两点重合的决定性 A X).
      subst; assumption.
    apply l10_12 with X X; Cong; [apply L形垂直转直角2|apply L形垂直转直角1];
      apply 垂直的左交换性, 垂线共线点也构成垂直1 with C; auto.
  - apply 等长的传递性 with C I; trivial.
    destruct (两点重合的决定性 C X).
      subst; assumption.
    apply l10_12 with X X; Cong; [apply L形垂直转直角2|apply L形垂直转直角1];
      apply 垂直的左交换性, 垂线共线点也构成垂直1 with A; Perp; Col.
Qed.

(** If two circles intersect, then they intersect on any plane containing the centers *)

Lemma circle_circle_cop : forall A B C D I P, 在圆上 I A B -> 在圆上 I C D ->
  exists Z, 在圆上 Z A B /\ 在圆上 Z C D /\ 共面 A C P Z.
Proof.
  intros A B C D I P HI1 HI2.
  destruct (共线的决定性 A C P).
    exists I; repeat split; trivial.
    exists P; left; split; Col.
  destruct (共线的决定性 A C I).
    exists I; repeat split; trivial.
    exists I; left; split; Col.
  destruct (circle_circle_os A B C D I P) as [Z [HZ1 [HZ2 HOS]]]; trivial.
  exists Z; repeat split; Cop.
Qed.

(** A circle does not cut a line at more than two points. *)

Lemma 圆交一线于至多两点 : forall O P U V W,
 U <> V -> Col U V W -> 在圆上 U O P -> 在圆上 V O P -> 在圆上 W O P -> 
 W = U \/ W = V.
Proof.
intros O P U V W HUV HCol HUOn HVOn HWOn.
destruct (两点重合的决定性 W U); auto.
right.
apply 双中间性推出点重合 with U; apply col_inc_onc2__bet with O P; Col; Circle.
Qed.

(** The midpoint of a chord is strictly inside the circle. *)

Lemma 弦中点严格在圆内 : forall O P U V M, 
 U <> V -> 在圆上 U O P -> 在圆上 V O P -> 中点 M U V ->
 在圆内 M O P.
Proof.
intros O P U V M HUV HUOn HVOn HM.
assert_diffs.
apply bet_inc2__incs with U V; Between; Circle.
Qed.

(** A point is either strictly inside, on or strictly outside a circle. *)

Lemma 点与圆的位置关系的决定性 : forall O P X,
  在圆上 X O P \/ 在圆内 X O P \/ 在圆外 X O P.
Proof.
intros O P X.
destruct (等长的决定性 O X O P); auto.
right.
destruct (长度小于等于的决定性 O P O X); [right|left]; split; Cong.
Qed.

(** If a point is inside a circle, then it lies on a radius. *)

Lemma 圆上或圆内的点在一条半径上 : forall O P X, 在圆上或圆内 X O P ->
  exists Y, 在圆上 Y O P /\ Bet O X Y.
Proof.
  intros O P X HIn.
  destruct (两点重合的决定性 O P).
    unfold 在圆上或圆内 in HIn; treat_equalities.
    exists O; split; Circle; Between.
  destruct (两点重合的决定性 O X).
    subst; exists P; split; Circle; Between.
  destruct (由一点往一方向构造等长线段_3 O X O P) as [Y [HY1 HY2]]; auto.
  exists Y; split; auto.
  apply l6_13_1; trivial.
  apply (l5_6_等长保持小于等于关系 O X O P); Cong.
Qed.

Lemma inc_onc2_out__eq : forall O P A B C,
  在圆上或圆内 A O P -> 在圆上 B O P -> 在圆上 C O P -> Out A B C -> B = C.
Proof.
  intros O P A B C HA HB HC HOut.
  destruct (由圆上圆内两点补全一弦 O P B A) as [B' [HB' HBet]]; trivial.
  assert_diffs.
  destruct (圆交一线于至多两点 O P B B' C); auto.
    ColR.
  subst C.
  exfalso.
  apply (not_bet_and_out B A B'); split; assumption.
Qed.

Lemma 非退化圆上的点不与圆心重合 : forall O P A, O <> P -> 在圆上 A O P -> A <> O.
Proof.
intros.
intro.
unfold 在圆上 in *.
treat_equalities; tauto.
Qed.

Lemma 与弦成直角的直径平分弦 : forall O P U V M, U <> V -> M <> U ->
 在圆上 U O P -> 在圆上 V O P -> Col M U V -> Per O M U -> 中点 M U V .
Proof.
intros.
assert(HH:=中点的存在性 U V).
ex_and HH M'.
assert(HH:=(弦中点与圆心连线形成直角 O P U V M' H1 H2 H5)).
assert(M = M' \/ ~ Col M' U V).
apply(共线点和两直角的两种情况 O M U V M'); Col.
assert_diffs;auto.
induction H6.
subst M'.
assumption.
apply False_ind.
apply H6.
ColR.
Qed.

(** Euclid Book III Prop 14
Equal straight lines in a circle are equally distant from the center, 
and those which are equally distant from the center equal one another.
*)

Lemma 同圆等长弦与圆心等距 : forall O P A B C D M N,
 在圆上 A O P ->
 在圆上 B O P ->
 在圆上 C O P ->
 在圆上 D O P ->
 中点 M A B ->
 中点 N C D ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(Cong M B N D).
apply 等长的交换性.
eapply (两中点组全段等长则前半段等长 _ _ A _ _ C); 中点.
Cong.
unfold 中点 in *.
unfold 在圆上 in *.
spliter.
apply 等长的交换性.
apply 等长的对称性.
apply(l4_2 A M B O C N D O).
unfold 内五线段形式.
repeat split; Cong.
apply (等长的传递性 _ _ O P); Cong.
apply (等长的传递性 _ _ O P); Cong.
Qed.

(** variant *)
Lemma 同圆等长弦与圆心等距 : forall O P A B C D M N,
 A <> B -> C <> D -> M <> A -> N <> C ->
 在圆上 A O P ->
 在圆上 B O P ->
 在圆上 C O P ->
 在圆上 D O P ->
 Col M A B ->
 Col N C D ->
 Per O M A ->
 Per O N C ->
 Cong A B C D ->
 Cong O N O M.
Proof.
intros.
assert(中点 M A B).
apply(与弦成直角的直径平分弦 O P A B M H H1 H3 H4 H7 H9).
assert(中点 N C D).
apply(与弦成直角的直径平分弦 O P C D N H0 H2 H5 H6 H8 H10).
apply (同圆等长弦与圆心等距 O P A B C D M N); auto.
Qed.

(** Prop 7   **)

Lemma 在圆上的对称性__onc : forall O P A B X Y, 
Bet O A B -> 在圆上 A O P -> 在圆上 B O P -> 在圆上 X O P -> 严格对称 X Y A B -> 在圆上 Y O P.
Proof.
intros.
unfold 在圆上 in *.
assert(Cong X O Y O).
  {
    apply(is_image_spec_col_cong A B X Y O H3);Col.
  }
apply 等长的传递性 with O X; Cong.
Qed.


Lemma 圆上点与其关于圆心的对称点构成直径 : forall O P A B, 在圆上 A O P -> 中点 O A B -> 直径 A B O P.
Proof.
  intros O P A B HA HB.
  repeat split; Between.
  apply (圆上点关于圆心的对称点也在圆上 A); trivial.
Qed.

Lemma 弦长小于等于直径 : forall O P A B U V,
 直径 A B O P -> 在圆上 U O P -> 在圆上 V O P -> Le U V A B.
Proof.
intros.
unfold 在圆上 in *.
unfold 直径 in *.
spliter.
apply(triangle_inequality_2 U O V A O B); trivial;
apply 等长的传递性 with O P; Cong.
Qed.

Lemma 非直径之弦长小于直径 : forall O P A B U V, 
 ~ Col O U V -> 直径 A B O P -> 在圆上 U O P -> 在圆上 V O P ->
 Lt U V A B.
Proof.
intros.
assert(HH:= 弦长小于等于直径 O P A B U V H0 H1 H2).
unfold Lt.
split; auto.
intro.
apply H.
unfold 直径 in *.
assert(HP:=中点的存在性 U V).
ex_and HP O'.
unfold 中点 in *.
spliter.
unfold 在圆上 in *.
assert(Cong O A O B) by (apply 等长的传递性 with O P; Cong).
assert(Cong A O U O').
apply(两中点组全段等长则前半段等长 A O B U O' V); unfold 中点; try split; Cong.
assert(Cong B O V O').
apply(两中点组全段等长则后半段等长 A O B U O' V); unfold 中点; try split; Cong.
apply(全等于退化的三角形 O A B).
Col.
unfold 三角形全等.
repeat split; Cong; apply 等长的传递性 with O P; Cong.
Qed.


Lemma 圆上或圆内两点间距小于等于直径: forall O P A B U V, 直径 A B O P -> 在圆上或圆内 U O P -> 在圆上或圆内 V O P -> Le U V A B.
Proof.
intros.
unfold 在圆上或圆内 in *.
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
assert(HH:= 由一点往一方向构造等长线段 U O O V).
ex_and HH W.
assert(Le U V U W).
{
  apply (triangle_inequality U O); Between; Cong.
}

assert(Le U W A B).
{
  apply(bet2_le2__le O O A B U W); Between.

  apply (l5_6_等长保持小于等于关系 O U O P O U O A);Cong.
  apply (l5_6_等长保持小于等于关系 O V O P O W O B);Cong.
}
apply(长度小于等于的传递性 U V U W A B); auto.
Qed.


Lemma 直径与圆的交点为直径两端点 : forall O P A B X, 直径 A B O P -> 在圆上 X O P -> Col A B X -> X = A \/ X = B.
Proof.
intros.
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
induction(两点重合的决定性 O P).
treat_equalities.
left; auto.

induction(两点重合的决定性 X B).
right; auto.
left.
assert_diffs.
assert(Cong O A O X) by (apply 等长的传递性 with O P; Cong).
assert(Col A O X) by ColR.
assert(HH:= 共线点间距相同要么重合要么中点 O A X H11 H10).
induction HH.
auto.
assert(中点 O A B).
unfold 中点; split; trivial.
apply 等长的传递性 with O P; Cong.
apply False_ind.
apply H5.
apply (中点组的唯一性1 A O ); auto.
Qed.

Lemma 直径上一点距圆上一点小于等于距较远的直径端点 : forall O P A B T X, 直径 A B O P -> Bet B O T -> 在圆上 X O P -> Le T A T X.
Proof.
intros.
unfold 直径 in*.
spliter.
unfold 在圆上 in *.
assert(Cong O X O A) by (apply 等长的传递性 with O P; Cong).
induction(两点重合的决定性 P O).
treat_equalities.
apply AB小于等于AB.
induction(两点重合的决定性 T O).
subst T.
apply 等长则小于等于;Cong.
assert_diffs.
apply(triangle_reverse_inequality O T X A); Cong.
assert_diffs.
repeat split; auto.
apply (l5_2 B); Between.
Qed.


Lemma 直径上一点距圆上另一点小于距较远的直径端点 : forall O P A B T X,
 直径 A B O P -> O <> P -> O <> T -> X <> A -> Bet B O T  -> 在圆上 X O P ->
 Lt T A T X.
Proof.
intros.
assert(HH:= 直径上一点距圆上一点小于等于距较远的直径端点 O P A B T X H H3 H4).
assert(Lt T A T X \/ Cong T A T X).
{
  induction(等长的决定性 T A T X).
  right; auto.
  left.
  unfold Lt.
  split; auto.
}
induction H5; auto.
unfold 直径 in*.
spliter.
unfold 在圆上 in *.
assert_diffs.
assert(Bet O A T \/ Bet O T A).
apply(l5_2 B O A T); Between.
assert (Cong O A O X) by (apply 等长的传递性 with O P; Cong).
induction H13.
assert(Bet O X T).
{
  apply(l4_6 O A T O X T); auto.
  unfold 三角形全等.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_2 O T); Cong.
assert(Bet O T X).
{
  apply(l4_6 O T A O T X); auto.
  unfold 三角形全等.
  repeat split; Cong.
}
apply False_ind.
apply H2.
apply(between_cong_3 O T); Cong.
Qed.



Lemma bet_onc_le_b : forall O P A B T X,
 直径 A B O P -> Bet A O T -> 在圆上 X O P ->
 Le T X T A.
Proof.
intros.
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
apply(triangle_inequality T O X A).
Between.
apply 等长的传递性 with O P; Cong.
Qed.


Lemma bet_onc_lt_b : forall O P A B T X,
 直径 A B O P -> T <> O -> X <> A -> Bet A O T -> 在圆上 X O P ->
 Lt T X T A.
Proof.
intros.
assert(HH:= bet_onc_le_b O P A B T X H H2 H3 ).
assert(Lt T X  T A \/ Cong T A T X).
{
  induction(等长的决定性 T A T X).
  right; auto.
  left.
  unfold Lt.
  split; Cong.
}
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
induction H4; auto.
apply False_ind.
assert(Bet T O A) by eBetween.
assert(Bet T O X).
{
  apply(l4_6 T O A T O X); auto.
  repeat split.
    apply 等长的自反性.
    assumption.
    apply 等长的传递性 with O P; Cong.
}
apply H1.
apply(between_cong_3 T O); trivial.
apply 等长的传递性 with O P; Cong.
Qed.



Lemma incs2_lt_diam : forall O P A B U V, 直径 A B O P -> 在圆内 U O P -> 在圆内 V O P -> Lt U V A B.
Proof.
intros.
unfold 直径 in H.
spliter.
unfold 在圆上 in *.
unfold 在圆内 in *.

induction(两点重合的决定性 O P).
treat_equalities.
unfold Lt in H0.
spliter.
apply AB小于等于CC推出A与B重合 in H.
treat_equalities.
apply False_ind.
apply H0; Cong.

assert(Lt A O A B /\ Lt B O A B).
{
  assert (中点 O A B).
    split; [assumption|apply 等长的传递性 with O P; Cong].
  split.
  apply(严格中点组半段小于全段 ); assert_diffs;auto.
  assert (Lt B O B A) by (assert_diffs; apply 严格中点组半段小于全段; 中点).
  auto using 长度小于的右交换性.
}
spliter.

induction(两点重合的决定性 O U).
treat_equalities.
spliter.
assert(Lt O V O A).
{
  apply(等长保持小于关系 O V O P); Cong.
}
apply (长度小于的传递性 O V O A A B); auto.
apply 长度小于的左交换性; auto.

assert(HH:=由一点往一方向构造等长线段 U O O V).
ex_and HH V'.

assert(Le U V U V').
{
  apply(triangle_inequality U O V V' H8); Cong.
}
assert(Lt U V' A B).
{
  apply(bet2_lt2__lt O O A B U V' H8 H).
  apply(等长保持小于关系 O U O P O U O A); Cong.
  apply(等长保持小于关系 O V O P O V' O B); Cong.
}

apply(长度小于等于_小于_传递性 U V U V' A B); auto.
Qed.

Lemma incs_onc_diam__lt : forall O P A B U V, 直径 A B O P -> 在圆内 U O P -> 在圆上 V O P -> Lt U V A B.
Proof.
intros.
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
unfold 在圆内 in *.

assert(HH:=由一点往一方向构造等长线段 V O O U).
ex_and HH U'.
assert(Lt V U' A B).
{
  apply(bet2_lt_le__lt O O A B V U' H4 H).
  apply 等长的传递性 with O P; Cong.
  apply(等长保持小于关系 O U O P); Cong.
}
assert(Le V U V U').
{
  apply(triangle_inequality V O U U' H4); Cong.
}
apply 长度小于的左交换性.
apply(长度小于等于_小于_传递性 V U V U'); auto.
Qed.

Lemma diam_cong_在圆内等价的在圆外 : forall O P A B U V, 直径 A B O P -> Cong A B U V -> 在圆内 U O P -> 在圆外 V O P.
Proof.
intros.
induction(两点重合的决定性 O P).
treat_equalities.
unfold 在圆内 in H1.

unfold Lt in H1.
spliter.
apply AB小于等于CC推出A与B重合 in H1.
treat_equalities.
apply False_ind.
apply H2; Cong.

assert(HH:= 点与圆的位置关系的决定性 O P V).
induction HH.
assert(Lt U V A B) by  apply(incs_onc_diam__lt O P A B U V H H1 H3).
unfold Lt in H4.
spliter.
apply False_ind.
apply H5; Cong.

induction H3.
assert(HH:=incs2_lt_diam O P A B U V H H1 H3).
unfold Lt in HH.
spliter.
apply False_ind.
apply H5; Cong.
assumption.
Qed.

Lemma diam_uniqueness : forall O P A B X, 直径 A B O P -> Cong A X A B -> 在圆上 X O P -> X = B.
Proof.
intros.
unfold 直径 in *.
spliter.
unfold 在圆上 in *.
induction(两点重合的决定性 O P).
treat_equalities; auto.
assert(Bet A O X).
{
  apply(l4_6 A O B A O X); auto.
  repeat split; Cong.
  apply 等长的传递性 with O P; Cong.
}
assert_diffs.
apply(between_cong_3 A O); auto.
apply 等长的传递性 with O P; Cong.
Qed.

Lemma onc3__ncol : forall O P A B C,
 A <> B -> A <> C -> B <> C ->
 在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
 ~ Col A B C.
Proof.
intros.
assert (Hcong := 在同圆上的两点与圆心等距 O P).
apply (cong2__ncol O); Cong.
Qed.

Lemma diam_exists : forall O P T, exists A, exists B, 直径 A B O P /\ Col A B T.
Proof.
intros.
destruct (存在两端点在圆心两侧的直径 O P T) as [A [B [HBet [HCol [HA HB]]]]].
exists A, B.
repeat split; auto.
Qed.

Lemma chord_intersection : forall O P A B X Y,
  在圆上 A O P -> 在圆上 B O P -> 在圆上 X O P -> 在圆上 Y O P -> TS A B X Y ->
  TS X Y A B.
Proof.
intros.
unfold TS in H3.
spliter.
ex_and H5 T.
repeat split.
apply (onc3__ncol O P); Circle; try(intro; treat_equalities; Col).
apply (onc3__ncol O P); Circle; try(intro; treat_equalities; Col).
exists T.
split.
Col.
assert_diffs.
apply (col_inc_onc2__bet O P); Col.
apply(bet_inc2__incs O P X Y T); Circle; intro; treat_equalities; Col.
Qed.

Lemma ray_cut_chord : forall O P A B X Y,
  直径 A B O P -> 在圆上 X O P -> 在圆上 Y O P -> TS A B X Y -> OS X Y O A ->
  TS X Y O B.
Proof.
intros.
unfold 直径 in *.
spliter.
apply(l9_8_2 X Y A O B); [|Side].
apply (chord_intersection O P); assumption.
Qed.

Lemma center_col__diam : forall O P A B,
 A <> B -> Col O A B -> 在圆上 A O P -> 在圆上 B O P ->
 直径 A B O P.
Proof.
Proof.
intros.
unfold 直径.
split; Circle.
assert(Cong O A O B) by (apply 等长的传递性 with O P; Cong).
assert(A = B \/ 中点 O A B) by (apply(共线点间距相同要么重合要么中点 O A B); Col).
induction H4.
contradiction.
Between.
Qed.

Lemma diam__midpoint: forall O P A B, 直径 A B O P -> 中点 O A B.
Proof.
intros.
unfold 直径 in *.
spliter.
unfold 中点.
unfold 在圆上 in *.
split.
  assumption.
apply 等长的传递性 with O P; Cong.
Qed.

Lemma diam_sym : forall O P A B, 直径 A B O P -> 直径 B A O P.
Proof.
intros.
unfold 直径 in *.
spliter.
repeat split; Between.
Qed.

Lemma diam_end_uniqueness : forall O P A B C, 直径 A B O P -> 直径 A C O P -> B = C.
Proof.
intros.
apply diam__midpoint in H.
apply diam__midpoint in H0.
apply (中点组的唯一性1 A O); 中点.
Qed.


Lemma center_onc2_mid__ncol : forall O P A B M ,
 O <> P -> ~ Col O A B ->
 在圆上 A O P -> 在圆上 B O P ->
 中点 M A B  -> ~ Col A O M.
Proof.
intros.
intro.
assert_diffs.
unfold 中点 in H3.
spliter.
apply H0.
ColR.
Qed.

Lemma bet_chord__diam_or_ncol : forall O P A B T,
  A <> B -> T <> A -> T <> B -> 在圆上 A O P -> 在圆上 B O P -> Bet A T B ->
  直径 A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
induction(共线的决定性 O A B).
left.
apply(center_col__diam); Col.
right.
split.
intro.
apply H5; ColR.
intro.
apply H5; ColR.
Qed.

Lemma mid_chord__diam_or_ncol : forall O P A B T,
 A <> B -> 在圆上 A O P -> 在圆上 B O P ->
 中点 T A B ->
 直径 A B O P \/ ~Col O A T /\ ~Col O B T.
Proof.
intros.
unfold 中点 in H2.
spliter.
apply(bet_chord__diam_or_ncol);auto.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.
Qed.

Lemma cop_mid_onc2_perp__col : forall O P A B X Y, A <> B -> 在圆上 A O P -> 在圆上 B O P ->
  中点 X A B -> Perp X Y A B -> 共面 O A B Y -> Col X Y O.
Proof.
  intros O P A B X Y HAB HAOn HBOn HX HPerp HCop.
  destruct (两点重合的决定性 O X).
    subst; Col.
  apply cop_perp2__col with A B; Cop.
  apply 垂直的左交换性, 弦中点与圆心连线垂直于弦 with P; auto.
Qed.

Lemma cong2_cop2_onc3__eq : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P -> 共面 A B C O ->
  Cong X A X B -> Cong X A X C -> 共面 A B C X ->
  X = O.
Proof.
  intros O P X A B C HAB HAC HBC HAOn HBOn HCOn HCop HCong1 HCong2 HCop1.
  destruct (中点的存在性 A B) as [M1 HM1].
  destruct (中点的存在性 A C) as [M2 HM2].
  assert (HNCol : ~ Col C A B) by (apply (onc3__ncol O P); auto).
  destruct (l10_15 A B M1 C) as [P1 [HPerp1 HOS1]]; Col.
  destruct (l10_15 A C M2 B) as [P2 [HPerp2 HOS2]]; Col.
  assert (HColX1 : Col M1 P1 X).
    apply (cop_mid_onc2_perp__col X A A B); Circle; Perp.
    apply coplanar_perm_12, coplanar_trans_1 with C; Cop.
  assert (HColO1 : Col M1 P1 O).
    apply (cop_mid_onc2_perp__col O P A B); Perp.
    apply coplanar_perm_12, coplanar_trans_1 with C; Cop.
  apply 共线否定排列CBA in HNCol.
  assert (HColX2 : Col M2 P2 X).
    apply (cop_mid_onc2_perp__col X A A C); Circle; Perp.
    apply coplanar_perm_12, coplanar_trans_1 with B; Cop.
  assert (HColO2 : Col M2 P2 O).
    apply (cop_mid_onc2_perp__col O P A C); Perp.
    apply coplanar_perm_12, coplanar_trans_1 with B; Cop.
  assert_diffs.
  destruct (共线的决定性 M1 P1 M2); [apply (l6_21_两线交点的唯一性 M2 P2 M1 P1)|apply (l6_21_两线交点的唯一性 M1 P1 M2 P2)]; Col.
  intro.
  apply HBC.
  destruct (两点重合的决定性 M1 M2).
    apply (中点组的唯一性1 A M1); subst; trivial.
  apply l10_2_uniqueness_spec with M1 P1 A.
    split; Perp; exists M1; Col.
  split.
    exists M2; auto.
  left.
  apply 与垂线共线之线也为垂线2 with P2 M2; Perp; ColR.
Qed.

Lemma tree_points_onc_cop : forall O P, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ 在圆上 A O P /\ 在圆上 B O P /\ 在圆上 C O P /\ 共面 A B C O.
Proof.
  intros O P HOP.
  destruct (两点不重合则存在不共线的点 O P) as [X HNCol]; auto.
  destruct (存在两端点在圆心两侧的直径 O P X) as [B [C [HBet [HCol []]]]].
  exists P, B, C.
  repeat split; Circle.
    intro; subst; apply HNCol; ColR.
    intro; subst; apply HNCol; ColR.
    intro; treat_equalities; auto.
    exists B; left; split; Col.
Qed.

Lemma tree_points_onc_cop2 : forall O P Q, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ 在圆上 A O P /\ 在圆上 B O P /\ 在圆上 C O P /\
  共面 A B C O /\ 共面 A B C Q.
Proof.
  intros O P Q HOP.
  destruct (两点重合的决定性 O Q).
    subst Q.
    destruct (tree_points_onc_cop O P HOP) as [A [B [C]]]; spliter.
    exists A, B, C; repeat split; auto.
  destruct (两点不重合则存在不共线的点 O Q) as [X HNCol]; auto.
  destruct (存在两端点在圆心两侧的直径 O P X) as [B [C [HBet [HCol []]]]].
  destruct (l6_11_existence O O P Q) as [A []]; auto.
  exists A, B, C.
  assert (~ Col O A B) by (intro; unfold 在圆上 in *; assert_diffs; apply HNCol; ColR).
  assert_diffs.
  repeat split; Circle.
    intro; subst; apply HNCol; ColR.
    exists B; left; split; Col.
    exists O; right; right; split; Col.
Qed.

Lemma tree_points_onc : forall O P, O <> P -> exists A B C,
  A <> B /\ A <> C /\ B <> C /\ 在圆上 A O P /\ 在圆上 B O P /\ 在圆上 C O P.
Proof.
  intros O P HOP.
  destruct (tree_points_onc_cop O P HOP) as [A [B [C]]]; spliter.
  exists A, B, C; repeat split; assumption.
Qed.

Lemma bet_cop_onc2__ex_onc_os_out : forall O P A B C I,
  A <> I -> B <> I -> ~ Col A B C -> ~ Col A B O ->
  在圆上 A O P -> 在圆上 B O P -> Bet A I B -> 共面 A B C O ->
  exists C1, Out C1 O I /\ 在圆上 C1 O P /\ OS A B C C1.
Proof.
  intros O P A B C I HAI HBI HNCol HNCol1 HA HB HBet HCop.
  destruct (存在两端点在圆心两侧的直径 O P I) as [C1 [C2 [HBet1 [HCol [HC1 HC2]]]]].
  assert (HTS : TS A B C1 C2).
  { apply (chord_intersection O P); trivial.
    unfold 在圆上 in *; assert_diffs.
    repeat split; [intro; apply HNCol1; ColR..|exists I; split; Col].
  }
  assert (HBet2 : Bet C1 I C2).
  { assert_diffs; apply (col_inc_onc2__bet O P); auto.
    apply bet_inc2__inc with A B; Circle.
  }
  assert (HNCol2 : ~ Col C1 A B) by (destruct HTS; assumption).
  destruct (cop__one_or_two_sides A B C C1); Col.
    apply coplanar_trans_1 with O; Col; [Cop|exists I; right; right; assert_diffs; split; ColR].
  - exists C2.
    split; [|split; trivial; exists C1; Side].
    apply bet2__out with C1; Between.
      intro; treat_equalities; auto.
      destruct HTS as [_ [HNCol3 _]]; spliter; intro; subst; apply HNCol3; Col.
  - exists C1.
    split; [|split; trivial].
    apply bet2__out with C2; trivial.
      intro; treat_equalities; auto.
      intro; subst; apply HNCol2; Col.
Qed.

(** Two circles are equal if and only if they have the same center and the same radius *)

Lemma eqc_chara: forall A B C D, 同圆 A B C D <-> A = C /\ Cong A B C D.
Proof.
  intros A B C D.
  split.
  - intro Heq.
    unfold 同圆 in Heq.
    assert (C = A).
    { destruct (两点重合的决定性 A B) as [|Hd].
      - subst B.
        unfold 在圆上 in Heq.
        assert (Cong A D A A) by (rewrite Heq; Cong).
        treat_equalities.
        destruct (由一点往一方向构造等长线段 A C A C) as [A' []].
        assert (Cong A A' A A) by (rewrite Heq; Cong).
        treat_equalities; auto.
      - destruct (tree_points_onc_cop2 A B C Hd) as [B0 [B1 [B2]]].
        spliter.
        assert (HCong := 在同圆上的两点与圆心等距 C D).
        apply cong2_cop2_onc3__eq with B B0 B1 B2; try (apply HCong; apply Heq); auto.
    }
    subst C.
    split; trivial.
    unfold 在圆上 in Heq.
    rewrite <- (Heq B); Cong.
  - intros [].
    subst C.
    intro X.
    split; intro; [apply 等长的传递性 with A B|apply 等长的传递性 with A D]; Cong.
Qed.

(** Two circles are distinct if and only if there is a point
    belonging to the first and not to the second *)

Lemma neqc_chara : forall A B C D, A <> B ->
  ~ 同圆 A B C D <->
  (exists X, 在圆上 X A B /\ ~ 在圆上 X C D).
Proof.
  intros A B C D HAB.
  split.
  { intro Hneq.
    destruct (两点重合的决定性 C A) as [|HCA].
    { destruct (等长的决定性 A B C D) as [|HNCong].
        exfalso; apply Hneq, eqc_chara; split; auto.
        subst C; exists B; split; Circle.
    }
    destruct (tree_points_onc_cop2 A B C HAB) as [B0 [B1 [B2]]]; spliter.
    destruct (等长的决定性 C B0 C D); [destruct (等长的决定性 C B1 C D);[destruct (等长的决定性 C B2 C D)|]|].
    - exfalso.
      apply HCA.
      apply cong2_cop2_onc3__eq with B B0 B1 B2; auto; apply 等长的传递性 with C D; Cong.
    - exists B2; auto.
    - exists B1; auto.
    - exists B0; auto.
  }
  intros [X [HX Habs]] Heq.
  apply Habs, Heq, HX.
Qed.

(** The 同圆 predicate is an equivalence relation on ordered pairs of points *)

Lemma eqc_refl : forall A B, 同圆 A B A B.
Proof.
  unfold 同圆; tauto.
Qed.

Lemma eqc_sym : forall A B C D, 同圆 A B C D -> 同圆 C D A B.
Proof.
  unfold 同圆.
  intros A B C D Heq X.
  rewrite Heq.
  apply eqc_refl.
Qed.

Lemma eqc_trans : forall A B C D E F, 同圆 A B C D -> 同圆 C D E F -> 同圆 A B E F.
Proof.
  unfold 同圆.
  intros A B C D E F Heq Heq' X.
  rewrite Heq.
  apply Heq'.
Qed.

(** If two circles have three common points, then they are equal *)

Lemma cop2_onc6__eqc : forall A B C O P O' P', A <> B -> B <> C -> A <> C ->
  在圆上 A O P ->  在圆上 B O P -> 在圆上 C O P -> 共面 A B C O ->
  在圆上 A O' P' ->  在圆上 B O' P' -> 在圆上 C O' P' -> 共面 A B C O' ->
  同圆 O P O' P'.
Proof.
  intros A B C O P O' P'; intros.
  assert (HCong := 在同圆上的两点与圆心等距 O P).
  assert (HCong' := 在同圆上的两点与圆心等距 O' P').
  assert (O = O') by (apply (cong4_cop2__eq A B C); Cong).
  apply eqc_chara.
  split.
    assumption.
  subst O'.
  apply 等长的传递性 with O A; Cong.
Qed.

(** If four coplanar points belong to a same sphere, then they belong to a same circle.
    This lemma justifies our definition of 共圆. *)

Lemma 共圆定义_辅助 : forall A B C D, 共圆 A B C D -> exists O P,
  在圆上 A O P /\ 在圆上 B O P /\ 在圆上 C O P /\ 在圆上 D O P /\ 共面 A B C O.
Proof.
  intros A B C D [HCop [O1 [P1]]]; spliter.
  destruct (共线的决定性 A B C).
    exists O1, P1; repeat split; Cop.
  destruct (l11_62_existence A B C O1) as [O []].
  exists O, A.
  assert (HCong := 在同圆上的两点与圆心等距 O1 P1).
  repeat split; [Circle|apply cong2_per2__cong with O1 O1; finish..|assumption].
Qed.

Lemma 等价共圆ABDC : forall A B C D, 共圆 A B C D -> 共圆 B C D A.
Proof.
  unfold 共圆.
  intros A B C D [HCop [O [P]]].
  split.
    Cop.
  exists O, P.
  spliter; repeat split; assumption.
Qed.

Lemma concyclic_gen_perm_1 : forall A B C D,
  共圆或共线 A B C D -> 共圆或共线 B C D A.
Proof.
  intros A B C D [H|].
    left; apply 等价共圆ABDC, H.
    right; spliter; repeat split; Col.
Qed.

Lemma 等价共圆ACBD : forall A B C D, 共圆 A B C D -> 共圆 B A C D.
Proof.
  unfold 共圆.
  intros A B C D [HCop [O [P]]].
  split.
    Cop.
  exists O, P.
  spliter; repeat split; assumption.
Qed.

Lemma concyclic_gen_perm_2 : forall A B C D,
  共圆或共线 A B C D -> 共圆或共线 B A C D.
Proof.
  intros A B C D [H|].
    left; apply 等价共圆ACBD, H.
    right; spliter; repeat split; Col.
Qed.

Lemma 共圆的传递性_1 : forall P Q R A B, ~ Col P Q R ->
  共圆 P Q R A -> 共圆 P Q R B -> 共圆 Q R A B.
Proof.
  intros P Q R A B HNC H1 H2.
  split.
    unfold 共圆 in *; spliter; apply coplanar_trans_1 with P; assumption.
  destruct (共圆定义_辅助 P Q R A H1) as [O [M]].
  destruct (共圆定义_辅助 P Q R B H2) as [O' [M']].
  spliter.
  exists O, M; repeat split; trivial.
  assert_diffs.
  apply (cop2_onc6__eqc P Q R O' M'); auto.
Qed.

Lemma concyclic_gen_trans_1 : forall P Q R A B,
  ~ Col P Q R ->
  共圆或共线 P Q R A -> 共圆或共线 P Q R B ->
  共圆或共线 Q R A B.
Proof.
  intros P Q R A B HNC [|] [|]; [|spliter; exfalso; apply HNC; Col..].
  left.
  apply (共圆的传递性_1 P); assumption.
Qed.

Lemma concyclic_pseudo_trans : forall A B C D P Q R, ~ Col P Q R ->
  共圆 P Q R A -> 共圆 P Q R B -> 共圆 P Q R C -> 共圆 P Q R D ->
  共圆 A B C D.
Proof.
  intros A B C D P Q R HNCol HA HB HC HD.
  spliter.
  split.
    unfold 共圆 in *; spliter; apply coplanar_pseudo_trans with P Q R; assumption.
  destruct (共圆定义_辅助 P Q R A HA) as [OA [MA]].
  destruct (共圆定义_辅助 P Q R B HB) as [OB [MB]].
  destruct (共圆定义_辅助 P Q R C HC) as [OC [MC]].
  destruct (共圆定义_辅助 P Q R D HD) as [OD [MD]].
  spliter.
  assert_diffs.
  exists OA, MA; repeat split; [|apply (cop2_onc6__eqc P Q R OB MB)|
    apply (cop2_onc6__eqc P Q R OC MC)|apply (cop2_onc6__eqc P Q R OD MD)]; auto.
Qed.

Lemma concyclic_gen_pseudo_trans : forall A B C D P Q R,
  ~ Col P Q R ->
  共圆或共线 P Q R A ->
  共圆或共线 P Q R B ->
  共圆或共线 P Q R C ->
  共圆或共线 P Q R D ->
  共圆或共线 A B C D.
Proof.
  intros A B C D P Q R HNC [|] [|] [|] [|]; [|spliter; exfalso; apply HNC; Col..].
  left.
  apply concyclic_pseudo_trans with P Q R; assumption.
Qed.

End Circle_2.

Section Circle_2D.

Context `{T2D:Tarski_2D}.

(** The center of a circle belongs to the perpendicular bisector of each chord *)

Lemma mid_onc2_perp__col : forall O P A B X Y,
 A <> B -> 在圆上 A O P -> 在圆上 B O P -> 中点 X A B -> Perp X Y A B -> Col X Y O.
Proof.
  intros O P A B X Y HAB HAOn HBOn HX HPerp.
  assert (HCop := all_coplanar O A B Y).
  apply cop_mid_onc2_perp__col with P A B; assumption.
Qed.

(** Euclid Book III Prop 4.
 If in a circle two straight lines which do not pass through the center cut one another,
 then they do not bisect one another.
 *)

Lemma mid2_onc4__eq : forall O P A B C D X, B <> C-> A <> B ->
 在圆上 A O P ->
 在圆上 B O P ->
 在圆上 C O P ->
 在圆上 D O P ->
 中点 X A C ->
 中点 X B D ->
 X=O.
Proof.
intros O P A B C D X Hbc.
intros.
assert(HH:=弦中点与圆心连线形成直角 O P A C X H0 H2 H4).
assert(HP:=弦中点与圆心连线形成直角 O P B D X H1 H3 H5).

induction(两点重合的决定性 X O).
auto.
assert(Col A B X).
apply(per2__col A B O X); Perp.
unfold 中点 in *.
spliter.
assert(Col B X D).
apply 中间性蕴含共线1; auto.
assert(Col A X C).
ColR.

induction(两点重合的决定性 A X).
subst X.
treat_equalities.
assert(在圆外 D O P).
apply(onc2_out__outcs O P A B D); auto.
assert_diffs.
unfold Out.
split.
auto.
split.
auto.
left; Between.

unfold 在圆外 in *.
unfold Lt in *.
spliter.
unfold 在圆上 in H3.
apply False_ind.
absurd (Cong O P O D);Cong.

assert(Col A B C). 
ColR.

assert(C = A \/ C = B).
apply(圆交一线于至多两点 O P A B C); Col.
destruct H14.
treat_equalities.
intuition.
treat_equalities.
assert(A = D) by
(apply (中点组的唯一性1 C X); split; Between; Cong).
treat_equalities.
tauto.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle,
 then the point taken is the center of the circle.
*)

Lemma cong2_onc3__eq : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
  Cong X A X B -> Cong X A X C ->
  X = O.
Proof.
  intros O P X A B C HAB HAC HBC HAOn HBOn HCOn HCong1 HCong2.
  assert (HCop := all_coplanar A B C O).
  assert (HCop1 := all_coplanar A B C X).
  apply cong2_cop2_onc3__eq with P A B C; assumption.
Qed.

Lemma onc2_mid_cong_col : forall O P U V M X,
 U <> V ->在圆上 U O P -> 在圆上 V O P -> 中点 M U V -> Cong U X V X -> Col O X M.
Proof.
intros.
assert(HH:=弦中点与圆心连线形成直角 O P U V M H0 H1 H2).
assert(Per X M U).
unfold Per.
exists V.
unfold 在圆上 in *.
split; Cong.
apply(per2__col _ _ U); auto.
assert_diffs.
auto.
Qed.


Lemma cong_onc3_cases : forall O P A X Y,
 Cong A X A Y ->
 在圆上 A O P -> 在圆上 X O P -> 在圆上 Y O P ->
 X = Y \/ 严格对称 X Y O A.
Proof.
intros.
unfold 在圆上 in *.
induction(两点重合的决定性 X Y).
left; auto.
right.
assert(HH:= 中点的存在性 X Y).
ex_and HH M.
assert(Per O M X).
{
  apply(弦中点与圆心连线形成直角 O P X Y M); Circle.
}
assert(Per A M X).
{
  unfold Per.
  exists Y.
  split; auto.
}
assert(Col A O M).
{
  apply (per2__col _ _ X); auto.
  intro.
  treat_equalities; tauto.
}

unfold 严格对称.
split.
exists M.
split; 中点.
Col.
left.

unfold 中点 in *.
spliter.

induction(两点重合的决定性 M O).
subst M.
apply 直角转L形垂直于 in H6.
apply 垂直于的交换性 in H6.
apply 垂直于转垂直 in H6.
apply 垂直的对称性 in H6.
apply (垂线共线点也构成垂直1 X O O A Y) in H6; Col.
Perp.
intro.
treat_equalities; tauto.
intro.
treat_equalities; tauto.

apply(垂线共线点也构成垂直1 O M Y X A);Col.
intro.
treat_equalities; tauto.
apply 直角转L形垂直于 in H5.
apply 垂直于的交换性 in H5.
apply 垂直于转垂直 in H5.
apply 垂直的对称性 in H5.
apply(垂线共线点也构成垂直1 X M M O Y) in H5; auto.
Perp.
Col.
auto.
intro.
treat_equalities; tauto.
Qed.


Lemma bet_cong_onc3_cases : forall O P A X Y T,
 T <> O -> Bet A O T -> Cong T X T Y ->
 在圆上 A O P  -> 在圆上 X O P  -> 在圆上 Y O P ->
 X = Y \/ 严格对称 X Y O A.
Proof.
intros.
unfold 在圆上 in *.
induction(两点重合的决定性 O P).
treat_equalities.
left; auto.

induction(两点重合的决定性 T X).
treat_equalities.
left; auto.

assert(等角 T O X T O Y /\ 等角 O T X O T Y /\ 等角 T X O T Y O).
{
  apply(l11_51 O T X O T Y); Cong.
    intro.
    treat_equalities; tauto.
  apply 等长的传递性 with O P; Cong.
}
spliter.
assert(Out T A O).
{
  repeat split; auto.
  intro.
  treat_equalities; tauto.
  Between.
}
assert(Cong A X A Y).
{ apply(cong2_conga_cong A T X A T Y); Cong.
  apply (l11_10 O T X O T Y); auto.
  apply out_trivial; auto.
  apply out_trivial.
  intro.
  treat_equalities; tauto.
}
apply (cong_onc3_cases O P); auto.
Qed.

Lemma prop_7_8 : forall O P A B T X Y , 直径 A B O P -> Bet A O T 
                               -> 在圆上 X O P -> 在圆上 Y O P
                               -> 角度小于等于 A O X A O Y -> Le T Y T X.
Proof.
intros.
assert(HD:=H).
unfold 直径 in H.
spliter.
unfold 在圆上 in *.
induction(两点重合的决定性 O P).
subst P.
treat_equalities; auto.
apply AB小于等于AB.

induction(两点重合的决定性 O T).
treat_equalities.
apply 等长则小于等于, 等长的传递性 with O P; Cong.

induction(等长的决定性 A X A Y).
assert(X = Y \/ 严格对称 X Y O A).
{
  apply(cong_onc3_cases O P A X Y); Circle.
}
induction H9.
treat_equalities.
apply AB小于等于AB.
apply 等长则小于等于.
apply 等长的对称性.
apply 等长的交换性.
apply(is_image_spec_col_cong O A X Y T); auto.
unfold 直径 in *.
spliter.
ColR.

assert(Le T X T A).
{
  apply(bet_onc_le_b O P A B T X HD H0).
  Circle.
}
assert_diffs.

assert(角度小于等于 Y O T X O T).
{
  apply lea_comm.
  apply(l11_36 A O X A O Y T T); auto.
}

assert(Lt T Y T X).
{
  assert(Cong O X O Y) by (apply 等长的传递性 with O P; Cong).
  apply(t18_18 O T X O T Y); Cong.
  unfold 角度小于.
  split; auto.
  intro.
  assert(Cong Y T X T).
  {
    apply(cong2_conga_cong Y O T X O T); Cong.
  }
  assert(等角 A O X A O Y).
  apply(l11_13 T O X T O Y A A); Between.
  等角.
  apply H8.
  apply(cong2_conga_cong A O X A O Y); Cong.
}
apply 长度小于蕴含小于等于.
assumption.
Qed.




Lemma Prop_7_8_uniqueness : forall O P A X Y Z T, T <> O -> X <> Y ->
  Bet A O T -> Cong T X T Y -> Cong T X T Z ->
  在圆上 A O P -> 在圆上 X O P -> 在圆上 Y O P -> 在圆上 Z O P ->
  Z = X \/ Z = Y.
Proof.
intros.
induction(两点重合的决定性 O P).
unfold 在圆上 in *.
treat_equalities.
auto.
assert(X = Y \/ 严格对称 X Y O A).
{
  apply(bet_cong_onc3_cases O P A X Y T); auto.
}
assert(X = Z \/ 严格对称 X Z O A).
{
  apply(bet_cong_onc3_cases O P A X Z T); auto.
}
assert(Y = Z \/ 严格对称 Y Z O A).
{
  apply(bet_cong_onc3_cases O P A Y Z T); auto.
  apply 等长的传递性 with T X; Cong.
}
induction H9.
contradiction.
induction H10.
auto.
induction H11.
auto.
assert(HH:=l10_2_uniqueness_spec O A Z X Y H10 H11).
contradiction.
Qed.

Lemma chords_midpoints_col_par : forall O P A M B C N D, 
 O <> P ->
 在圆上 A O P -> 在圆上 B O P ->
 在圆上 C O P -> 在圆上 D O P ->
 中点 M A B -> 中点 N C D ->
 Col O M N -> ~ Col O A B -> ~ Col O C D -> Par A B C D.
Proof.
intros.
assert(Perp O M A B).
{
  apply(弦中点与圆心连线垂直于弦 O  P A B M); Circle.
  intro.
  treat_equalities.
  apply H7.
  Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
assert(Perp O N C D).
{
  apply(弦中点与圆心连线垂直于弦 O  P C D N); Circle.
  intro.
  treat_equalities.
  apply H8.
  Col.
  intro.
  treat_equalities.
  apply H8; Col.
}
assert(Perp O M C D).
{
  apply (垂线共线点也构成垂直1 O N C D M); Col.
  intro.
  treat_equalities.
  apply H7; Col.
}
apply (l12_9_2D A B C D O M); Perp.
Qed.

Lemma onc3_mid2__ncol : forall O P A B C A' B',
 O <> P -> 
 在圆上 A O P -> 在圆上 B O P -> 在圆上 C O P ->
 中点 A' A C -> 中点 B' B C -> ~ Col A B C ->
 ~ Col O A' B' \/ A' = O \/ B' = O.
Proof.
intros.
induction(共线的决定性 O A C).
assert(A = C \/ 中点 O A C) by (apply 共线点间距相同要么重合要么中点; [Col|CongR]).
induction H7.
treat_equalities.
apply False_ind.
apply H5; Col.
right; left.
apply (中点的唯一性1 A C); auto.

induction(共线的决定性 O B C).
assert(B = C \/ 中点 O B C) by (apply 共线点间距相同要么重合要么中点; [Col|CongR]).
induction H8.
treat_equalities.
apply False_ind.
apply H5; Col.
right; right.
apply (中点的唯一性1 B C); auto.
left.
intro.
assert(HH:=chords_midpoints_col_par O P A A' C B B' C H H0 H2 H1 H2 H3 H4 H8 H6 H7).
induction HH.
apply H9.
exists C.
split; Col.
spliter; contradiction.
Qed.

(** Euclid Book III Prop 9.
 If a point is taken within a circle,
 and more than two equal straight lines fall from the point on the circle, 
 then the point taken is the center of the circle.*)

Lemma onc4_cong2__eq: 
 forall A B C D O P X,
 A<>B -> C<>D ->
 ~ Par A B C D ->
 在圆上 A O P ->
 在圆上 B O P ->
 在圆上 C O P ->
 在圆上 D O P ->
 Cong A X B X ->
 Cong C X D X ->
 O=X.
Proof.
intros.

assert(HP:O <> P).
{
intro.
unfold 在圆上 in *.
treat_equalities. intuition.
}

assert(HH:= 中点的存在性 A B).
ex_and HH M.
assert(HH:= 中点的存在性 C D).
ex_and HH N.

assert(Col O X M)
 by (apply(onc2_mid_cong_col O P A B M X); auto).
assert(Col O X N)
 by (apply(onc2_mid_cong_col O P C D N X); auto).

induction(两点重合的决定性 O X).
- auto.
- assert(Col O M N) by eCol.


assert(HH1:=与两点等距点要么为其中点要么在其中垂线上 A B M X H H8 H6).
assert(HH2:=与两点等距点要么为其中点要么在其中垂线上 C D N X H0 H9 H7).

induction HH1.
subst X.
induction HH2.
subst N.

induction(共线的决定性 O A B).
assert(A = B \/ 中点 O A B).
unfold 在圆上 in *.
apply 共线点间距相同要么重合要么中点; Col.
apply 等长的传递性 with O P; Cong.
induction H15.
contradiction.
assert(M = O).
apply (中点的唯一性1 A B); auto.
subst M; tauto.

induction(共线的决定性 O C D).
assert(C = D \/ 中点 O C D).
unfold 在圆上 in *.
apply 共线点间距相同要么重合要么中点; Col.
apply 等长的传递性 with O P; Cong.
induction H16.
contradiction.
apply (中点的唯一性1 C D); auto.
assert(HM1:=弦中点与圆心连线垂直于弦 O P A B M H12 H H2 H3 H8).
assert(HM2:=弦中点与圆心连线垂直于弦 O P C D M H12 H0 H4 H5 H9).
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O M); Perp.

spliter.
apply 垂直于转垂直 in H15.
induction(共线的决定性 O A B).
assert(A = B \/ 中点 O A B).
unfold 在圆上 in *.
apply 共线点间距相同要么重合要么中点; Col.
apply 等长的传递性 with O P; Cong.
induction H17.
contradiction.
assert(M = O).
apply (中点的唯一性1 A B); auto.
subst M; tauto.
assert(HM1:=弦中点与圆心连线垂直于弦 O P A B M H12 H H2 H3 H8).
apply(垂线共线点也构成垂直1 M N C D O ) in H15; Col.
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O M); Perp.
induction HH2.
subst X.
spliter.

induction(共线的决定性 O C D).
assert(C = D \/ 中点 O C D).
unfold 在圆上 in *.
apply 共线点间距相同要么重合要么中点; Col.
apply 等长的传递性 with O P; Cong.
induction H17.
contradiction.
apply (中点的唯一性1 C D); auto.

assert(HM1:=弦中点与圆心连线垂直于弦 O P C D N H12 H0 H4 H5 H9).
apply 垂直于转垂直 in H15.
apply False_ind.
apply H1.
apply(垂线共线点也构成垂直1 N M A B O) in H15; Col.

apply (l12_9_2D _ _ _ _ O N); Perp.
spliter.
apply 垂直于转垂直 in H17.
apply 垂直于转垂直 in H16.

apply(垂线共线点也构成垂直1 X M A B O) in H17; Col.
apply(垂线共线点也构成垂直1 X N C D O) in H16; Col.
apply False_ind.
apply H1.
apply (l12_9_2D _ _ _ _ O X); Perp.
Qed.


End Circle_2D.