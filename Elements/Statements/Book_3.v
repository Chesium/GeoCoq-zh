(** * Euclid's Elements

  Book III
*)

Require Export GeoCoq.Tarski_dev.Annexes.tangency.
Require Export GeoCoq.Tarski_dev.Annexes.inscribed_angle.

Section Book_3.

Context `{TE:Tarski_2D}.

(** * Proposition 1
To find the center of a given circle.
        *)

(** We do not formalize this proposition,
    because in our formalization circles are given by
    their center and one point on the circle. *)

(** * Proposition 2
If on the circumference of a circle two points are taken at random, the straight line joining the points will fall within the circle.
        *)

Lemma prop_2 : forall O P U V X,
 X <> U -> X <> V ->
 Bet U X V ->
 在圆上 U O P ->
 在圆上 V O P ->
 在圆内 X O P.
Proof.
intros O P U V X; intros.
apply bet_inc2__incs with U V; Circle.
Qed.

(** * Proposition 3
If in a circle a straight line passing through the center bisects a straight line not passing through the center, it also cuts it at right angles; and if it cut it at right angles, it also bisects it.
        *)

Lemma prop_3_1 : forall O P A B X,
 O <> X -> A <> B ->
 在圆上 A O P ->
 在圆上 B O P ->
 中点 X A B ->
 Perp O X A B.
Proof.
exact 弦中点与圆心连线垂直于弦.
Qed.

Lemma prop_3_2 : forall O P A B X,
 O<>X -> A<>B ->
 Col A B X ->
 在圆上 A O P ->
 在圆上 B O P ->
 Perp O X A B ->
 中点 X A B.
Proof.
exact 垂直于弦的直径平分弦.
Qed.

(** * Proposition 4
If in a circle two straight lines cut one another which are not through the center, they do not bisect one another.
        *)

Lemma prop_4 : forall O P A B C D X, B <> C -> A <> B ->
 在圆上 A O P ->
 在圆上 B O P ->
 在圆上 C O P ->
 在圆上 D O P ->
 中点 X A C ->
 中点 X B D ->
 X = O.
Proof.
exact mid2_onc4__eq.
Qed.

(** * Proposition 5
If two circles cut one another, they will not have the same center.
        *)

Lemma prop_5 :  forall A B C D,
 两圆相交 A B C D ->
 A <> C.
Proof.
exact 相交圆圆心不同.
Qed.


(** * Proposition 6
If two circles touch one another, they will not have the same center.
        *)

Lemma prop_6: forall A B C D,
 A <> B ->
 两圆相切 A B C D ->
 A <> C.
Proof.
exact 相切圆圆心不同.
Qed.

(** * Proposition 9
If a point is taken within a circle, and more than two equal straight lines fall from the point on the circle, the point taken is the center of the circle.
       *)

Lemma prop_9 : forall O P X A B C, A <> B -> A <> C -> B <> C ->
  在圆上 A O P ->
  在圆上 B O P ->
  在圆上 C O P ->
  Cong X A X B ->
  Cong X A X C ->
  X = O.
Proof.
exact cong2_onc3__eq.
Qed.

(** * Proposition 11
If two circles touch one another internally, and their centers are taken, the straight line joining their centers, being produced, will fall on the point of contact of the circles.
       *)

(** * Proposition 12
If two circles touch one another externally, the straight line joining their centers will pass through the point of contact.
       *)

(** In our formalization we do not need to distinguish between
    the two kinds of tangency. *)

Lemma prop_11_12 : forall A B C D X,
 两圆相切 A B C D ->
 在圆上 X A B ->
 在圆上 X C D ->
 Col X A C.
Proof.
exact 两圆切点与两圆心共线.
Qed.


(** * Proposition 18
If a straight line touches a circle, and a straight line is joined from the center to the point of contact, the straight line so joined will be perpendicular to the tangent.
*)

Lemma prop_18 : 
forall A B O P T,
 O <> P ->
 圆的切线切于 A B O P T ->
 Perp A B O T.
Proof.
exact 切点所在半径与切线垂直于切点.
Qed.

End Book_3.