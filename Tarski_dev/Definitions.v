Require Export GeoCoq.Axioms.tarski_axioms.

Section Definitions.

Context `{Tn:无维度中性塔斯基公理系统}.

(** Definition 2.10. *)
(* 八点形成外五线段形式，即五线段公理除去A≠B外 *)
Definition 外五线段形式 A B C D A' B' C' D' :=
  Bet A B C /\ Bet A' B' C' /\
  Cong A B A' B' /\ Cong B C B' C' /\
  Cong A D A' D' /\ Cong B D B' D'.

(** Definition 3.8. *)
(* 共线四点按照A-B-C-D顺序排列 *)
Definition 四点中间性 A1 A2 A3 A4 :=
   Bet A1 A2 A3 /\ Bet A2 A3 A4 /\ Bet A1 A3 A4 /\ Bet A1 A2 A4.

(** Definition 4.1. *)
(* 八点形成内五线段形式，即五线段公理除去A≠B外，并修改CD->BD *)
Definition 内五线段形式 A B C D A' B' C' D' :=
   Bet A B C /\ Bet A' B' C' /\
   Cong A C A' C' /\ Cong B C B' C' /\
   Cong A D A' D' /\ Cong C D C' D'.

(** Definition 4.4. *)
(* 多边形的全等定义：两n边形A1 A2 ... An和B1 B2 ... Bn全等
   当且仅当一多边形的任意两顶点组成的线段与另一多边形的对应相等 *)
(* 以下为三角形、四边形和五边形的例子 *)
Definition 三角形全等 A B C A' B' C' :=
  Cong A B A' B' /\ Cong A C A' C' /\ Cong B C B' C'.

Definition 四边形全等 P1 P2 P3 P4 Q1 Q2 Q3 Q4 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\ Cong P1 P4 Q1 Q4 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P3 P4 Q3 Q4.

Definition 五边形全等 P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 :=
  Cong P1 P2 Q1 Q2 /\ Cong P1 P3 Q1 Q3 /\
  Cong P1 P4 Q1 Q4 /\ Cong P1 P5 Q1 Q5 /\
  Cong P2 P3 Q2 Q3 /\ Cong P2 P4 Q2 Q4 /\ Cong P2 P5 Q2 Q5 /\
  Cong P3 P4 Q3 Q4 /\ Cong P3 P5 Q3 Q5 /\ Cong P4 P5 Q4 Q5.

(** Definition 4.10. *)
(* 三点共线 *)
Definition Col A B C := Bet A B C \/ Bet B C A \/ Bet C A B.

(** Definition 4.15. *)
(* 八点形成五线段形式 *)
Definition 五线段形式 A B C D A' B' C' D' :=
  Col A B C /\ 三角形全等 A B C A' B' C' /\ Cong A D A' D' /\ Cong B D B' D'.

(** Definition 5.4. *)
(* AB≤CD *)
Definition Le A B C D := exists E, Bet C E D /\ Cong A B C E.
(* AB≥CD *)
Definition Ge A B C D := Le C D A B.

(** Definition 5.14. *)
(* AB<CD *)
Definition Lt A B C D := Le A B C D /\ ~ Cong A B C D.
(* AB>CD *)
Definition Gt A B C D := Lt C D A B.

(** Definition 6.1. *)
(* A和B在P的一侧（A、B在P出发的同一条射线上） *)
Definition Out P A B := A <> P /\ B <> P /\ (Bet P A B \/ Bet P B A).

(** Definition 6.22. *)
(* X是A1A2与B1B2的交点 *)
Definition Inter A1 A2 B1 B2 X :=
 B1 <> B2 /\ (exists P, Col P B1 B2 /\ ~ Col P A1 A2) /\
 Col A1 A2 X /\ Col B1 B2 X.

(** Definition 7.1. *)
(* M是A与B的中点 *)
Definition 中点 M A B := Bet A M B /\ Cong A M M B.

(** Definition 8.1. *)
(* ∠ABC=90° *)
Definition Per A B C := exists C', 中点 B C C' /\ Cong A C A C'.

(** Definition 8.11. *)
(* AB⊥CD于X *)
Definition 垂直于 X A B C D :=
  A <> B /\ C <> D /\ Col X A B /\ Col X C D /\
  forall U V, Col U A B -> Col V C D -> Per U X V.

(** Definition 8.11. *)
(* AB⊥CD *)
Definition Perp A B C D := exists X, 垂直于 X A B C D.

(** Definition 9.1. *)
(* P和Q在直线AB异侧 *)
Definition TS A B P Q :=
  ~ Col P A B /\ ~ Col Q A B /\ exists T, Col T A B /\ Bet P T Q.

(** Definition 9.7. *)
(* P和Q在直线AB同侧 *)
Definition OS A B P Q := exists R, TS A B P R /\ TS A B Q R.

(** Satz 9.33. *)
(* ABCD四点共面 *)
Definition 共面 A B C D :=
  exists X, (Col A B X /\ Col C D X) \/
            (Col A C X /\ Col B D X) \/
            (Col A D X /\ Col B C X).

(** Definition 9.37 *)
(* P和Q在平面ABC异侧 *)
Definition 在平面异侧 A B C P Q :=
  ~ 共面 A B C P /\ ~ 共面 A B C Q /\ (exists T, 共面 A B C T /\ Bet P T Q).

(** Definition 9.40 *)
(* P和Q在平面ABC同侧 *)
Definition 在平面同侧 A B C P Q :=
  exists R, 在平面异侧 A B C P R /\ 在平面异侧 A B C Q R.

(** Definition 10.3. *)
(* P和P'明确地关于直线AB对称 *)
Definition 严格对称 P' P A B :=
  (exists X, 中点 X P P' /\ Col A B X) /\ (Perp A B P P' \/ P = P').
(* P和P'关于AB对称，A与B可重合 *)
Definition 对称 P' P A B :=
 (A <> B /\ 严格对称 P' P A B) \/ (A = B /\ 中点 A P P').
(* P和P'明确地关于直线AB对称，对称轴与对称点连线交于M *)
Definition 严格对称于 M P' P A B :=
  (中点 M P P' /\ Col A B M) /\ (Perp A B P P' \/ P = P').
(* P和P'关于AB对称，对称轴与对称点连线交于M，A与B可重合 *)
Definition 对称于 M P' P A B :=
 (A <> B /\ 严格对称于 M P' P A B) \/ (A = B /\ A = M /\ 中点 M P P').

(** Definition 11.2. *)
(* ∠ABC=∠DEF *)
Definition 等角 A B C D E F :=
  A <> B /\ C <> B /\ D <> E /\ F <> E /\
  exists A', exists C', exists D', exists F',
  Bet B A A' /\ Cong A A' E D /\
  Bet B C C' /\ Cong C C' E F /\
  Bet E D D' /\ Cong D D' B A /\
  Bet E F F' /\ Cong F F' B C /\
  Cong A' C' D' F'.

(** Definition 11.23. *)
(* 点P在∠ABC内部 *)
Definition 在角内 P A B C :=
  A <> B /\ C <> B /\ P <> B /\ exists X, Bet A X C /\ (X = B \/ Out B X P).

(** Definition 11.27. *)
(* ∠ABC≤∠DEF *)
Definition 角度小于等于 A B C D E F := exists P, 在角内 P D E F /\ 等角 A B C D E P.
(* ∠ABC≥∠DEF *)
Definition 角度大于等于 A B C D E F := 角度小于等于 D E F A B C.

(** Definition 11.38. *)
(* ∠ABC<∠DEF *)
Definition 角度小于 A B C D E F := 角度小于等于 A B C D E F /\ ~ 等角 A B C D E F.
(* ∠ABC>∠DEF *)
Definition 角度大于 A B C D E F := 角度小于 D E F A B C.

(** Definition 11.39. *)
(* ∠ABC是锐角 *)
Definition 为锐角 A B C :=
  exists A' B' C', Per A' B' C' /\ 角度小于 A B C A' B' C'.

(** Definition 11.39. *)
(* ∠ABC是钝角 *)
Definition 为钝角 A B C :=
  exists A' B' C', Per A' B' C' /\ 角度小于 A' B' C' A B C.

(** Definition 11.59. *)
(* UV⊥平面ABC于X *)
Definition 垂直平面于 X A B C U V :=
  ~ Col A B C /\ U <> V /\ 共面 A B C X /\ Col U V X /\
  forall P Q, 共面 A B C P -> Col U V Q -> Per P X Q.
(* UV⊥平面ABC *)
Definition Orth A B C U V := exists X, 垂直平面于 X A B C U V.

(** Definition 12.2. *)
(* AB∥CD，严格平行，即不允许ABCD四点共线 *)
Definition 严格平行 A B C D :=
  共面 A B C D /\ ~ exists X, Col X A B /\ Col X C D.

(** Definition 12.3. *)
(* AB∥CD *)
Definition Par A B C D :=
  严格平行 A B C D \/ (A <> B /\ C <> D /\ Col A C D /\ Col B C D).

(** Definition 13.4. *)
(* l是描述一线段长度为特定值的一谓词（该类型简称为“长度”），l A B可理解为AB长度为l *)
(* 长度的形式化类型为"Tpoint -> Tpoint -> Prop" *)
Definition Q_Cong l := exists A B, forall X Y, Cong A B X Y <-> l X Y.
(* AB长度为l *)
Definition Len A B l := Q_Cong l /\ l A B.
(* l是描述一线段长度为0的一谓词 *)
Definition 零长谓词 l := Q_Cong l /\ exists A, l A A.
(* 两长度相等 *)
Definition 谓词等长 (l1 l2 : Tpoint -> Tpoint -> Prop) :=
  forall A B, l1 A B <-> l2 A B.
(* a是描述一角大小为特定值的一谓词（该类型简称为“角度”），a A B C可理解为∠ABC大小为a *)
(* 角度的形式化类型为"Tpoint -> Tpoint -> Tpoint -> Prop" *)
Definition 角谓词 a :=
  exists A B C,
    A <> B /\ C <> B /\ forall X Y Z, 等角 A B C X Y Z <-> a X Y Z.
(* ∠ABC大小为a *)
Definition Ang A B C a := 角谓词 a /\ a A B C.
(* a是描述一角为平角的一谓词 *)
Definition 平角谓词 a := 角谓词 a /\ forall A B C, a A B C -> Bet A B C.
(* 两角度相等 *)
Definition EqA (a1 a2 : Tpoint -> Tpoint -> Tpoint -> Prop) :=
  forall A B C, a1 A B C <-> a2 A B C.

(** Definition 13.9. *)
(* 存在一条过P，同时垂直于直线AB与直线CD的线 *)
Definition Perp2 A B C D P :=
  exists X Y, Col P X Y /\ Perp X Y A B /\ Perp X Y C D.
(* a是描述一锐角大小为特定值的一谓词 *)
Definition 锐角谓词 a :=
  exists A B C,
    为锐角 A B C /\ forall X Y Z, 等角 A B C X Y Z <-> a X Y Z.
(* 锐角∠ABC大小为a *)
Definition 锐角 A B C a := 锐角谓词 a /\ a A B C.
(* a是描述一角为非零角的一谓词 *)
Definition 非零角谓词 a := 角谓词 a /\ forall A B C, a A B C -> ~ Out B A C.
(* a是描述一角为非平角的一谓词 *)
Definition 非平角谓词 a := 角谓词 a /\ forall A B C, a A B C -> ~ Bet A B C.
(* a是描述一角为零角的一谓词 *)
Definition 零角谓词 a := 角谓词 a /\ forall A B C, a A B C -> Out B A C.
(* a是描述一锐角为零角的一谓词 *)
Definition 锐零角谓词 a :=
  锐角谓词 a /\ forall A B C, a A B C -> Out B A C.
(* a是描述一角为零角的一谓词，另一种描述 *)
Definition 零角谓词' a :=
  锐角谓词 a /\ exists A B C, a A B C /\ Out B A C.
(* a是描述一锐角为非零角的一谓词 *)
Definition 非锐零角谓词 a :=
  锐角谓词 a /\ forall A B C, a A B C -> ~ Out B A C.
(* cos(a)=lb/lc，a为锐角 *)
Definition Lcos lb lc a :=
  Q_Cong lb /\ Q_Cong lc /\ 锐角谓词 a /\
  (exists A B C, (Per C B A /\ lb A B /\ lc A C /\ a B A C)).

Definition Eq_Lcos la a lb b := exists lp, Lcos lp la a /\ Lcos lp lb b.

Definition Lcos2 lp l a b := exists la, Lcos la l a /\ Lcos lp la b.

Definition Eq_Lcos2 l1 a b l2 c d :=
  exists lp, Lcos2 lp l1 a b /\ Lcos2 lp l2 c d.

Definition Lcos3 lp l a b c :=
  exists la lab, Lcos la l a /\ Lcos lab la b /\ Lcos lp lab c.

Definition Eq_Lcos3 l1 a b c l2 d e f :=
  exists lp, Lcos3 lp l1 a b c /\ Lcos3 lp l2 d e f.

(** Definition 14.1. *)

Definition Ar1 O E A B C :=
 O <> E /\ Col O E A /\ Col O E B /\ Col O E C.

Definition Ar2 O E E' A B C :=
 ~ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C.

(** Definition 14.2. *)

Definition Pj A B C D := Par A B C D \/ C = D.

(** Definition 14.3. *)

Definition Sum O E E' A B C :=
 Ar2 O E E' A B C /\
 exists A' C',
 Pj E E' A  A' /\ Col O E' A' /\
 Pj O E  A' C' /\
 Pj O E' B  C' /\
 Pj E' E C' C.

Definition Proj P Q A B X Y :=
  A <> B /\ X <> Y /\ ~Par A B X Y  /\ Col A B Q /\ (Par P Q X Y \/ P = Q).

Definition Sump O E E' A B C :=
 Col O E A /\ Col O E B /\
 exists A' C' P',
   Proj A A' O E' E E' /\
   Par O E A' P' /\
   Proj B C' A' P' O E' /\
   Proj C' C O E E E'.

(** Definition 14.4. *)

Definition Prod O E E' A B C :=
 Ar2 O E E' A B C /\
 exists B', Pj E E' B B' /\ Col O E' B' /\ Pj E' A B' C.

Definition Prodp O E E' A B C :=
 Col O E A /\ Col O E B /\
 exists B', Proj B B' O E' E E' /\ Proj B' C O E A E'.

(** Definition 14.8. *)

Definition Opp O E E' A B :=
 Sum O E E' B A O.

(** Definition 14.38. *)

Definition Diff O E E' A B C :=
  exists B', Opp O E E' B B' /\ Sum O E E' A B' C.

Definition sum3 O E E' A B C S :=
  exists AB, Sum O E E' A B AB /\ Sum O E E' AB C S.

Definition Sum4 O E E' A B C D S :=
  exists ABC, sum3 O E E' A B C ABC /\ Sum O E E' ABC D S.

Definition sum22 O E E' A B C D S :=
  exists AB CD, Sum O E E' A B AB /\ Sum O E E' C D CD /\ Sum O E E' AB CD S.

Definition Ar2_4 O E E' A B C D :=
  ~ Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D.

(** Definition 14.34. *)

Definition Ps O E A := Out O A E.

Definition Ng O E A := A <> O /\ E <> O /\ Bet A O E .

(** Definition 14.38. *)

Definition LtP O E E' A B := exists D, Diff O E E' B A D /\ Ps O E D.

Definition LeP O E E' A B := LtP O E E' A B \/ A = B.

Definition Length O E E' A B L :=
 O <> E /\ Col O E L /\ LeP O E E' O L /\ Cong O L A B.

(** Definition 15.1. *)

Definition Is_length O E E' A B L :=
 Length O E E' A B L \/ (O = E /\ O = L).

Definition Sumg O E E' A B C :=
  Sum O E E' A B C \/ (~ Ar2 O E E' A B B /\ C = O).

Definition Prodg O E E' A B C :=
  Prod O E E' A B C \/ (~ Ar2 O E E' A B B /\ C = O).

Definition PythRel O E E' A B C :=
  Ar2 O E E' A B C /\
  ((O = B /\ (A = C \/ Opp O E E' A C)) \/
   exists B', Perp O B' O B /\ Cong O B' O B /\ Cong O C A B').

Definition SignEq O E A B := Ps O E A /\ Ps O E B \/ Ng O E A /\ Ng O E B.

Definition LtPs O E E' A B := exists D, Ps O E D /\ Sum O E E' A D B.

(** Definition 16.1. *)
(** We skip the case of dimension 1. *)

Definition Cs O E S U1 U2 :=
   O <> E /\ Cong O E S U1 /\ Cong O E S U2 /\ Per U1 S U2.


(** Q is the orthogonal projection of P on the line AB. *)

Definition Projp P Q A B :=
  A <> B /\ ((Col A B Q /\ Perp A B P Q) \/ (Col A B P /\ P = Q)).

(** Definition 16.5. *)
(** P is of coordinates (X,Y) in the grid SU1U2 using unit length OE. *)

Definition Cd O E S U1 U2 P X Y :=
  Cs O E S U1 U2 /\ 共面 P S U1 U2 /\
  (exists PX, Projp P PX S U1 /\ 三角形全等 O E X S U1 PX) /\
  (exists PY, Projp P PY S U2 /\ 三角形全等 O E Y S U2 PY).


(** Strict betweenness *)

Definition BetS A B C : Prop := Bet A B C /\ A <> B /\ B <> C.

(** Definition of the sum of segments.
    长度之和 A B C D E F means that AB + CD = EF. *)

Definition 长度之和 A B C D E F := exists P Q R,
  Bet P Q R /\ Cong P Q A B /\ Cong Q R C D /\ Cong P R E F.

(** PQ is the perpendicular bisector of segment AB *)

Definition 中垂线 P Q A B := 严格对称 A B P Q /\ A <> B.

Definition 中垂线_另一定义 P Q A B :=
  exists I, 垂直于 I P Q A B /\ 中点 I A B.

Definition 在中垂线上 P A B := Cong A P P B.

(** Definition of the sum of angles.
    和角 A B C D E F G H I means that ABC + DEF = GHI. *)

Definition 和角 A B C D E F G H I :=
  exists J, 等角 C B J D E F /\ ~ OS B C A J /\ 共面 A B C J /\ 等角 A B J G H I.

(** The 和角不大于平角 predicate describes the fact that the sum of the two angles is "at most straight" *)

Definition 和角不大于平角 A B C D E F :=
  A <> B /\ (Out E D F \/ ~ Bet A B C) /\
  exists J, 等角 C B J D E F /\ ~ OS B C A J /\ ~ TS A B C J /\ 共面 A B C J.

(** Supplementary angles *)

Definition 互为补角 A B C D E F :=
  A <> B /\ exists A', Bet A B A' /\ 等角 D E F C B A'.

(** Definition of the sum of the interior angles of a triangle.
    三角形内角和 A B C D E F means that the sum of the angles of the triangle ABC
    is equal to the angle DEF *)

Definition 三角形内角和 A B C D E F :=
  exists G H I, 和角 A B C B C A G H I /\ 和角 G H I C A B D E F.

(** The difference between a straight angle and the sum of the angles of the triangle ABC.
    It is a non-oriented angle, so we can't discriminate between positive and negative difference *)

Definition 三角形内角和与平角之差 A B C D E F := exists G H I,
  三角形内角和 A B C G H I /\ 互为补角 G H I D E F.

(** P is on the circle of center A going through B *)

Definition 在圆上 P A B := Cong A P A B.

(** P is inside or on the circle of center A going through B *)

Definition 在圆上或圆内 P A B := Le A P A B.

(** P is outside or on the circle of center A going through B *)

Definition 在圆上或圆外 P A B := Le A B A P.

(** P is strictly inside the circle of center A going through B *)

Definition 在圆内 P A B := Lt A P A B.

(** P is strictly outside the circle of center A going through B *)

Definition 在圆外 P A B := Lt A B A P.

(** The line segment AB is a diameter of the circle of center O going through P *)

Definition 直径 A B O P := Bet A O B /\ 在圆上 A O P /\ 在圆上 B O P.

Definition 同圆 A B C D :=
 forall X, 在圆上 X A B <-> 在圆上 X C D.

(** The circles of center A passing through B and
                of center C passing through D intersect
                in two distinct points P and Q. *)

Definition 两圆相交于 A B C D P Q :=
  ~ 同圆 A B C D /\
  P<>Q /\ 在圆上 P C D /\ 在圆上 Q C D /\ 在圆上 P A B /\ 在圆上 Q A B.


(** The circles of center A passing through B and
                of center C passing through D
                have two distinct intersections. *)

Definition 两圆相交 A B C D :=
 exists P Q, 两圆相交于 A B C D P Q.

(** The circles of center A passing through B and
                of center C passing through D
                are tangent. *)

Definition 两圆相切 A B C D := exists !X, 在圆上 X A B /\ 在圆上 X C D.

(** The line AB is tangent to the circle OP *)

Definition 圆的切线 A B O P := exists !X, Col A B X /\ 在圆上 X O P.

Definition 圆的切线切于 A B O P T :=
  圆的切线 A B O P /\ Col A B T /\ 在圆上 T O P.

(** The points A, B, C and D belong to a same circle *)

Definition 共圆 A B C D := 共面 A B C D /\
  exists O P, 在圆上 A O P /\ 在圆上 B O P /\ 在圆上 C O P /\ 在圆上 D O P.

(** The points A, B, C and D are concyclic or lined up *)

Definition 共圆或共线 A B C D :=
  共圆 A B C D \/ (Col A B C /\ Col A B D /\ Col A C D /\ Col B C D).

(** C is on the graduation based on [AB] *)
Inductive Grad : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | 线性刻度_初始化 : forall A B, Grad A B B
  | 线性刻度_步进 : forall A B C C',
                  Grad A B C ->
                  Bet A C C' -> Cong A B C C' ->
                  Grad A B C'.

Definition Reach A B C D := exists B', Grad A B B' /\ Le C D A B'.

(** There exists n such that AC = n times AB and DF = n times DE *)
Inductive 在同样的线性刻度上 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop :=
  | 双重线性刻度_初始化 : forall A B D E, 在同样的线性刻度上 A B B D E E
  | 双重线性刻度_步进 : forall A B C C' D E F F',
                   在同样的线性刻度上 A B C D E F ->
                   Bet A C C' -> Cong A B C C' ->
                   Bet D F F' -> Cong D E F F' ->
                   在同样的线性刻度上 A B C' D E F'.

(** Graduation based on the powers of 2 *)
Inductive 在对数刻度上 : Tpoint -> Tpoint -> Tpoint -> Prop :=
  | 对数刻度_初始化 : forall A B, 在对数刻度上 A B B
  | 对数刻度_步进 : forall A B C C',
                     在对数刻度上 A B C ->
                     Bet A C C' -> Cong A C C C' ->
                     在对数刻度上 A B C'.

Inductive 在同样的对数刻度上 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop :=
  | 双重对数刻度_初始化 : forall A B D E, 在同样的对数刻度上 A B B D E E
  | 双重对数刻度_步进 : forall A B C C' D E F F',
                      在同样的对数刻度上 A B C D E F ->
                      Bet A C C' -> Cong A C C C' ->
                      Bet D F F' -> Cong D F F F' ->
                      在同样的对数刻度上 A B C' D E F'.

(** There exists n such that the angle DEF is congruent to n times the angle ABC *)
Inductive 角度在线性刻度上 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                  Prop :=
  | 角度线性刻度_初始化 : forall A B C D E F, 等角 A B C D E F -> 角度在线性刻度上 A B C D E F
  | 角度线性刻度_步进 : forall A B C D E F G H I,
                   角度在线性刻度上 A B C D E F ->
                   和角不大于平角 D E F A B C -> 和角 D E F A B C G H I ->
                   角度在线性刻度上 A B C G H I.

(** There exists n such that the angle DEF is congruent to 2^n times the angle ABC *)
Inductive 角度在对数刻度上 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint -> Tpoint ->
                     Prop :=
  | 角度对数刻度_初始化 : forall A B C D E F, 等角 A B C D E F -> 角度在对数刻度上 A B C D E F
  | 角度对数刻度_步进 : forall A B C D E F G H I,
                      角度在对数刻度上 A B C D E F ->
                      和角不大于平角 D E F D E F -> 和角 D E F D E F G H I ->
                      角度在对数刻度上 A B C G H I.

(** 平行四边形 *)

Definition 严格平行四边形 A B A' B' :=
  TS A A' B B' /\ Par A B A' B' /\ Cong A B A' B'.

Definition 退化平行四边形 A B A' B' :=
  Col A B A' /\ Col A B B' /\
  Cong A B A' B' /\ Cong A B' A' B /\
  (A <> A' \/ B <> B').

Definition 平行四边形 A B A' B' :=
  严格平行四边形 A B A' B' \/ 退化平行四边形 A B A' B'.

Definition 平四 A B C D :=
  (A <> C \/ B <> D) /\ exists M, 中点 M A C /\ 中点 M B D.

(** 菱形 *)

Definition 菱形 A B C D := 平四 A B C D /\ Cong A B B C.

(** 长方形 *)

Definition 长方形 A B C D := 平四 A B C D /\ Cong A C B D.

(** 正方形 *)

Definition 正方形 A B C D := 长方形 A B C D /\ Cong A B B C.

(** 筝形 *)

Definition 筝形 A B C D := Cong B C C D /\ Cong D A A B.

(** 萨凯里四边形 *)
(* 
  C- - - -B -
  |      *| ^         *---saccheri.v中有公理决定该角的类型：为锐角、直角还是钝角
  =       = |同侧 等距
  |90   90| v
  D-------A -
  |
  x
*)
Definition 萨凯里四边形 A B C D :=
  Per B A D /\ Per A D C /\ Cong A B C D /\ OS A D B C.

(** Lambert四边形 *)

Definition Lambert四边形 A B C D :=
  A <> B /\ B <> C /\ C <> D /\ A <> D /\ Per B A D /\ Per A D C /\ Per A B C /\ 共面 A B C D.

(** Vector *)

Definition EqV A B C D := 平行四边形 A B D C \/ A = B /\ C = D.

Definition SumV A B C D E F := forall D', EqV C D B D' -> EqV A D' E F.

Definition SumV_exists A B C D E F := exists D', EqV B D' C D /\ EqV A D' E F.

Definition Same_dir A B C D :=
  A = B /\ C = D \/ exists D', Out C D D' /\ EqV A B C D'.

Definition Opp_dir A B C D := Same_dir A B D C.

(** Projections *)

Definition 等角_3 A B C A' B' C' :=
  等角 A B C A' B' C' /\ 等角 B C A B' C' A' /\ 等角 C A B C' A' B'.

End Definitions.