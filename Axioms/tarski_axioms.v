Require Export GeoCoq.Utils.general_tactics.

(** This version of the axioms of Tarski is the one given in
 Wolfram Schwabhäuser, Wanda Szmielew and Alfred Tarski,
 Metamathematische Methoden in der Geometrie, Springer-Verlag, Berlin, 1983.

This axioms system is the result of a long history of axiom systems for geometry studied by
 Tarski, Schwabhäuser, Szmielew and Gupta.
*)

Class Tarski_neutral_dimensionless :=
{
  (* 塔斯基公理系统中的基本元素：点 *)
 Tpoint : Type;
 (* 三元关系：中间性(betweenness) *)
 Bet : Tpoint -> Tpoint -> Tpoint -> Prop;
 (* 四元关系：线段全等（等长）(congruence) *)
 Cong : Tpoint -> Tpoint -> Tpoint -> Tpoint -> Prop;
 (* 等长的伪自反律 *)
 cong_pseudo_reflexivity : forall A B, Cong A B B A;
 (* 等长的内交换律 *)
 cong_inner_transitivity : forall A B C D E F,
   Cong A B C D -> Cong A B E F -> Cong C D E F;
 (* 等长的同一律 *)
 cong_identity : forall A B C, Cong A B C C -> A = B;
 (* 线段构造：对任一点B，可以由其往任意方向（由A决定）作出一条与CD等长的线段 *)
 segment_construction : forall A B C D,
   exists E, Bet A B E /\ Cong B E C D;
 (* 五线段公理：等价于判定三角形全等的SAS方式，见https://en.wikipedia.org/wiki/File:Five_segment.svg *)
 five_segment : forall A A' B B' C C' D D',
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' ->
   Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D';
 (* 中间性的同一律 *)
 between_identity : forall A B, Bet A B A -> A = B;
 (* 帕施公理，见https://baike.baidu.com/item/%E5%B8%95%E6%96%BD%E5%85%AC%E7%90%86 *)
 inner_pasch : forall A B C P Q,
   Bet A P C -> Bet B Q C ->
   exists X, Bet P X B /\ Bet Q X A;
 (* 任意三点 *)
 PA : Tpoint;
 PB : Tpoint;
 PC : Tpoint;
 (* 低维公理，保证不共线三点的存在性 *)
 lower_dim : ~ (Bet PA PB PC \/ Bet PB PC PA \/ Bet PC PA PB)
}.

Class Tarski_neutral_dimensionless_with_decidable_point_equality
 `(Tn : Tarski_neutral_dimensionless) :=
{
 (* 两点要么重合要么不重合 *)
 point_equality_decidability : forall A B : Tpoint, A = B \/ ~ A = B
}.

Class Tarski_2D
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 (* 高维公理，保证距不同两点距离相同的三点必会共线，见
 https://en.wikipedia.org/wiki/File:Points_in_a_plane_equidistant_to_two_given_points_lie_on_a_line.svg *)
 upper_dim : forall A B C P Q,
   P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
   (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

Class Tarski_3D
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 (* 随意四个点 *)
 S1 : Tpoint;
 S2 : Tpoint;
 S3 : Tpoint;
 S4 : Tpoint;
 lower_dim_3 : ~ exists X,
   (Bet S1 S2 X \/ Bet S2 X S1 \/ Bet X S1 S2) /\ (Bet S3 S4 X \/ Bet S4 X S3 \/ Bet X S3 S4) \/
   (Bet S1 S3 X \/ Bet S3 X S1 \/ Bet X S1 S3) /\ (Bet S2 S4 X \/ Bet S4 X S2 \/ Bet X S2 S4) \/
   (Bet S1 S4 X \/ Bet S4 X S1 \/ Bet X S1 S4) /\ (Bet S2 S3 X \/ Bet S3 X S2 \/ Bet X S2 S3);
 upper_dim_3 : forall A B C P Q R,
   P <> Q -> Q <> R -> P <> R ->
   Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
   Cong A P A R -> Cong B P B R -> Cong C P C R ->
   (Bet A B C \/ Bet B C A \/ Bet C A B)
}.

Class Tarski_euclidean
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 (* 欧几里得公理：与欧几里得平行公理等价，见https://en.wikipedia.org/wiki/File:Tarski%27s_axiom_of_Euclid_C.svg *)
 euclid : forall A B C D T,
   Bet A D T -> Bet B D C -> A<>D ->
   exists X, exists Y,
   Bet A B X /\ Bet A C Y /\ Bet X T Y
}.

Class Tarski_ruler_and_compass
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 (* 圆与圆的连续性？ *)
 circle_circle_continuity : forall A B C D B' D',
   Cong A B' A B -> Cong C D' C D ->
   Bet A D' B -> Bet C B' D ->
   exists Z, Cong A Z A B /\ Cong C Z C D
}.

Class Tarski_continuous
 `(TnEQD : Tarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 (* 连续性公理模式(Axiom Schema of Continuity) *)
 continuity : forall (Alpha Beta : Tpoint -> Prop),
   (exists A, forall X Y, Alpha X -> Beta Y -> Bet A X Y) ->
   (exists B, forall X Y, Alpha X -> Beta Y -> Bet X B Y)
}.