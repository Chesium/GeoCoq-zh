(*  Roland Coghetto, 17 March 2018
     GNU Lesser General Public License v3.0 
     See LICENSE GeoCoq 2.3.0 

    MODIFY makarios_variant_axioms,v, Version GeoCoq 2.3.0
    SPLIT 无维度中性塔斯基公理系统_variant
     a) 无维度中性塔斯基公理系统_variant 
     b) 无维度中性塔斯基公理系统_variant_with_decidable_point_equality
*)

(** We describe here a variant of the axiom system proposed by T.J.M. Makarios in June 2013. *)
(** This variant has a slightly different 五线段公理_等价SAS  axioms and allows to remove the 
    等长的伪自反性 axiom.
    All axioms have been shown to be independent except 等长的同一性 and 帕施公理. *)

Class 无维度中性塔斯基公理系统_variant := {
 MTpoint : Type;
 BetM : MTpoint -> MTpoint -> MTpoint -> Prop;
 CongM : MTpoint -> MTpoint -> MTpoint -> MTpoint -> Prop;
 M等长的同一性 : forall A B C, CongM A B C C -> A = B;
 M等长的内传递性 : forall A B C D E F,
   CongM A B C D -> CongM A B E F -> CongM C D E F;
 M由一点往一方向构造等长线段 : forall A B C D,
   exists E, BetM A B E /\ CongM B E C D;
 M五线段公理_等价SAS : forall A A' B B' C C' D D',
   CongM A B A' B' ->
   CongM B C B' C' ->
   CongM A D A' D' ->
   CongM B D B' D' ->
   BetM A B C -> BetM A' B' C' -> A <> B ->
   CongM D C C' D';
 M中间性的同一律 : forall A B, BetM A B A -> A = B;
 M帕施公理 : forall A B C P Q,
   BetM A P C -> BetM B Q C ->
   exists X, BetM P X B /\ BetM Q X A;
 MPA : MTpoint;
 MPB : MTpoint;
 MPC : MTpoint;
 M防降维公理 : ~ (BetM MPA MPB MPC \/ BetM MPB MPC MPA \/ BetM MPC MPA MPB)
 }.

Class 无维度中性塔斯基公理系统_variant_with_decidable_point_equality
 `(Tn : 无维度中性塔斯基公理系统_variant) :=
{
 M两点要么重合要么不重合 : forall A B : MTpoint, A = B \/ ~ A = B
}.
