Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Makarios_variant_to_Tarski83.

Context `{MTn:无维度中性塔斯基公理系统_variant_with_decidable_point_equality}.

Ltac prolong A B x C D :=
 assert (sg:= M由一点往一方向构造等长线段 A B C D);
 ex_and sg x.

Lemma M等长的自反性 : forall A B,
 CongM A B A B.
Proof.
intros.
prolong B A x A B.
eapply M等长的内传递性 with A x;auto.
Qed.

Lemma M等长的对称性 : forall A B C D ,
 CongM A B C D -> CongM C D A B.
Proof.
intros.
eapply M等长的内传递性.
apply H.
apply M等长的自反性.
Qed.

Lemma ABB中间性 : forall A B, BetM A B B.
Proof.
intros.
prolong A B x B B.
assert (x = B)
 by (apply M等长的同一性 in H0;auto).
subst;assumption.
Qed.

Lemma M等长的平凡同一性 : forall A B, CongM A A B B.
Proof.
  intros.
  assert (sg:= M由一点往一方向构造等长线段 A A B B);
  ex_and sg x.
  assert( A = x) by (eapply M等长的同一性;eauto).
  subst.
  assumption.
Qed.

Lemma LmCoghGrab : forall A B C D E F,
  A <> B -> BetM B A C -> BetM D A E ->
  CongM B A D A -> CongM A C A E -> CongM B F D F ->
  CongM F C E F.
Proof.
  intros.
  assert(CongM A F A F) by (eapply M等长的自反性;eauto).
  assert(forall A A' B B' C C' D D':MTpoint,
   CongM A B A' B' -> CongM B C B' C' ->
   CongM A D A' D' -> CongM B D B' D' ->
   BetM A B C -> BetM A' B' C' -> A <> B ->
   CongM D C C' D') by apply M五线段公理_等价SAS.
  apply (H6 B D A A);auto.
Qed.

Lemma cong_pre_pseudo_reflexivity : forall A B C D,
  C <> D -> BetM D C B -> CongM A B B A.
Proof.
  intros.
  assert(CongM C B C B) by (eapply M等长的自反性;eauto).
  assert(CongM D C D C) by (eapply M等长的自反性;eauto).
  assert(CongM D A D A) by (eapply M等长的自反性;eauto).
  eapply LmCoghGrab;eauto.
Qed.

Lemma 等长的伪自反性 : forall A B, CongM A B B A.
Proof.
  intros.
  elim (M两点要么重合要么不重合 A B).
    intros.
    subst.
    eapply M等长的平凡同一性;eauto.

    intros.
    assert(BetM B A A) by (eapply ABB中间性;eauto).
    eapply M等长的对称性;eauto.
    eapply cong_pre_pseudo_reflexivity;eauto.
Qed.

Lemma 五线段公理_等价SAS : forall A A' B B' C C' D D',
  CongM A B A' B' ->
  CongM B C B' C' ->
  CongM A D A' D' ->
  CongM B D B' D' ->
  BetM A B C -> BetM A' B' C' -> A <> B ->
  CongM C D C' D'.
Proof.
  intros.
  assert(CongM D C C' D').
  intros.
  eapply M五线段公理_等价SAS with A A' B B';assumption.
  assert(CongM D C C D).
  eapply 等长的伪自反性;eauto.
  eapply M等长的内传递性 with D C;eauto.
Qed.

Instance Tarski_follows_from_Makarios_Variant : 无维度中性塔斯基公理系统.
Proof.
exact (Build_无维度中性塔斯基公理系统
 MTpoint BetM CongM
 等长的伪自反性
 M等长的内传递性
 M等长的同一性
 M由一点往一方向构造等长线段
 五线段公理_等价SAS
 M中间性的同一律
 M帕施公理
 MPA MPB MPC
 M防降维公理).
Defined.

Instance Tarski_follows_from_Makarios_Variant_with_decidable_point_equality' :
  无维度中性塔斯基公理系统_带两点重合决定性 Tarski_follows_from_Makarios_Variant.
Proof. split; apply M两点要么重合要么不重合. Defined.

End Makarios_variant_to_Tarski83.