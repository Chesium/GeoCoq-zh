(*   Roland Coghetto, 17 March 2018
     GNU Lesser General Public License v3.0
     See LICENSE GeoCoq 2.3.0

     MODIFY, tarski_to_makarios,v Version GeoCoq 2.3.0
     MOTIVATION:
     in [1] Lemma 5: A' implies (RE)
     CHANGES: {(Point equality decidability),(TE),(IE),(SC),(FS')} |- (RE)
                                                                    i
     in [1] Lemma 6: if (RE) and (TE) holds, then (FS') is equivalent to (FS).
     CHANGES: a) {(RE), (TE),(FS)} |- (FS')
                                    i
              b) {(Point equality decidability), (TE), (IE) (SC), (FS')} |- (FS)
                                                                          i
     SOURCES:
       [1] Timothy James McKenzie Makarios. A further simplification of
             Tarski’s axioms of geometry. Note di Matematica, 33(2):123–132, 2013.
       [2] tarski_to_makarios,v GeoCoq 2.3.0
       [3] Mizar Mathematical Library (MML 5.46.1331):
             gtarski3.miz, Roland Coghetto and Adam Grabowski.
       [4] Tarski Geometry Axioms, part III.
             R. Coghetto & A. Grabowski.
             Formalized Mathematics Vol. 25 N° 4, 2017.(In preparation).

     in: Section Tarski83_to_Makarios_variant
         ------------------------------------
     REMOVE: 等长的自反性, 等长的对称性, 等长的左交换性.
     MODIFY: 五线段公理_等价SAS'.

     in: Section Makarios_variant_to_Tarski83
         ------------------------------------
     REMOVE: 中间性的对称性, M等长的左交换性.
     ADD: LmCoghGrab, cong_pre_pseudo_reflexivity.
     MODIFY: 等长的伪自反性 (M帕施公理 &
                  M中间性的同一律 are not used to
                  prove 等长的伪自反性)
*)

Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Tarski83_to_Makarios_variant.

Context `{TnEQD:无维度中性塔斯基公理系统}.

Lemma 五线段公理_等价SAS' : forall A A' B B' C C' D D',
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B ->
  Cong D C C' D'.
Proof.
  intros.
  assert(Cong C D C' D').
  intros.
  eapply 五线段公理_等价SAS with A A' B B';assumption.
  assert(Cong C D D C).
  eapply 等长的伪自反性;eauto.
  apply 等长的内传递性 with C D;assumption.
Qed.

Lemma 防降维公理_老版本 :
  exists A B C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB.
exists PC.
apply 防降维公理.
Qed.

Instance Makarios_Variant_follows_from_Tarski : 无维度中性塔斯基公理系统_variant.
Proof.
exact (Build_无维度中性塔斯基公理系统_variant
 Tpoint Bet Cong
 等长的同一性
 等长的内传递性
 由一点往一方向构造等长线段
 五线段公理_等价SAS'
 中间性的同一律
 帕施公理
 PA PB PC
 防降维公理).
Qed.

End Tarski83_to_Makarios_variant.