Require Import GeoCoq.Axioms.beeson_s_axioms.
Require Import GeoCoq.Axioms.tarski_axioms.

Section Proof_of_eq_stability_in_IT.

Context `{BTn:intuitionistic_无维度中性塔斯基公理系统}.

Lemma cong_stability_eq_stability : forall A B : ITpoint, ~ A <> B -> A = B.
Proof.
intros A B HAB.
apply I等长的同一性 with A.
apply Cong_stability.
intro HNCong.
apply HAB.
intro HEq.
subst.
apply HNCong.
apply I等长的伪自反性.
Qed.

End Proof_of_eq_stability_in_IT.

Require Import Classical.

Section Intuitionistic_Tarski_to_Tarski.

Context `{BTn:intuitionistic_无维度中性塔斯基公理系统}.

Lemma col_dec : forall A B C, ICol A B C \/ ~ ICol A B C.
Proof.
intros.
tauto.
Qed.

Lemma eq_dec : forall A B :ITpoint, A=B \/ A<>B.
Proof.
intros.
tauto.
Qed.

Definition BetT A B C := IBet A B C \/ A=B \/ B=C.

Lemma bet_id : forall A B : ITpoint, BetT A B A -> A = B.
Proof.
intros.
unfold BetT in H.
decompose [or] H.
apply I中间性的同一律 in H0.
elim H0.
assumption.
intuition.
Qed.

Lemma IT_chara : forall A B C,
 IT A B C <-> A=B \/ B=C \/ IBet A B C.
Proof.
intros.
unfold IT.
tauto. (* classical *)
Qed.

Lemma BetT_symmetry : forall A B C, BetT A B C -> BetT C B A.
Proof.
intros.
unfold BetT in *.
intuition.
left.
apply I中间性的对称性.
assumption.
Qed.

Lemma BetT_id : forall A B, BetT A B A -> A=B.
Proof.
intros.
unfold BetT in *.
intuition.
apply I中间性的同一律 in H0.
elim H0.
Qed.

(* Lemma 4.1 page 22 *)

Lemma pasch_col_case : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> ICol A B C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
elim (eq_dec A B);intro.
 subst.
 exists B.
 unfold BetT;auto.
elim (eq_dec A C);intro.
 subst.
 apply BetT_id in H.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec B C);intro.
 subst.
 apply BetT_id in H0.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec B Q);intro.
 subst.
 exists Q.
 unfold BetT;auto.
elim (eq_dec C Q);intro.
 subst.
 exists P.
 split.
 unfold BetT;auto.
 apply BetT_symmetry.
 auto.
elim (eq_dec A P);intro.
 subst.
 exists P.
 unfold BetT;auto.
elim (eq_dec C P);intro.
 subst.
 exists Q.
 split.
 apply BetT_symmetry.
 auto.
 unfold BetT;auto.

unfold ICol in H1.
spliter.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in *.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
exists A.
split.
apply I中间性的对称性 in H1.
induction H.
assert (T:=I中间性的内传递性1 B A P C H1 H).
unfold BetT.
left.
apply I中间性的对称性;auto.
induction H;subst.
unfold BetT;auto.
left.
apply I中间性的对称性;auto.
unfold BetT;auto.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.

exists C.

unfold BetT in H.
induction H;induction H0.
split.
apply BetT_symmetry.
left.

apply I中间性的内传递性1 with A.
apply I中间性的对称性;auto.
apply I中间性的对称性;auto.
apply BetT_symmetry.
left.
apply I中间性的内传递性1 with B.
assumption.
apply I中间性的对称性;auto.
induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.

apply NNPP in H1.
induction H;induction H0.

exists B.
split.
unfold BetT;auto.

left.
apply I中间性的对称性.
apply I中间性的内传递性1 with C.
unfold IT in H1.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply not_and_or in H1.
induction H1.
apply NNPP in H1.
subst.
intuition.
apply NNPP in H1.
assumption.
assumption.

induction H0;subst;intuition.
induction H;subst;intuition.
induction H;subst;intuition.
Qed.

Lemma pasch : forall A B C P Q : ITpoint,
        BetT A P C ->
        BetT B Q C -> exists x : ITpoint, BetT P x B /\ BetT Q x A.
Proof.
intros.
induction (col_dec A B C).
eapply pasch_col_case;eauto.

unfold BetT in *.
decompose [or] H;clear H.
decompose [or] H0;clear H0.

elim (I帕施公理 A B C P Q H2 H H1).
intros.
spliter.
exists x.
split.
tauto.
tauto.

subst.
exists Q;auto.
subst.
exists P.
split.
auto.
left.
apply I中间性的对称性.
auto.
subst.
exists P;auto.
subst.
decompose [or] H0;clear H0.
exists Q.
split.
left.
apply I中间性的对称性.
auto.
auto.
subst.
exists Q;auto.
subst.
exists C;auto.
Qed.

Lemma 五线段公理_等价SAS:
 forall A A' B B' C C' D D' : ITpoint,
        ICong A B A' B' ->
        ICong B C B' C' ->
        ICong A D A' D' ->
        ICong B D B' D' ->
        BetT A B C -> BetT A' B' C' -> A <> B -> ICong C D C' D'.
Proof.
intros.
apply I五线段公理_等价SAS with A A' B B' ;try assumption.
unfold IT.
intro.
spliter.
unfold BetT in *.
intuition.
unfold BetT in *.
unfold IT.
intro.
intuition.
Qed.

Lemma IT_trivial : forall A B, IT A A B.
Proof.
intros.
unfold IT.
intro.
spliter.
intuition.
Qed.

Lemma IT_trivial2 : forall A B, IT A B B.
Proof.
intros.
unfold IT.
intro.
spliter.
intuition.
Qed.

Lemma 每个点均有不同点 : forall A, exists B:ITpoint, A<>B.
Proof.
intros.
assert (T:=I防降维公理).
elim (eq_dec A beeson_s_axioms.PA);intro.
subst.
elim (eq_dec beeson_s_axioms.PA beeson_s_axioms.PB);intro.
rewrite <- H in *.
exfalso.
apply T.
apply IT_trivial.
exists beeson_s_axioms.PB.
assumption.
exists beeson_s_axioms.PA.
assumption.
Qed.

Lemma 由一点往一方向构造等长线段 :
 forall A B C D : ITpoint,
        exists E : ITpoint, BetT A B E /\ ICong B E C D.
Proof.
intros.
induction (eq_dec A B).
subst.
elim (每个点均有不同点 B);intros.
elim (I由一点往一方向构造等长线段 x B C D);intros.
exists x0.
split.
unfold BetT.
intuition.
intuition.
intuition.
elim (I由一点往一方向构造等长线段 A B C D H).
intros.
exists x.
spliter.
split;try assumption.
unfold IT in *.
unfold BetT.
tauto.
Qed.

Lemma 防降维公理 :
  ~ (BetT beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC \/ 
     BetT beeson_s_axioms.PB beeson_s_axioms.PC beeson_s_axioms.PA \/ 
     BetT beeson_s_axioms.PC beeson_s_axioms.PA beeson_s_axioms.PB).
Proof.
assert (T:=I防降维公理).
unfold BetT in *.
unfold ICol in  *.
unfold IT in *.
firstorder using I中间性的对称性.
Qed.

Lemma 两点重合的决定性_from_classic : forall A B : ITpoint, A = B \/ A <> B.
Proof.
intros.
apply classic.
Qed.

Instance IT_to_T : 无维度中性塔斯基公理系统.
exact
(Build_无维度中性塔斯基公理系统
   ITpoint BetT ICong
   I等长的伪自反性 I等长的内传递性 I等长的同一性
   由一点往一方向构造等长线段 五线段公理_等价SAS
   bet_id pasch beeson_s_axioms.PA beeson_s_axioms.PB beeson_s_axioms.PC 防降维公理).
Defined.

Instance IT_to_T_PED :
  无维度中性塔斯基公理系统_带两点重合决定性 IT_to_T.
Proof. split; apply 两点重合的决定性_from_classic. Defined.

End Intuitionistic_Tarski_to_Tarski.