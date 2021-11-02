Require Export GeoCoq.Tarski_dev.Ch12_parallel.
Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section Triangles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Section ABC.

Variable A B C : Tpoint.

Definition isosceles A B C :=
 Cong A B B C.

Lemma isosceles_sym :
  isosceles A B C ->
  isosceles C B A.
Proof.
unfold isosceles.
intros.
Cong.
Qed.

Lemma isosceles_conga :
  A<>C -> A<>B ->
  isosceles A B C ->
  等角 C A B A C B.
Proof.
intros.
apply cong3_conga.
auto.
auto.
unfold 三角形全等.
unfold isosceles in H.
repeat split;Cong.
Qed.

Lemma conga_isosceles :
 ~ Col A B C ->
 等角 C A B A C B ->
 isosceles A B C. 
Proof.
intros.
assert (Cong B A B C)
 by (apply l11_44_1_b;finish;等角).
unfold isosceles.
Cong.
Qed.

(** In a triangle isosceles in A the altitude wrt. A, is also the bisector and median. *)

Lemma isosceles_foot__midpoint_conga :
 forall H,
 isosceles A B C ->
 Col H A C -> 
 Perp H B A C ->
 ~ Col A B C /\ A<>H /\ C<>H /\ 中点 H A C /\ 等角 H B A H B C.
Proof.
intros.
assert_diffs.
assert (~ Col A B C).
 {
   intro;apply perp_not_col2 in H2.
   destruct H2;apply H2;ColR.
 }
assert_diffs. 
assert (A<>H).
 { (** these point are distinct
      because otherwise the hypothenuse is not larger than the side *)
 intro.
 treat_equalities.
 assert (Lt A B B C /\ Lt A C B C).
 apply (l11_46 B A C);Col; left;apply perp_per_2;auto.
 spliter.
 unfold isosceles in *.
 apply (cong__nlt A B B C);auto.
 }
assert (C<>H).
 {
 intro.
 treat_equalities.
 assert (Lt C B B A /\ Lt C A B A).
 apply (l11_46 B C A);Col; left;apply perp_per_2;finish.
 spliter.
 unfold isosceles in *.
 apply (cong__nlt C B B A);finish.
 } 
assert (垂直于 H A C B H)
 by (apply l8_14_2_1b_bis;finish).
assert (Per A H B) by (apply perp_in_per_1 with C H;finish).
assert (Per C H B) by (apply perp_in_per_3 with A H;finish). 
(* We prove that A H B and C H B are congruent triangles *)
assert (Cong H A H C /\ 等角 H A B H C B /\ 等角 H B A H B C)
 by (apply (cong2_per2__cong_conga2 A H B C H B);finish).
spliter.
assert (中点 H A C)
 by (apply l7_20_bis;finish).
auto.
Qed.

Definition equilateral A B C :=
 Cong A B B C /\ Cong B C C A.

Definition equilateral_strict A B C :=
 equilateral A B C /\ A <> B.

Lemma equilateral_strict_equilateral :
 equilateral_strict A B C ->
 equilateral A B C.
Proof.
unfold equilateral_strict in *. tauto.
Qed.

Lemma equilateral_cong:
  equilateral A B C ->
  Cong A B B C /\ Cong B C C A /\ Cong C A A B.
Proof.
unfold equilateral;intros;intuition Cong.
assert (T:=等长的传递性 A B B C C A H0 H1).
Cong.
Qed.

Lemma equilateral_rot :
 equilateral A B C ->
 equilateral B C A.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap :
 equilateral A B C ->
 equilateral B A C.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_rot_2 :
 equilateral A B C ->
 equilateral C B A.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap_2 :
 equilateral A B C ->
 equilateral A C B.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap_rot :
 equilateral A B C ->
 equilateral C A B.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Hint Resolve equilateral_swap equilateral_swap_2
 equilateral_swap_rot equilateral_rot equilateral_rot_2 : equilateral.

Lemma equilateral_isosceles_1 :
  equilateral A B C ->
  isosceles A B C.
Proof.
unfold equilateral, isosceles.
tauto.
Qed.

Lemma equilateral_isosceles_2 :
  equilateral A B C ->
  isosceles B C A.
Proof.
unfold equilateral, isosceles.
tauto.
Qed.

Lemma equilateral_isosceles_3 :
  equilateral A B C ->
  isosceles C A B.
Proof.
intros.
apply equilateral_cong in H.
unfold isosceles.
tauto.
Qed.

Hint Resolve equilateral_isosceles_1 equilateral_isosceles_2 equilateral_isosceles_3 : equilateral.

Lemma equilateral_strict_neq :
 equilateral_strict A B C ->
 A <> B /\ B <> C /\ A <> C.
Proof.
intros.
unfold equilateral_strict, equilateral in H.
decompose [and] H;clear H.
repeat split;Cong.
eauto using 与不同点等长之点不同.
eapply 与不同点等长之点不同.
assert (T:=等长的传递性 A B B C C A H2 H3).
apply H1.
assert (T:=等长的传递性 A B B C C A H2 H3).
Cong.
Qed.

Hint Resolve equilateral_strict_neq : equilateral.

Lemma equilateral_strict_swap_1 :
 equilateral_strict A B C ->
 equilateral_strict A C B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_2 :
 equilateral_strict A B C ->
 equilateral_strict B A C.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_3 :
 equilateral_strict A B C ->
 equilateral_strict B C A.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_4 :
 equilateral_strict A B C ->
 equilateral_strict C A B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_5 :
 equilateral_strict A B C ->
 equilateral_strict C B A.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Hint Resolve equilateral_strict_swap_1 equilateral_strict_swap_2
equilateral_strict_swap_3 equilateral_strict_swap_4 equilateral_strict_swap_5 : equilateral.

Lemma equilateral_strict__not_col : 
 equilateral_strict A B C -> ~ Col A B C.
Proof.
intros.
assert (T:=(equilateral_strict_neq H)).
unfold equilateral_strict in *.
unfold equilateral in *.
spliter.
intro.
assert (中点 B A C) by (apply (l7_20_bis B A C);finish).
assert (中点 C A B) by (apply (l7_20_bis C A B);finish).
apply midpoint_not_midpoint with C A B;auto.
Qed.

Lemma equilateral_strict_conga_1 :
 equilateral_strict A B C ->
 等角 C A B A C B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
apply equilateral_strict_equilateral in H.
apply equilateral_isosceles_1 in H.
apply isosceles_conga.
tauto.
tauto.
assumption.
Qed.

End ABC.

Lemma equilateral_strict_conga_2 :
 forall A B C,
 equilateral_strict A B C ->
 等角 B A C A B C.
Proof.
intros.
apply equilateral_strict_swap_1 in H.
apply equilateral_strict_conga_1 in H.
assumption.
Qed.

Lemma equilateral_strict_conga_3 :
 forall A B C,
 equilateral_strict A B C ->
 等角 C B A B C A.
Proof.
intros.
apply equilateral_strict_swap_2 in H.
apply equilateral_strict_conga_1 in H.
assumption.
Qed.

Lemma conga3_equilateral :
 forall A B C, 
 ~ Col A B C ->
 等角 B A C A B C ->
 等角 A B C B C A ->
 equilateral A B C.
Proof.
intros.
assert (isosceles B C A)
 by (apply conga_isosceles;等角;Col).
assert (isosceles C A B)
 by (apply conga_isosceles;等角;Col).
unfold isosceles in *.
unfold equilateral.
split;eCong.
Qed.



End Triangles.