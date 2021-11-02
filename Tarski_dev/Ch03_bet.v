Require Export GeoCoq.Tarski_dev.Ch02_cong.

Section T2_1.

Context `{Tn:无维度中性塔斯基公理系统}.

Lemma 中间性转共线 : forall A B C, Bet A B C -> Col A B C.
Proof.
    intros;unfold Col;auto.
Qed.

Lemma ABB中间性 : forall A B : Tpoint, Bet A B B.
Proof.
    intros.
    prolong A B x B B.
    assert (x = B) by (apply 等长的反向同一性 with B; Cong).
    subst;assumption.
Qed.

Lemma 中间性的对称性 : forall A B C : Tpoint, Bet A B C -> Bet C B A.
Proof.
    intros.
    assert (Bet B C C) by (apply ABB中间性).
    assert(exists x, Bet B x B /\ Bet C x A) by (apply 帕施公理 with C;auto).
    ex_and H1 x.
    apply 中间性的同一律 in H1; subst; assumption.
Qed.

(** This lemma is used by tactics for trying several permutations. *)
Lemma 中间性的各排列情况 :
 forall A B C,
 Bet A B C \/ Bet C B A ->
 Bet A B C.
Proof.
    intros.
    decompose [or] H; auto using 中间性的对称性.
Qed.

Lemma 中间性的等价排列 :
  forall A B C,
 Bet A B C ->
 Bet A B C /\ Bet C B A.
Proof.
    intros.
    auto using 中间性的对称性.
Qed.

Lemma AAB中间性 : forall A B : Tpoint, Bet A A B.
Proof.
    intros.
    apply 中间性的对称性.
    apply ABB中间性.
Qed.

Lemma between_equality : forall A B C : Tpoint, Bet A B C -> Bet B A C -> A = B.
Proof.
    intros.
    assert (exists x, Bet B x B /\ Bet A x A) by (apply (帕施公理 A B C);assumption).
    ex_and H1 x.
    apply 中间性的同一律 in H1.
    apply 中间性的同一律 in H2.
    congruence.
Qed.

Lemma between_equality_2 : forall A B C : Tpoint, Bet A B C -> Bet A C B -> B = C.
Proof.
    intros.
    apply between_equality with A; auto using 中间性的对称性.
Qed.

Lemma between_exchange3 : forall A B C D, Bet A B C -> Bet A C D -> Bet B C D.
Proof.
intros.
assert (exists x, Bet C x C /\ Bet B x D)
  by (apply 帕施公理 with A; apply 中间性的对称性; auto).
ex_and H1 x.
assert (C = x) by (apply 中间性的同一律; auto); subst; auto.
Qed.

Lemma bet_neq12__neq : forall A B C, Bet A B C -> A <> B -> A <> C.
Proof.
    intros A B C HBet HAB Heq.
    subst C; apply HAB, 中间性的同一律; trivial.
Qed.

Lemma bet_neq21__neq : forall A B C, Bet A B C -> B <> A -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq12__neq with B; auto.
Qed.

Lemma bet_neq23__neq : forall A B C, Bet A B C -> B <> C -> A <> C.
Proof.
    intros A B C HBet HBC Heq.
    subst C; apply HBC; symmetry.
    apply 中间性的同一律; trivial.
Qed.

Lemma bet_neq32__neq : forall A B C, Bet A B C -> C <> B -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq23__neq with B; auto.
Qed.

Lemma not_bet_distincts : forall A B C, ~ Bet A B C -> A <> B /\ B <> C.
Proof.
    intros A B C HNBet.
    repeat split; intro; subst B; apply HNBet.
      apply AAB中间性.
      apply ABB中间性.
Qed.

End T2_1.

(** Some tactics *)

Hint Resolve 中间性的对称性 : between.
Hint Resolve ABB中间性 AAB中间性 : between_no_eauto.

Ltac eBetween := eauto with between.
Ltac Between := auto with between between_no_eauto.

Ltac not_exist_hyp_perm_col A B C := not_exist_hyp (Col A B C); not_exist_hyp (Col A C B);
                                 not_exist_hyp (Col B A C); not_exist_hyp (Col B C A);
                                 not_exist_hyp (Col C A B); not_exist_hyp (Col C B A).

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;assert (Col X1 X2 X3) by (apply 中间性转共线;apply H)
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
end.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
end.

Ltac clean := clean_trivial_hyps;clean_reap_hyps.

Ltac smart_subst X := subst X;clean.

Ltac treat_equalities_aux :=
  repeat
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst X2
end.

Ltac treat_equalities :=
treat_equalities_aux;
repeat
  match goal with
   | H : Cong ?X3 ?X3 ?X1 ?X2 |- _ =>
      apply 等长的对称性 in H; apply 等长的同一性 in H;smart_subst X2
   | H : Cong ?X1 ?X2 ?X3 ?X3 |- _ =>
      apply 等长的同一性 in H;smart_subst X2
   | H : Bet ?X1 ?X2 ?X1 |- _ => apply 中间性的同一律 in H;smart_subst X2
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in assert (T : A=B) by (apply (between_equality A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?A ?C ?B |- _ =>
     let T := fresh in assert (T : B=C) by (apply (between_equality_2 A B C); Between);
                       smart_subst B
   | H : Bet ?A ?B ?C, H2 : Bet ?C ?A ?B |- _ =>
     let T := fresh in assert (T : A=B) by (apply (between_equality A B C); Between);
                       smart_subst A
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?C ?A |- _ =>
     let T := fresh in assert (T : B=C) by (apply (between_equality_2 A B C); Between);
                       smart_subst A
end.

Ltac show_distinct X Y := assert (X<>Y);[intro;treat_equalities|idtac].

Section T2_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma between_inner_transitivity : forall A B C D, Bet A B D -> Bet B C D -> Bet A B C.
Proof.
    intros.
    assert (exists x, Bet B x B /\ Bet C x A) by (apply 帕施公理 with D;auto).
    ex_and H1 x.
    treat_equalities.
    Between.
Qed.

Lemma outer_transitivity_between2 : forall A B C D, Bet A B C -> Bet B C D -> B<>C -> Bet A C D.
Proof.
    intros.
    prolong A C x C D.
    assert (x = D) by (apply (点的唯一构造 B C C D); try apply (between_exchange3 A B C x); Cong).
    subst x;assumption.
Qed.

End T2_2.

Hint Resolve outer_transitivity_between2 between_inner_transitivity between_exchange3 : between.

Section T2_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma between_exchange2 : forall A B C D, Bet A B D -> Bet B C D -> Bet A C D.
Proof.
    intros.
    induction (两点重合的决定性 B C);subst;eBetween.
Qed.

Lemma outer_transitivity_between : forall A B C D, Bet A B C -> Bet B C D -> B<>C -> Bet A B D.
Proof.
    intros.
    apply 中间性的对称性.
    apply (outer_transitivity_between2) with C; Between.
Qed.

Lemma between_exchange4 : forall A B C D, Bet A B C -> Bet A C D -> Bet A B D.
Proof.
    intros.
    apply 中间性的对称性.
    apply between_exchange2 with C; Between.
Qed.

End T2_3.

Hint Resolve between_exchange2 outer_transitivity_between between_exchange4 : between.

Section T2_4.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l3_9_4 : forall A1 A2 A3 A4, 四点中间性 A1 A2 A3 A4 -> 四点中间性 A4 A3 A2 A1.
Proof.
    unfold 四点中间性.
    intros;spliter; auto with between.
Qed.

Lemma l3_17 : forall A B C A' B' P,
  Bet A B C -> Bet A' B' C -> Bet A P A' -> exists Q, Bet P Q C /\ Bet B Q B'.
Proof.
    intros.
    assert (exists Q', Bet B' Q' A /\ Bet P Q' C) by (eapply 帕施公理;eBetween).
    ex_and H2 x.
    assert (exists y, Bet x y C /\ Bet B y B') by (eapply 帕施公理;eBetween).
    ex_and H4 y.
    exists y;eBetween.
Qed.

(** The prove the former version of lower dimension axiom for compatibility. *)

Lemma 防降维公理_ex : exists A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB.
exists PC.
apply 防降维公理.
Qed.

Lemma two_distinct_points : exists X, exists Y: Tpoint, X <> Y.
Proof.
    assert (ld:=防降维公理_ex).
    ex_elim ld A.
    ex_elim H B.
    ex_elim H0 C.
    exists A; exists B.
    intro; subst; apply H.
    right; right; apply ABB中间性.
Qed.

Lemma point_construction_different : forall A B, exists C, Bet A B C /\ B <> C.
Proof.
    intros.
    assert (tdp := two_distinct_points).
    ex_elim tdp x.
    ex_elim H y.
    prolong A B F x y.
    exists F.
    show_distinct B F.
      intuition.
    intuition.
Qed.

Lemma another_point : forall A: Tpoint, exists B, A <> B.
Proof.
    intros.
    assert (pcd := point_construction_different A A).
    ex_and pcd B.
    exists B;assumption.
Qed.

End T2_4.

Section Beeson_1.

(** Another proof of 两组连续三点分段等则全体等 without 两点重合的决定性 but using Cong stability
inspired by Micheal Beeson. #<a href="http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf"></a> # *)

Context `{Tn:无维度中性塔斯基公理系统}.

Variable Cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.

Lemma 两组连续三点分段等则全体等_b : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    apply Cong_stability; intro.
    assert (A<>B).
      intro; subst.
      assert (A'=B') by (apply (等长的同一性 A' B' B); Cong).
      subst; tauto.
    assert (Cong C A C' A') by (apply (五线段公理_等价SAS _ _ _ _ _ _ _ _ H1 );auto using 等长的平凡同一性, 等长的交换性).
    apply H3; Cong.
Qed.

Lemma cong_dec_eq_dec_b :
 (forall A B:Tpoint, ~ A <> B -> A = B).
Proof.
    intros A B HAB.
    apply 等长的同一性 with A.
    apply Cong_stability.
    intro HNCong.
    apply HAB.
    intro HEq.
    subst.
    apply HNCong.
    apply 等长的伪自反性.
Qed.

End Beeson_1.

Section Beeson_2.

Context `{Tn:无维度中性塔斯基公理系统}.

Variable Bet_stability : forall A B C, ~ ~ Bet A B C -> Bet A B C.

Lemma bet_dec_eq_dec_b :
 (forall A B:Tpoint, ~ A <> B -> A = B).
Proof.
    intros A B HAB.
    apply 中间性的同一律.
    apply Bet_stability.
    intro HNBet.
    apply HAB.
    intro HEq.
    subst.
    apply HNBet.
    apply ABB中间性.
Qed.

Lemma BetSEq : forall A B C, BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
intros; unfold BetS; split; intro; spliter;
repeat split; auto; intro; treat_equalities; auto.
Qed.

End Beeson_2.