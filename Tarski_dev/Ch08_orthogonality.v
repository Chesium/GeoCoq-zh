Require Export GeoCoq.Tarski_dev.Ch07_midpoint.
(*
We choose to use ColR as it is faster than CoincR.
*)
(*
Require Export GeoCoq.Tactics.Coinc.CoincR_for_col.
*)
Require Export GeoCoq.Tactics.Coinc.ColR.

Ltac not_exist_hyp_perm_ncol A B C := not_exist_hyp (~ Col A B C); not_exist_hyp (~ Col A C B);
                                 not_exist_hyp (~ Col B A C); not_exist_hyp (~ Col B C A);
                                 not_exist_hyp (~ Col C A B); not_exist_hyp (~ Col C B A).

Ltac assert_diffs_by_cases :=
 repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;induction (两点重合的决定性 A B);[treat_equalities;solve [finish|trivial] |idtac]
end.

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;assert (Col X1 X2 X3) by (apply 中间性蕴含共线1;apply H)

      | H:中点 ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := 中点蕴含共线 X2 X1 X3 H)

      | H:Out ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;let N := fresh in assert (N := out_col X1 X2 X3 H)
 end.

Ltac assert_bets :=
repeat
 match goal with
      | H:中点 ?B ?A ?C |- _ => let T := fresh in not_exist_hyp (Bet A B C); assert (T := midpoint_bet A B C H)
 end.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(中点 ?A ?B ?C), H2 : 中点 ?A ?C ?B |- _ => clear H2
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

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := 不共线则不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := 非中间性则任两点不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_AB不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BA不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BC不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_CB不等推AC不等 A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D H2 H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于推出不重合 A B C D H);clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B (不重合的对称性 B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B (不重合的对称性 A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B (不重合的对称性 B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
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
   | H:(中点 ?X1 ?X1 ?X1) |- _ => clear H
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
   treat_equalities; unfold 中点 in *; spliter; Cong; Cong_refl tpoint cong.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; assert_diffs; Col_refl tpoint col.

Ltac show_distinct X Y := assert (X<>Y);[intro;treat_equalities|idtac].

Ltac show_distinct'' X Y :=
 assert (X<>Y);
 [intro;treat_equalities; solve [finish]|idtac].

Ltac assert_all_diffs_by_contradiction :=
assert_diffs;repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;show_distinct'' A B
end.

Ltac search_contradiction :=
 match goal with
  | H: ~ ?P |- _ => exfalso;apply H;finish;ColR
 end.

Ltac show_distinct' X Y :=
 assert (X<>Y);
 [intro;treat_equalities; solve [search_contradiction]|idtac].

Ltac assert_all_diffs_by_contradiction' :=
repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => not_exist_hyp_comm A B;show_distinct' A B
end.
(*
Ltac update_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   update_cols_gen tpoint col.

Ltac deduce_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; deduce_cols_hide_gen tpoint col.

Ltac cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   cols_gen tpoint col.

Ltac tag_hyps :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   tag_hyps_gen tpoint col.

Ltac untag_hyps :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   untag_hyps_gen tpoint col.

Ltac clear_cols :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   clear_cols_gen tpoint col.

Ltac smart_subst' := update_cols;clean.

Ltac treat_equalities_aux' :=
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst'
end.

Ltac treat_equalities' :=
try treat_equalities_aux';
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply 等长的对称性 in H; apply 等长的同一性 in H; smart_subst'
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply 等长的同一性 in H; smart_subst'
   | H:(Bet ?X1 ?X2 ?X1) |- _ =>
      apply  中间性的同一律 in H; smart_subst'
   | H:(中点 ?X ?Y ?Y) |- _ => apply M是AA中点则M与A重合 in H; smart_subst'
   | H : Bet ?A ?B ?C, H2 : Bet ?B ?A ?C |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T : 双中间性推出点重合 A B C H H2); smart_subst'
   | H : 中点 ?P ?A ?P1, H2 : 中点 ?P ?A ?P2 |- _ =>
     let T := fresh in not_exist_hyp (P1=P2); assert (T : 中点组的唯一性1 A P P1 P2 H H2); smart_subst'
   | H : 中点 ?A ?P ?X, H2 : 中点 ?A ?Q ?X |- _ =>
     let T := fresh in not_exist_hyp (P=Q); assert (T : 中点组的唯一性2 P Q A X H H2); smart_subst'
   | H : 中点 ?M ?A ?A |- _ =>
     let T := fresh in not_exist_hyp (M=A); assert (T : M是AA中点则M与A重合 M A H); smart_subst'
   | H : 中点 ?A ?P ?P', H2 : 中点 ?B ?P ?P' |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := 中点的唯一性1 P P' A B H H2); smart_subst'
   | H : 中点 ?A ?B ?A |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := A是BA中点则A与B重合 A B H); smart_subst'
   | H : 中点 ?A ?A ?B |- _ =>
     let T := fresh in not_exist_hyp (A=B); assert (T := A是AB中点则A与B重合 A B H); smart_subst'
end.

Ltac search_contradiction' :=
 match goal with
  | H: ?A <> ?A |- _ => exfalso;apply H;reflexivity
  | H: ~ Col ?A ?B ?C |- _ => exfalso;apply H;cols
 end.

Ltac show_distinct'' X Y :=
 assert (X<>Y);
 [intro; treat_equalities'; (solve [search_contradiction'])|idtac].

Ltac show_not_col X Y Z :=
 assert (~ Col X Y Z);
 [intro; update_cols; (solve [search_contradiction'])|idtac].

Ltac assert_all_diffs_by_contradiction_aux :=
repeat match goal with
 | A: Tpoint, B: Tpoint |- _ => untag_hyps; not_exist_hyp_comm A B; tag_hyps; show_distinct'' A B
end.

Ltac assert_all_not_cols_by_contradiction_aux :=
repeat match goal with
 | A: Tpoint, B: Tpoint, C: Tpoint |- _ => untag_hyps; not_exist_hyp_perm_ncol A B C; tag_hyps; show_not_col A B C
end.

Ltac assert_all_diffs_by_contradiction' :=
  deduce_cols; assert_all_diffs_by_contradiction_aux; untag_hyps; clear_cols.

Ltac assert_all_not_cols_by_contradiction :=
  deduce_cols; assert_all_not_cols_by_contradiction_aux; untag_hyps; clear_cols.

Ltac assert_ndc_by_contradiction :=
  assert_all_diffs_by_contradiction'; assert_all_not_cols_by_contradiction.
*)
Section T8_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma per_dec : forall A B C, Per A B C \/ ~ Per A B C.
Proof.
    intros.
    unfold Per.
    elim (构造对称点 C B);intros C' HC'.
    elim (等长的决定性 A C A C');intro.
      left.
      exists C'.
      intuition.
    right.
    intro.
    decompose [ex and] H0;clear H0.
    assert (C'=x) by (apply 中点组的唯一性1 with C B;assumption).
    subst.
    intuition.
Qed.

Lemma l8_2 : forall A B C, Per A B C -> Per C B A.
Proof.
    unfold Per.
    intros.
    ex_and H C'.
    assert (exists A', 中点 B A A').
      apply 构造对称点.
    ex_and H1 A'.
    exists A'.
    split.
      assumption.
    eapply 等长的传递性.
      apply 等长的交换性.
      apply H0.
    eapply l7_13_同中点组两侧等长.
      apply H.
    apply M是AB中点则M是BA中点.
    assumption.
Qed.

End T8_1.

Hint Resolve l8_2 : perp.

Ltac Perp := auto with perp.

Section T8_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma Per_cases :
 forall A B C,
 Per A B C \/ Per C B A ->
 Per A B C.
Proof.
    intros.
    decompose [or]  H;Perp.
Qed.

Lemma Per_perm :
 forall A B C,
 Per A B C ->
 Per A B C /\ Per C B A.
Proof.
    intros.
    split; Perp.
Qed.

Lemma l8_3 : forall A B C A',
 Per A B C -> A<>B -> Col B A A' -> Per A' B C.
Proof.
    unfold Per.
    intros.
    ex_and H C'.
    exists C'.
    split.
      assumption.
    unfold 中点 in *;spliter.
    apply l4_17 with A B; Col; Cong.
Qed.

Lemma l8_4 : forall A B C C', Per A B C -> 中点 B C C' -> Per A B C'.
Proof.
    unfold Per.
    intros.
    ex_and H B'.
    exists C.
    split.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (B' = C') by (eapply 中点组的唯一性1;eauto).
    subst B'.
    Cong.
Qed.

Lemma l8_5 : forall A B, Per A B B.
Proof.
    unfold Per.
    intros.
    exists B.
    split.
      apply A是AA中点.
    Cong.
Qed.

Lemma l8_6 : forall A B C A', Per A B C -> Per A' B C -> Bet A C A' -> B=C.
Proof.
    unfold Per.
    intros.
    ex_and H C'.
    ex_and H0 C''.
    assert (C'=C'') by (eapply 中点组的唯一性1;eauto).
    subst C''.
    assert (C = C') by (eapply l4_19;eauto).
    subst C'.
    apply M是AA中点则M与A重合.
    assumption.
Qed.

End T8_2.

Hint Resolve l8_5 : perp.

Ltac let_symmetric C P A :=
let id1:=fresh in (assert (id1:(exists A', 中点 P A A'));
[apply 构造对称点|ex_and id1 C]).

Ltac symmetric B' A B :=
assert(sp:= 构造对称点 B A); ex_and sp B'.

Section T8_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l8_7 : forall A B C, Per A B C -> Per A C B -> B=C.
Proof.
    intros.
    unfold Per in H.
    ex_and H C'.
    symmetric A' C A.
    induction (两点重合的决定性 B C).
      assumption.
    assert (Per C' C A).
      eapply l8_3.
        eapply l8_2.
        apply H0.
        assumption.
      unfold 中点 in H.
      spliter.
      unfold Col.
      left.
      assumption.
    assert (Cong A C' A' C').
      unfold Per in H4.
      ex_and H4 Z.
      assert (A' = Z) by (eapply (中点组的唯一性1 A C A');auto).
      subst Z.
      Cong.
    unfold 中点 in *.
    spliter.
    assert (Cong A' C A' C').
      eapply 等长的传递性.
        apply 等长的对称性.
        apply 等长的交换性.
        apply H6.
      eapply 等长的传递性.
        apply 等长的交换性.
        apply H1.
      apply 等长的左交换性.
      assumption.
    assert (Per A' B C).
      unfold Per.
      exists C'.
      unfold 中点.
      repeat split;auto.
    eapply l8_6.
      apply H9.
      unfold Per.
      exists C'.
      split.
        unfold 中点;auto.
      apply H1.
    Between.
Qed.

Lemma l8_8 : forall A B, Per A B A -> A=B.
Proof.
    intros.
    apply l8_7 with A.
      apply l8_2.
      apply l8_5.
    assumption.
Qed.

Lemma per_distinct : forall A B C, Per A B C -> A <> B -> A <> C.
Proof.
    intros.
    intro.
    subst C.
    apply H0.
    apply (l8_8).
    assumption.
Qed.

Lemma per_distinct_1 : forall A B C, Per A B C -> B <> C -> A <> C.
Proof.
    intros.
    intro.
    subst C.
    apply H0.
    apply eq_sym.
    apply (l8_8).
    assumption.
Qed.

Lemma l8_9 : forall A B C, Per A B C -> Col A B C -> A=B \/ C=B.
Proof.
    intros.
    elim (两点重合的决定性 A B);intro.
      tauto.
    right.
    eapply l8_7.
      eapply l8_2.
      eapply l8_5.
    apply l8_3 with A; Col.
Qed.


Lemma l8_10 : forall A B C A' B' C',  Per A B C -> 三角形全等 A B C A' B' C' -> Per A' B' C'.
Proof.
    unfold Per.
    intros.
    ex_and H D.
    prolong C' B' D' B' C'.
    exists D'.
    split.
      unfold 中点.
      split.
        assumption.
      Cong.
    unfold 三角形全等, 中点 in *.
    spliter.
    induction (两点重合的决定性 C B).
      treat_equalities;Cong.
    assert(外五线段形式 C B D A C' B' D' A').
      unfold 外五线段形式.
      repeat split.
        assumption.
        assumption.
        Cong.
        eapply 等长的传递性.
          apply 等长的对称性.
          apply H4.
        eapply 等长的传递性.
          apply 等长的交换性.
          apply H6.
        Cong.
        Cong.
      Cong.
    assert (Cong D A D' A').
      eapply 五线段公理_等价SAS_with_def.
        apply H8.
      assumption.
    eapply 等长的传递性.
      apply 等长的对称性.
      apply H5.
    eapply 等长的传递性.
      apply H1.
    Cong.
Qed.

Lemma col_col_per_per : forall A X C U V,
 A<>X -> C<>X ->
 Col U A X ->
 Col V C X ->
 Per A X C ->
 Per U X V.
Proof.
    intros.
    assert (Per U X C) by (apply (l8_3 A X C U);Col).
    apply l8_2 in H4.
    apply l8_2 .
    apply (l8_3 C X U V);Col.
Qed.

Lemma perp_in_dec : forall X A B C D, 垂直于 X A B C D \/ ~ 垂直于 X A B C D.
Proof.
    intros.
    unfold 垂直于.
    elim (两点重合的决定性 A B);intro; elim (两点重合的决定性 C D);intro; elim (共线的决定性 X A B);intro; elim (共线的决定性 X C D);intro; try tauto.
    elim (两点重合的决定性 B X);intro; elim (两点重合的决定性 D X);intro;subst;treat_equalities.
      elim (per_dec A X C);intro.
        left;repeat split;Col;intros; apply col_col_per_per with A C;Col.
      right;intro;spliter;apply H3;apply H8;Col.
      elim (per_dec A X D);intro.
        left;repeat split;Col;intros; apply col_col_per_per with A D;ColR.
      right;intro;spliter;apply H3;apply H9;Col.
      elim (per_dec B X C);intro.
        left;repeat split;Col;intros; apply col_col_per_per with B C;ColR.
      right;intro;spliter;apply H4;apply H9;Col.
    elim (per_dec B X D);intro.
      left;repeat split;Col;intros; apply col_col_per_per with B D;ColR.
    right;intro;spliter;apply H5;apply H10;Col.
Qed.

Lemma perp_distinct : forall A B C D, Perp A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    unfold Perp in H.
    ex_elim H X.
    unfold 垂直于 in H0.
    tauto.
Qed.

Lemma l8_12 : forall A B C D X, 垂直于 X A B C D -> 垂直于 X C D A B.
Proof.
    unfold 垂直于.
    intros.
    spliter.
    repeat split;try assumption.
    intros;eapply l8_2;eauto.
Qed.

Lemma per_col : forall A B C D,
 B <> C -> Per A B C -> Col B C D -> Per A B D.
Proof.
    unfold Per.
    intros.
    ex_and H0 C'.
    prolong D B D' D B.
    exists D'.
    assert (中点 B C C').
      apply H0.
    induction H5.
    assert (中点 B D D') by (unfold 中点;split;Cong).
    assert (中点 B D D').
      apply H7.
    induction H8.
    repeat split.
      assumption.
      Cong.
    unfold Col in H1.
    induction H1.
      assert (Bet B C' D').
        eapply l7_15.
          eapply A是AA中点.
          apply H0.
          apply H7.
        assumption.
      assert (Cong C D C' D').
        eapply l4_3_1.
          apply H1.
          apply H10.
          Cong.
        Cong.
      assert(外五线段形式 B C D A B C' D' A) by (unfold 外五线段形式;repeat split;Cong).
      apply 等长的交换性.
      eauto using 五线段公理_等价SAS_with_def.
    induction H1.
      assert (Bet C' D' B).
        eapply l7_15.
          apply H0.
          apply H7.
          apply A是AA中点.
        assumption.
      assert (Cong C D C' D') by (eapply l4_3 with B B;Between;Cong).
      assert(内五线段形式 B D C A B D' C' A) by (unfold 内五线段形式;repeat split;Between;Cong).
      apply 等长的交换性.
      eauto using l4_2.
    assert (Bet D' B C').
      eapply l7_15.
        apply H7.
        eapply A是AA中点.
        apply H0.
      assumption.
    assert (Cong C D C' D') by (eapply 两组连续三点分段等则全体等 with B B;Between;Cong).
    assert(外五线段形式 C B D A C' B D' A) by (unfold 外五线段形式;repeat split;Between;Cong).
    apply 等长的交换性.
    eauto using 五线段公理_等价SAS_with_def.
Qed.

Lemma l8_13_2 : forall A B C D X,
   A <> B -> C <> D -> Col X A B -> Col X C D ->
  (exists U, exists V :Tpoint, Col U A B /\ Col V C D /\ U<>X /\ V<>X /\ Per U X V) ->
  垂直于 X A B C D.
Proof.
    intros.
    ex_and H3 U.
    ex_and H4 V.
    unfold 垂直于.
    repeat split;try assumption.
    intros.
    assert (Per V X U0).
      eapply l8_2.
      eapply l8_3.
        apply H7.
        assumption.
      eapply 共线的传递性4.
        apply H.
        Col.
        Col.
      Col.
    apply per_col with V.
      auto.
      apply l8_2.
      assumption.
    eapply 共线的传递性4.
      apply H0.
      Col.
      Col.
    Col.
Qed.

Lemma l8_14_1 : forall A B, ~ Perp A B A B.
Proof.
    intros.
    unfold Perp.
    intro.
    ex_and H X.
    unfold 垂直于 in H0.
    spliter.
    assert (Per A X A).
      apply H3.
        Col.
      Col.
    assert (A = X).
      apply (l8_7 A).
        apply l8_2.
        apply l8_5.
      assumption.
    assert (Per B X B) by (apply H3;Col).
    assert (B = X).
      apply l8_7 with B.
        apply l8_2.
        apply l8_5.
      assumption.
    apply H0.
    congruence.
Qed.

Lemma l8_14_2_1a : forall X A B C D, 垂直于 X A B C D -> Perp A B C D.
Proof.
    intros.
    unfold Perp.
    exists X.
    assumption.
Qed.

Lemma perp_in_distinct : forall X A B C D , 垂直于 X A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    apply l8_14_2_1a in H.
    apply perp_distinct.
    assumption.
Qed.

Lemma l8_14_2_1b : forall X A B C D Y, 垂直于 X A B C D -> Col Y A B -> Col Y C D -> X=Y.
Proof.
    intros.
    unfold 垂直于 in H.
    spliter.
    apply (H5 Y Y) in H1.
      apply eq_sym, l8_8; assumption.
    assumption.
Qed.

Lemma l8_14_2_1b_bis : forall A B C D X, Perp A B C D -> Col X A B -> Col X C D -> 垂直于 X A B C D.
Proof.
    intros.
    unfold Perp in H.
    ex_and H Y.
    assert (Y = X) by (eapply (l8_14_2_1b Y _ _ _ _ X) in H2;assumption).
    subst Y.
    assumption.
Qed.

Lemma l8_14_2_2 : forall X A B C D,
 Perp A B C D -> (forall Y, Col Y A B -> Col Y C D -> X=Y) ->  垂直于 X A B C D.
Proof.
    intros.
    eapply l8_14_2_1b_bis.
      assumption.
      unfold Perp in H.
      ex_and H Y.
      unfold 垂直于 in H1.
      spliter.
      assert (Col Y C D) by assumption.
      apply (H0 Y H2) in H3.
      subst Y.
      assumption.
    unfold Perp in H.
    ex_and H Y.
    unfold 垂直于 in H1.
    spliter.
    assert (Col Y C D).
      assumption.
    apply (H0 Y H2) in H3.
    subst Y.
    assumption.
Qed.

Lemma l8_14_3 : forall A B C D X Y, 垂直于 X A B C D -> 垂直于 Y A B C D -> X=Y.
Proof.
    intros.
    eapply l8_14_2_1b.
      apply H.
      unfold 垂直于 in H0.
      intuition.
    eapply l8_12 in H0.
    unfold 垂直于 in H0.
    intuition.
Qed.

Lemma l8_15_1 : forall A B C X, Col A B X -> Perp A B C X -> 垂直于 X A B C X.
Proof.
    intros.
    eapply l8_14_2_1b_bis;Col.
Qed.

Lemma l8_15_2 : forall A B C X, Col A B X ->  垂直于 X A B C X -> Perp A B C X.
Proof.
    intros.
    eapply l8_14_2_1a.
    apply H0.
Qed.

Lemma perp_in_per : forall A B C, 垂直于 B A B B C-> Per A B C.
Proof.
    intros.
    unfold 垂直于 in H.
    spliter.
    apply H3;Col.
Qed.

Lemma perp_sym : forall A B C D, Perp A B C D -> Perp C D A B.
Proof.
    unfold Perp.
    intros.
    ex_and H X.
    exists X.
    apply l8_12.
    assumption.
Qed.

Lemma perp_col0 : forall A B C D X Y, Perp A B C D -> X <> Y -> Col A B X -> Col A B Y -> Perp C D X Y.
Proof.
    unfold Perp.
    intros.
    ex_and H X0.
    exists X0.
    unfold 垂直于 in *.
    spliter.
    repeat split.
      assumption.
      assumption.
      assumption.
      eapply 共线的传递性4.
        apply H.
        Col.
        assumption.
      assumption.
    intros.
    apply l8_2.
    apply H6.
      assert(Col A X Y).
        eapply 共线的传递性4 with A B;Col.
      assert (Col B X Y).
        eapply 共线的传递性4 with A B;Col.
      eapply 共线的传递性4 with X Y;Col.
    assumption.
Qed.

Lemma per_perp_in : forall A B C, A <> B -> B <> C -> Per A B C -> 垂直于 B A B B C.
Proof.
    intros.
    unfold Perp.
    repeat split.
      assumption.
      assumption.
      Col.
      Col.
    intros.
    eapply per_col.
      apply H0.
      eapply l8_2.
      eapply per_col.
        intro.
        apply H.
        apply sym_equal.
        apply H4.
        apply l8_2.
        assumption.
      Col.
    Col.
Qed.

Lemma per_perp : forall A B C, A <> B -> B <> C -> Per A B C -> Perp A B B C.
Proof.
    intros.
    apply per_perp_in in H1.
      eapply l8_14_2_1a with B;assumption.
      assumption.
    assumption.
Qed.

Lemma perp_left_comm : forall A B C D, Perp A B C D -> Perp B A C D.
Proof.
    unfold Perp.
    intros.
    ex_and H X.
    exists X.
    unfold 垂直于 in *.
    intuition.
Qed.

Lemma perp_right_comm : forall A B C D, Perp A B C D -> Perp A B D C.
Proof.
    unfold Perp.
    intros.
    ex_and H X.
    exists X.
    unfold 垂直于 in *.
    intuition.
Qed.

Lemma perp_comm : forall A B C D, Perp A B C D -> Perp B A D C.
Proof.
    intros.
    apply perp_left_comm.
    apply perp_right_comm.
    assumption.
Qed.

Lemma perp_in_sym :
 forall A B C D X,
  垂直于 X A B C D -> 垂直于 X C D A B.
Proof.
    unfold 垂直于.
    intros.
    spliter.
    repeat split.
      assumption.
      assumption.
      assumption.
      assumption.
    intros.
    apply l8_2.
    apply H3;assumption.
Qed.

Lemma perp_in_left_comm :
 forall A B C D X,
  垂直于 X A B C D -> 垂直于 X B A C D.
Proof.
    unfold 垂直于.
    intuition.
Qed.

Lemma perp_in_right_comm : forall A B C D X, 垂直于 X A B C D -> 垂直于 X A B D C.
Proof.
    intros.
    apply perp_in_sym.
    apply perp_in_left_comm.
    apply perp_in_sym.
    assumption.
Qed.

Lemma perp_in_comm : forall A B C D X, 垂直于 X A B C D -> 垂直于 X B A D C.
Proof.
    intros.
    apply perp_in_left_comm.
    apply perp_in_right_comm.
    assumption.
Qed.

End T8_3.

Hint Resolve perp_sym perp_left_comm perp_right_comm perp_comm per_perp_in per_perp
             perp_in_per perp_in_left_comm perp_in_right_comm perp_in_comm perp_in_sym : perp.

Ltac double A B A' :=
   assert (mp:= 构造对称点 A B);
   elim mp; intros A' ; intro; clear mp.

Section T8_4.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma Perp_cases :
  forall A B C D,
  Perp A B C D \/ Perp B A C D \/ Perp A B D C \/ Perp B A D C \/
  Perp C D A B \/ Perp C D B A \/ Perp D C A B \/ Perp D C B A ->
  Perp A B C D.
Proof.
    intros.
    decompose [or] H; Perp.
Qed.

Lemma Perp_perm :
  forall A B C D,
  Perp A B C D ->
  Perp A B C D /\ Perp B A C D /\ Perp A B D C /\ Perp B A D C /\
  Perp C D A B /\ Perp C D B A /\ Perp D C A B /\ Perp D C B A.
Proof.
    intros.
    repeat split; Perp.
Qed.

Lemma Perp_in_cases :
  forall X A B C D,
  垂直于 X A B C D \/ 垂直于 X B A C D \/ 垂直于 X A B D C \/ 垂直于 X B A D C \/
  垂直于 X C D A B \/ 垂直于 X C D B A \/ 垂直于 X D C A B \/ 垂直于 X D C B A ->
  垂直于 X A B C D.
Proof.
    intros.
    decompose [or]  H; Perp.
Qed.

Lemma Perp_in_perm :
  forall X A B C D,
  垂直于 X A B C D ->
  垂直于 X A B C D /\ 垂直于 X B A C D /\ 垂直于 X A B D C /\ 垂直于 X B A D C /\
  垂直于 X C D A B /\ 垂直于 X C D B A /\ 垂直于 X D C A B /\ 垂直于 X D C B A.
Proof.
    intros.
    do 7 (split; Perp).
Qed.

Lemma perp_in_col : forall A B C D X, 垂直于 X A B C D -> Col A B X /\ Col C D X.
Proof.
    unfold 垂直于.
    intuition.
Qed.

Lemma perp_perp_in : forall A B C, Perp A B C A -> 垂直于 A A B C A.
Proof.
    intros.
    apply l8_15_1.
      unfold Perp in H.
      ex_and H X.
      unfold 垂直于 in H0.
      intuition.
    assumption.
Qed.

Lemma perp_per_1 : forall A B C, Perp A B C A -> Per B A C.
Proof.
    intros.
    assert (垂直于 A A B C A).
      apply perp_perp_in.
      assumption.
    unfold 垂直于 in H0.
    spliter.
    apply H4.
    Col.
    Col.
Qed.

Lemma perp_per_2 : forall A B C, Perp A B A C -> Per B A C.
Proof.
    intros.
    apply perp_right_comm in H.
    apply perp_per_1; assumption.
Qed.

Lemma perp_col : forall A B C D E, A<>E -> Perp A B C D -> Col A B E -> Perp A E C D.
Proof.
    intros.
    apply perp_sym.
    apply perp_col0 with A B; Col.
Qed.

Lemma perp_col2 : forall A B C D X Y,
  Perp A B X Y ->
  C <> D -> Col A B C -> Col A B D -> Perp C D X Y.
Proof.
    intros.
    assert(HH:=H).
    apply perp_distinct in HH.
    spliter.
    induction (两点重合的决定性 A C).
      subst A.
      apply perp_col with B; Col.
    assert(Perp A C X Y) by (eapply perp_col;eauto).
    apply perp_col with A; Perp.
    ColR.
Qed.

Lemma perp_col4 : forall A B C D P Q R S, P <> Q -> R <> S ->
  Col A B P -> Col A B Q -> Col C D R -> Col C D S -> Perp A B C D -> Perp P Q R S.
Proof.
    intros.
    apply (perp_col2 A B); auto.
    apply perp_sym, (perp_col2 C D); auto.
    apply perp_sym, H5.
Qed.

Lemma perp_not_eq_1 : forall A B C D, Perp A B C D -> A<>B.
Proof.
    intros.
    unfold Perp in H.
    ex_elim H X.
    unfold 垂直于 in H0.
    tauto.
Qed.

Lemma perp_not_eq_2 : forall A B C D, Perp A B C D -> C<>D.
Proof.
    intros.
    apply perp_sym in H.
    eapply perp_not_eq_1.
    apply H.
Qed.

Lemma diff_per_diff : forall A B P R ,
      A <> B -> Cong A P B R -> Per B A P -> Per A B R -> P <> R.
Proof.
    intros.
    intro.
    subst.
    assert (A = B).
      eapply l8_7.
        apply l8_2.
        apply H1.
      apply l8_2.
      assumption.
    intuition.
Qed.

Lemma per_not_colp : forall A B P R, A <> B -> A <> P -> B <> R -> Per B A P -> Per A B R -> ~Col P A R.
Proof.
    intros.
    intro.
    assert (Perp A B P A).
      apply perp_comm.
      apply per_perp; auto.
    assert (Perp A B B R).
      apply per_perp; auto.
    assert (Per B A R).
      eapply per_col.
        apply H0.
        assumption.
      ColR.
    apply l8_2 in H3.
    apply l8_2 in H7.
    assert (A = B).
      eapply l8_7.
        apply H7.
      assumption.
    contradiction.
Qed.

Lemma per_not_col : forall A B C, A <> B -> B <> C -> Per A B C -> ~Col A B C.
Proof.
    intros.
    intro.
    unfold Per in H1.
    ex_and H1 C'.
    assert (C = C' \/ 中点 A C C').
      apply 共线点间距相同要么重合要么中点.
        ColR.
        assumption.
    induction H4;treat_equalities; intuition.
Qed.

Lemma perp_not_col2 : forall A B C D, Perp A B C D -> ~ Col A B C \/ ~ Col A B D.
Proof.
    intros.
    induction (共线的决定性 A B C).
      right.
      assert(垂直于 C A B C D).
        apply l8_14_2_1b_bis; Col.
      intro.
      assert(垂直于 D A B C D).
        apply l8_14_2_1b_bis; Col.
      assert(C = D).
        eapply l8_14_3.
          apply H1.
        assumption.
      apply perp_not_eq_2 in H.
      contradiction.
    left.
    assumption.
Qed.

Lemma perp_not_col : forall A B P, Perp A B P A -> ~ Col A B P.
Proof.
    intros.
    assert (垂直于 A A B P A).
      apply perp_perp_in.
      assumption.
    assert (Per P A B).
      apply perp_in_per.
      apply perp_in_sym.
      assumption.
    apply perp_in_left_comm in H0.
    assert (~ Col B A P  -> ~ Col A B P).
      intro.
      intro.
      apply H2.
      apply 等价共线BAC.
      assumption.
    apply H2.
    apply perp_distinct in H.
    spliter.
    apply per_not_col.
      auto.
      auto.
    apply perp_in_per.
    apply perp_in_right_comm.
    assumption.
Qed.

Lemma perp_in_col_perp_in : forall A B C D E P, C <> E -> Col C D E -> 垂直于 P A B C D -> 垂直于 P A B C E.
Proof.
    intros.
    unfold 垂直于 in *.
    spliter.
    repeat split; auto.
      ColR.
    intros.
    apply H5.
      assumption.
    ColR.
Qed.

Lemma perp_col2_bis : forall A B C D P Q,
  Perp A B C D ->
  Col C D P ->
  Col C D Q ->
  P <> Q ->
  Perp A B P Q.
Proof.
intros A B C D P Q HPerp HCol1 HCol2 HCD.
apply perp_sym.
apply perp_col2 with C D; Perp.
Qed.

Lemma perp_in_perp_bis : forall A B C D X,
 垂直于 X A B C D -> Perp X B C D \/ Perp A X C D.
Proof.
    intros.
    induction (两点重合的决定性 X A).
      subst X.
      left.
      unfold Perp.
      exists A.
      assumption.
    right.
    unfold Perp.
    exists X.
    unfold 垂直于 in *.
    spliter.
    repeat split.
      intro.
      apply H0.
      subst X.
      reflexivity.
      assumption.
      apply ABA型共线.
      assumption.
    intros.
    apply H4.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        intro.
        apply H0.
        apply sym_equal.
        apply H7.
        Col.
      Col.
    assumption.
Qed.

Lemma col_per_perp : forall A B C D,
 A <> B -> B <> C -> D <> B -> D <> C ->
 Col B C D -> Per A B C -> Perp C D A B.
Proof.
    intros.
    apply per_perp_in in H4.
      apply perp_in_perp_bis in H4.
      induction H4.
        apply perp_distinct in H4.
        spliter.
        absurde.
      eapply (perp_col _ B).
        auto.
        apply perp_sym.
        apply perp_right_comm.
        assumption.
      apply 等价共线BAC.
      assumption.
      assumption.
    assumption.
Qed.

Lemma per_cong_mid : forall A B C H,
 B <> C -> Bet A B C -> Cong A H C H -> Per H B C ->
 中点 B A C.
Proof.
    intros.
    induction (两点重合的决定性 H B).
      subst H.
      unfold 中点.
      split.
        assumption.
      apply 等长的右交换性.
      assumption.
    assert(Per C B H).
      apply l8_2.
      assumption.
    assert (Per H B A).
      eapply per_col.
        apply H0.
        assumption.
      unfold Col.
      right; right.
      assumption.
    assert (Per A B H).
      apply l8_2.
      assumption.
    unfold Per in *.
    ex_and H3 C'.
    ex_and H5 H'.
    ex_and H6 A'.
    ex_and H7 H''.
    assert (H' = H'').
      eapply (点的唯一构造 H B H B).
        assumption.
        apply midpoint_bet.
        assumption.
        apply 等长的交换性.
        apply 中点蕴含等长.
        apply M是AB中点则M是BA中点.
        apply H5.
        apply midpoint_bet.
        assumption.
      apply 等长的交换性.
      apply 中点蕴含等长.
      apply M是AB中点则M是BA中点.
      assumption.
    subst H''.
    assert(内五线段形式 H B H' A H B H' C).
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        assumption.
        apply 等长的自反性.
        apply 等长的自反性.
        apply 等长的交换性.
        assumption.
      apply 等长的交换性.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H11.
      eapply 等长的传递性.
        apply H2.
      assumption.
    eapply l4_2 in H12.
    unfold 中点.
    split.
      assumption.
    apply 等长的左交换性.
    assumption.
Qed.

Lemma per_double_cong : forall A B C C',
 Per A B C -> 中点 B C C' -> Cong A C A C'.
Proof.
    intros.
    unfold Per in H.
    ex_and H C''.
    assert (C' = C'').
      eapply 中点组的唯一性2.
        apply M是AB中点则M是BA中点.
        apply H0.
      apply M是AB中点则M是BA中点.
      assumption.
    subst C''.
    assumption.
Qed.

Lemma cong_perp_or_mid : forall A B M X, A <> B -> 中点 M A B -> Cong A X B X ->
 X = M \/ ~Col A B X /\ 垂直于 M X M A B.
Proof.
intros.
induction(共线的决定性 A B X).
left.
assert(A = B \/ 中点 X A B).
apply 共线点间距相同要么重合要么中点; Col.
Cong.
induction H3.
contradiction.
apply (中点的唯一性1 A B); auto.
right.
split; auto.
assert(Col M A B).
unfold 中点 in *.
spliter; Col.

assert_diffs.
assert(Per X M A)
 by (unfold Per;exists B;split; Cong).
apply per_perp_in in H4.
apply perp_in_right_comm in H4.
apply(perp_in_col_perp_in X M A M B M); Col.

intro;treat_equalities.
apply H2; Col.
auto.
Qed.

Lemma col_per2_cases : forall A B C D B', 
 B <> C -> B' <> C -> C <> D -> Col B C D -> Per A B C -> Per A B' C -> 
 B = B' \/ ~Col B' C D.
Proof.
intros.
induction(两点重合的决定性 B B').
left; auto.
right.
intro.
assert(Col C B B').
ColR.
assert(Per A B' B).
apply(per_col A B' C B H0 H4); Col.
assert(Per A B B').
apply(per_col A B C B' H H3); Col.
apply H5.
apply (l8_7 A); auto.
Qed.

Lemma l8_16_1 : forall A B C U X,
  Col A B X -> Col A B U -> Perp A B C X -> ~ Col A B C /\ Per C X U.
Proof.
      intros.
      destruct (两点重合的决定性 U X).
        subst X.
        split.
          destruct (perp_not_col2 A B C U); auto.
        apply l8_5.
      split.
        intro.
        assert (垂直于 X A B C X).
          eapply l8_15_1.
            assumption.
          assumption.
        assert (X = U).
          eapply l8_14_2_1b.
            apply H4.
            Col.
          eapply 共线的传递性4 with A B;Col.
          apply perp_distinct in H1; spliter; auto.
        intuition.
      apply l8_14_2_1b_bis with C X U X; Col.
      assert (Col A X U).
        eapply (共线的传递性4 A B);Col.
        apply perp_distinct in H1; spliter; auto.
      eapply perp_col0 with A B;Col.
Qed.

Lemma l8_16_2 : forall A B C U X,
  Col A B X -> Col A B U -> U<>X -> ~ Col A B C -> Per C X U -> Perp A B C X.
Proof.
    intros.
    assert (C <> X).
      intro.
      subst X.
      apply H2.
      assumption.
    unfold Perp.
    exists X.
    eapply l8_13_2.
      assert_diffs; auto.
      assumption.
      Col.
      Col.
    exists U.
    exists C.
    repeat split; Col.
    apply l8_2.
    assumption.
Qed.

Lemma l8_18_uniqueness : forall A B C X Y,
  ~ Col A B C -> Col A B X -> Perp A B C X -> Col A B Y -> Perp A B C Y -> X=Y.
Proof.
    intros.
    show_distinct A B.
      solve [intuition].
    assert (垂直于 X A B C X) by (eapply l8_15_1;assumption).
    assert (垂直于 Y A B C Y) by (eapply l8_15_1;assumption).
    unfold 垂直于 in *.
    spliter.
    apply l8_7 with C;apply l8_2;[apply H14 |apply H10];Col.
Qed.

Lemma midpoint_distinct : forall A B X C C', ~ Col A B C -> Col A B X -> 中点 X C C' -> C <> C'.
Proof.
    intros.
    intro.
    subst C'.
    apply H.
    unfold 中点 in H1.
    spliter.
    treat_equalities.
    assumption.
Qed.

Lemma l8_20_1 : forall A B C C' D P,
  Per A B C -> 中点 P C' D -> 中点 A C' C -> 中点 B D C -> Per B A P.
Proof.
    intros.
    double B A B'.
    double D A D'.
    double P A P'.
    induction (两点重合的决定性 A B).
      subst B.
      unfold 中点 in H5.
      spliter.
      eapply l8_2.
      eapply l8_5.
    assert (Per B' B C).
      eapply l8_3.
        apply H.
        assumption.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    assert (Per B B' C').
      eapply l8_10.
        apply H7.
      unfold 三角形全等.
      repeat split.
        apply 等长的伪自反性.
        eapply l7_13_同中点组两侧等长.
          unfold 中点.
          split.
            apply H3.
          apply 中点蕴含等长.
          assumption.
        assumption.
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H3.
      assumption.
    assert(中点 B' D' C').
      eapply 对称保持中点.
        apply H4.
        apply H3.
        apply M是AB中点则M是BA中点.
        apply H1.
      assumption.
    assert(中点 P' C D').
      eapply 对称保持中点.
        apply H1.
        apply H5.
        apply H4.
      assumption.
    unfold Per.
    exists P'.
    split.
      assumption.
    unfold Per in H7.
    ex_and H7 D''.
    assert (D''= D).
      eapply 中点组的唯一性1.
        apply H7.
      apply M是AB中点则M是BA中点.
      assumption.
    subst D''.
    unfold Per in H8.
    ex_and H8 D''.
    assert (D' = D'').
      eapply 中点组的唯一性1.
        apply M是AB中点则M是BA中点.
        apply H9.
      assumption.
    subst D''.
    assert (中点 P C' D).
      eapply 对称保持中点.
        apply M是AB中点则M是BA中点.
        apply H1.
        apply M是AB中点则M是BA中点.
        apply H5.
        apply M是AB中点则M是BA中点.
        apply H4.
      assumption.
    assert (Cong C D C' D').
      eapply l7_13_同中点组两侧等长.
        apply H1.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (Cong C' D C D').
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H1.
      apply M是AB中点则M是BA中点.
      assumption.
    assert(Cong P D P' D').
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H5.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (Cong P D P' C).
      eapply 等长的传递性.
        apply H16.
      unfold 中点 in H10.
      spliter.
      apply 等长的右交换性.
      apply 等长的对称性.
      assumption.
    assert (内五线段形式 C' P D B D' P' C B).
      unfold 内五线段形式.
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
        apply 等长的右交换性.
        assumption.
        assumption.
        apply 等长的交换性.
        assumption.
      apply 等长的右交换性.
      apply 中点蕴含等长.
      assumption.
    assert (Cong P B P' B).
      eapply l4_2.
      apply H18.
    apply 等长的交换性.
    assumption.
Qed.

Lemma l8_20_2 : forall A B C C' D P,
  Per A B C -> 中点 P C' D -> 中点 A C' C -> 中点 B D C -> B<>C -> A<>P.
Proof.
    intros.
    intro.
    subst P.
    assert (C = D).
      eapply 中点组的唯一性1.
        apply H1.
      assumption.
    subst D.
    assert (B = C).
      apply M是AA中点则M与A重合.
      assumption.
    subst C.
    absurde.
Qed.

Lemma perp_col1 : forall A B C D X,
 C <> X -> Perp A B C D -> Col C D X -> Perp A B C X.
Proof.
    intros.
    assert (T:=perp_distinct A B C D H0).
    spliter.
    unfold Perp in *.
    ex_and H0 P.
    exists P.
    unfold 垂直于 in *.
    spliter.
    repeat split.
      assumption.
      assumption.
      assumption.
      apply 等价共线CAB.
      eapply 共线的传递性3.
        intro.
        apply H3.
        apply sym_equal.
        apply H8.
        apply 等价共线BAC.
        assumption.
      apply 等价共线CBA.
      assumption.
    intros.
    apply H7.
      assumption.
    apply 等价共线CAB.
    eapply 共线的传递性2.
      apply H.
      apply 等价共线ACB.
      assumption.
    apply 等价共线BCA.
    assumption.
Qed.




Lemma l8_18_existence : forall A B C, ~ Col A B C -> exists X, Col A B X /\ Perp A B C X.
Proof.
    intros.
    prolong B A Y A C.
    assert (exists P, 中点 P C Y) by (apply 一点与两点等距则该两点存在中点 with A;Cong).
    ex_and H2 P.
    assert (Per A P Y) by (unfold Per;exists C;auto using M是AB中点则M是BA中点).
    prolong A Y Z Y P.
    prolong P Y Q Y A.
    prolong Q Z Q' Q Z.
    assert (中点 Z Q Q') by (unfold 中点;split;Cong).
    prolong Q' Y C' Y C.
    assert (exists X, 中点 X C C') by (apply 一点与两点等距则该两点存在中点 with Y;Cong).
    ex_and H13 X.
    assert (外五线段形式 A Y Z Q Q Y P A) by (unfold 外五线段形式;repeat split;Between;Cong).
    show_distinct A Y.
      intuition.
    assert (Cong Z Q P A) by (eauto using 五线段公理_等价SAS_with_def).
    assert (三角形全等 A P Y Q Z Y) by (unfold 三角形全等;repeat split;Cong).
    assert (Per Q Z Y) by (eauto using l8_10).
    assert (Per Y Z Q) by eauto using l8_2.
    (* diversion *)
    show_distinct P Y.
      apply H; Col.
    unfold Per in H19.
    ex_and H19 Q''.
    assert (Q' = Q'').
      eapply 中点组的唯一性1.
        apply H10.
      assumption.
    subst Q''.
    assert (hy:Bet Z Y X).
      apply (M是AB中点则M是BA中点2 Q C Q' C' Y Z X);Cong.
      assert (T:=中间性的外传递性1 C P Y Q).
      assert_bets.
      apply 中间性的对称性.
      apply T;Between.
    show_distinct Q Y.
      intuition.
    assert (Per Y X C) by (unfold Per;exists C';split;Cong).
    assert_diffs.
    assert (Col P Y Q).
      unfold Col.
      left.
      assumption.
    assert(Col P Y C).
      unfold 中点 in H3.
      spliter.
      unfold Col.
      right; right.
      assumption.
    assert (Col P Q C) by ColR.
    assert (Col Y Q C) by ColR.
    assert (Col A Y B) by Col.
    assert (Col A Y Z) by Col.
    assert (Col A B Z) by ColR.
    assert (Col Y B Z) by ColR.
    assert (Col Q Y P) by Col.
    assert(Q <> C).
      intro.
      subst Q.
      unfold 中点 in *.
      spliter.
      apply H.
      assert (Bet B Y Z) by (apply 中间性的外传递性1 with A;auto).
      apply 中间性的对称性 in H3.
      assert (Y = P).
        eapply 双中间性推出点重合.
          apply H3.
        assumption.
      treat_equalities.
      intuition.
    assert (Col Y B Z) by ColR.
    show_distinct Y Q'. intuition.
    assert (Col Y Q' C') by Col.
    assert (Q <> Q').
      intro.
      unfold 外五线段形式, 三角形全等 in *.
      spliter.
      treat_equalities.
      apply H.
      ColR.
    assert (C <> C').
      intro.
      subst C'.
      apply M是AA中点则M与A重合 in H14.
      subst X.
      assert (Col Z Q Q') by ColR.
      assert (Y <> Z).
        intro.
        subst Z.
        unfold 外五线段形式, 三角形全等, 中点 in *.
        spliter.
        treat_equalities.
        intuition.
      apply H.
      ColR.
    (* end of C<>C' *)
    assert(外五线段形式 Q Y C Z Q' Y C' Z).
      unfold 外五线段形式.
      repeat split;Between;Cong.
      unfold 外五线段形式, 中点 in *.
      spliter.
      eapply 中间性的外传递性2 with P;Between;Cong.
    assert (Cong C Z C' Z) by (eauto using 五线段公理_等价SAS_with_def).
    assert (Col Z Y X) by Col.
    show_distinct Y Z. intuition.
    assert(C <> X).
      intro.
      subst X.
      unfold 外五线段形式,三角形全等,中点 in *.
      spliter.
      treat_equalities.
      intuition.
    assert(X <> Y).
      intro.
      subst X.
      unfold 外五线段形式,三角形全等,中点 in *.
      spliter.
      clean_duplicated_hyps.
      clean_trivial_hyps.
      show_distinct C' Y.
        intuition.
      assert (Col Y C' P ).
        eapply 共线的传递性2 with C.
          intuition.
          unfold Col.
          right;right.
          apply 中间性的对称性.
          assumption.
        apply 等价共线BCA.
        assumption.
      show_distinct P Q.
        intuition.
      assert (Col Y P Q') by ColR.
      assert (Col Y Q Q') by ColR.
      assert (Col Q Y Z) by ColR.
      assert (Col Y Z C) by ColR.
      apply H.
      ColR.
    assert (垂直于 X Y Z C X).
      eapply l8_13_2;Col.
      exists Y.
      exists C.
      repeat split;Col.
    assert (Col A B X) by ColR.
    exists X.
    split.
      assumption.
    unfold Perp.
    exists X.
    unfold 垂直于.
    repeat split;Col.
    intros.
    unfold 垂直于 in H52.
    spliter.
    apply H57;ColR.
Qed.


Lemma l8_21_aux : forall A B C,
 ~ Col A B C -> exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    assert (exists X : Tpoint, Col A B X /\ Perp A B C X).
      eapply l8_18_existence.
      assumption.
    ex_and H0 X.
    assert (垂直于 X A B C X).
      eapply l8_15_1; assert_diffs; auto.
    assert (Per A X C).
      unfold 垂直于 in H2.
      spliter.
      apply H6.
        apply AAB型共线.
      apply AAB型共线.
    assert(HH:= H3).
    unfold Per in H3.
    ex_and H3 C'.
    double C A C''.
    assert (exists P, 中点 P C' C'').
      eapply 一点与两点等距则该两点存在中点.
      unfold 中点 in *.
      spliter.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H4.
      apply 等长的左交换性.
      assumption; spliter.
    ex_elim H6 P.
    assert (Per X A P).
      eapply l8_20_1.
        apply HH.
        apply M是AB中点则M是BA中点.
        apply H7.
        apply M是AB中点则M是BA中点.
        apply H5.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (X <> C).
      intro.
      subst C.
      apply H.
      assumption.
    assert (A <> P).
      eapply l8_20_2.
        apply HH.
        apply M是AB中点则M是BA中点.
        apply H7.
        apply M是AB中点则M是BA中点.
        assumption.
        apply M是AB中点则M是BA中点.
        assumption.
      assumption.
    assert (exists T, Bet P T C /\ Bet A T X).
      eapply l3_17_三中间性推交点存在性.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        apply H5.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        apply H3.
      apply midpoint_bet.
      apply M是AB中点则M是BA中点.
      apply H7.
    ex_and H10 T.
    induction (两点重合的决定性 A X).
      subst X.
      exists P.
      exists T.
      apply 中间性的同一律 in H11.
      subst T.
      assert (C'= C'').
        eapply 中点组的唯一性1.
          apply H3.
        assumption.
      subst C''.
      apply M是AA中点则M与A重合 in H7.
      subst P.
      assert (Col A C C') by ColR.
      repeat split;Col;Between.
      apply perp_col0 with C A;auto using perp_sym;Col.
    exists P.
    exists T.
    repeat split.
      unfold Perp.
      exists A.
      unfold 垂直于.
      repeat split.
        assert_diffs; auto.
        auto.
        apply AAB型共线.
        apply ABA型共线.
      unfold 垂直于 in H2.
      spliter.
      intros.
      eapply per_col in H6.
        apply l8_2 in H6.
        eapply per_col in H6.
          eapply l8_2 in H6.
          apply H6.
          assumption.
        ColR.
        assumption.
      ColR.
      ColR.
    Between.
Qed.

Lemma l8_21 : forall A B C,
 A <> B -> exists P, exists T, Perp A B P A /\ Col A B T /\ Bet C T P.
Proof.
    intros.
    induction(共线的决定性 A B C).
      assert (exists C', ~ Col A B C').
        eapply 两点不重合则存在不共线的点.
        assumption.
      ex_elim H1 C'.
      assert ( exists P : Tpoint, (exists T : Tpoint, Perp A B P A /\ Col A B T /\ Bet C' T P)).
        eapply l8_21_aux.
        assumption.
      ex_elim H1 P.
      ex_and H3 T.
      exists P.
      exists C.
      repeat split.
        assumption.
        assumption.
      apply AAB中间性.
    eapply l8_21_aux.
    assumption.
Qed.

Lemma per_cong : forall A B P R X ,
 A <> B -> A <> P ->
 Per B A P -> Per A B R ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B.
Proof.
    intros.
    assert (Per P A B).
      apply l8_2.
      assumption.
    double B R Q.
    assert (B <> R).
      intro.
      subst R.
      apply 等长的同一性 in H3.
      subst P.
      absurde.
    assert (Per A B Q).
      eapply per_col.
        apply H8.
        assumption.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    assert (Per P A X).
      eapply per_col.
        apply H.
        assumption.
      assumption.
    assert (B <> Q).
      intro.
      subst Q.
      apply M是AA中点则M与A重合 in H7.
      subst R.
      absurde.
    assert (Per R B X).
      eapply per_col.
        intro.
        apply H.
        apply sym_equal.
        apply H12.
        apply l8_2.
        assumption.
      apply 等价共线BAC.
      assumption.
    assert (X <> A).
      intro.
      subst X.
      assert (~Col P A R).
        eapply per_not_colp.
          apply H.
          assumption.
          assumption.
          assumption.
        assumption.
      apply H13.
      unfold Col.
      left.
      assumption.
    double P A P'.
    prolong P' X R' X R.
    assert (exists M, 中点 M R R').
      eapply 一点与两点等距则该两点存在中点.
      apply 等长的对称性.
      apply H16.
    ex_elim H17 M.
    assert (Per X M R).
      unfold Per.
      exists R'.
      split.
        assumption.
      apply 等长的对称性.
      assumption.
    assert (Cong X P X P').
      apply l8_2 in H10.
      unfold Per in H10.
      ex_and H10 P''.
      assert (P'=P'').
        eapply 中点组的唯一性1.
          apply H14.
        apply H10.
      subst P''.
      assumption.
    assert (X <> P').
      intro.
      subst P'.
      apply 等长的同一性 in H19.
      subst X.
      apply M是AA中点则M与A重合 in H14.
      subst P.
      absurde.
    assert (P <> P').
      intro.
      subst P'.
      eapply M是AA中点则M与A重合 in H14.
      subst P.
      absurde.
    assert(~Col X P P').
      intro.
      assert(Col X P A).
        eapply 共线的传递性4.
          apply H21.
          apply 等价共线BCA.
          assumption.
          apply ABA型共线.
        unfold Col.
        right;left.
        apply 中间性的对称性.
        apply midpoint_bet.
        assumption.
      apply 等价共线BCA in H23.
      assert (P = A \/ X = A).
        eapply l8_9.
          assumption.
        assumption.
      induction H24.
        subst P.
        absurde.
      apply H13.
      assumption.
    assert (Bet A X M).
      apply (M是AB中点则M是BA中点2 P R P' R'); trivial.
      apply 等长的对称性.
      assumption.
    assert (X <> R).
      intro.
      treat_equalities.
      apply l8_8 in H12.
      treat_equalities.
      unfold 中点 in *.
      spliter.
      treat_equalities.
      intuition.
    assert (X <> R').
      intro.
      subst R'.
      apply 等长的对称性 in H16.
      apply 等长的同一性 in H16.
      apply H24.
      assumption.
    assert (M <> X).
      intro.
      subst M.
      apply H22.
      eapply 共线的传递性2.
        apply H24.
        unfold Col.
        right; right.
        assumption.
      eapply 共线的传递性2.
        apply H25.
        unfold Col.
        right;right.
        apply midpoint_bet.
        assumption.
      unfold Col.
      right; right.
      assumption.
    assert (M = B).
      eapply (l8_18_uniqueness A X R).
        intro.
        assert (Col A B R).
          eapply 共线的传递性2.
            intro.
            apply H13.
            apply sym_equal.
            apply H28.
            apply 等价共线ACB.
            assumption.
          assumption.
        eapply per_not_col.
          apply H; apply H12.
          apply H8.
          assumption.
        assumption.
        unfold Col.
        left.
        assumption; eapply 共线的传递性2.
        apply per_perp in H17.
          apply perp_comm.
          eapply perp_col.
            assumption.
            apply H17.
          unfold Col.
          right;right.
          assumption.
          auto.
        intro.
        subst M.
        apply (中点组的唯一性1 R R R R')  in H18.
          subst R'.
          apply H22.
          eapply 共线的传递性2.
            apply H25.
            unfold Col.
            right;right.
            assumption.
          unfold Col.
          right; right.
          assumption.
        eapply A是AA中点.
        apply 等价共线ACB.
        assumption.
      apply per_perp in H10.
        apply perp_comm.
        eapply perp_col.
          apply H13.
          apply perp_comm.
          eapply perp_col.
            intro.
            apply H13.
            apply sym_equal.
            apply H27.
            apply perp_right_comm.
            apply per_perp in H2.
              apply H2.
              assumption.
            assumption.
          assumption.
        apply ABB型共线.
        auto.
      intro.
      apply H13.
      subst X.
      reflexivity.
    subst M.
    assert(外五线段形式 P X R P' P' X R' P).
      unfold 外五线段形式.
      repeat split.
        assumption.
        assumption.
        apply 等长的交换性.
        assumption.
        apply 等长的对称性.
        assumption.
        apply 等长的伪自反性.
      apply 等长的对称性.
      assumption.
    assert (Cong R P' R' P).
      eapply 五线段公理_等价SAS_with_def.
        apply H27.
      intro.
      subst X.
      apply H22.
      apply AAB型共线.
    assert (内五线段形式 P' A P R R' B R P).
      unfold 内五线段形式.
      repeat split.
        apply 中间性的对称性.
        apply midpoint_bet.
        assumption.
        apply 中间性的对称性.
        apply midpoint_bet.
        assumption.
        eapply 两组连续三点分段等则全体等.
          apply 中间性的对称性.
          apply midpoint_bet.
          apply H14.
          apply 中间性的对称性.
          apply midpoint_bet.
          apply H18.
          eapply 等长的传递性.
            apply 中点蕴含等长.
            apply M是AB中点则M是BA中点.
            apply H14.
          eapply 等长的传递性.
            apply H3.
          apply 等长的交换性.
          apply 中点蕴含等长.
          assumption.
        assumption.
        assumption.
        Cong.
      apply 等长的伪自反性.
    eapply 等长的右交换性.
    eapply l4_2.
    eapply H29.
Qed.


Lemma perp_cong : forall A B P R X,
 A <> B -> A <> P ->
 Perp A B P A -> Perp A B R B ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B.
Proof.
    intros.
    apply (per_cong A B P R X).
      assumption.
      assumption.
      apply perp_per_1.
      assumption.
      eapply perp_per_1.
        auto.
      apply perp_left_comm;auto.
      assumption.
      assumption.
    assumption.
Qed.

Lemma perp_exists : forall O A B, A <> B -> exists X, Perp O X A B.
Proof.
    intros.
    induction(共线的决定性 A B O).
      destruct (每组共线三点都有另一共线点 A B O H0) as [C].
      spliter.
      destruct (l8_21 O C O H3) as [P [T]].
      spliter.
      exists P.
      apply perp_comm.
      apply perp_sym.
      apply (perp_col2 O C); ColR.
    destruct (l8_18_existence A B O H0) as [X []].
    exists X.
    apply perp_sym.
    apply H2.
Qed.

Lemma perp_vector : forall A B, A <> B -> (exists X, exists Y, Perp A B X Y).
Proof.
    intros.
    exists A.
    destruct (perp_exists A A B) as [Y]; auto.
    exists Y; Perp.
Qed.

Lemma midpoint_existence_aux : forall A B P Q T,
  A<>B -> Perp A B Q B -> Perp A B P A ->
  Col A B T -> Bet Q T P -> Le A P B Q ->
  exists X : Tpoint, 中点 X A B.
Proof.
    intros.
    unfold Le in H4.
    ex_and H4 R.
    assert (exists X, Bet T X B /\ Bet R X P).
      eapply 帕施公理.
        apply 中间性的对称性.
        apply H3.
      auto.
    ex_and H6 X.
    assert (Col A B X).
      induction (两点重合的决定性 T B).
        subst T.
        apply 中间性的同一律 in H6.
        subst X.
        Col.
     ColR.
     induction(共线的决定性 A B P).
      assert (B=A \/ P=A).
        eapply l8_9.
          apply perp_per_1.
          assumption.
        apply 等价共线BAC.
        assumption.
      induction H10.
        exists A.
        subst B.
        eapply A是AA中点.
      treat_equalities.
      apply perp_distinct in H1.
      spliter.
      absurde.
    assert (B <> R).
      intro.
      subst R.
      treat_equalities.
      apply H9.
      apply ABA型共线.
    assert (~Col A B Q).
      intro.
      assert (A=B \/ Q=B).
        eapply l8_9.
          apply perp_per_2.
            auto.
          apply perp_comm.
          assumption.
        assumption.
      induction H12.
        apply H.
        assumption.
      subst Q.
      treat_equalities.
      absurde.
    assert (~Col A B R).
      intro.
      assert (Col B A Q).
        ColR.
      Col.
    show_distinct P R.
      intuition.
    induction (两点重合的决定性 A P).
      subst P.
      apply perp_distinct in H1.
      spliter.
      absurde.
    assert (Perp A B R B).
      eapply perp_col.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col.
          assumption.
          apply perp_left_comm.
          apply perp_sym.
          apply H0.
        Col.
      Col.
    apply 中间性的对称性 in H7.
    assert (Cong A R P B).
      apply (perp_cong A B P R X); assumption.
    assert (中点 X A B /\ 中点 X P R).
      apply (四点对边等长则对角线交点平分对角线 A P B R X); Col; Cong.
    spliter. exists X.
    assumption.
Qed.

(** This following result is very important, it shows the existence of a midpoint.
 The proof is involved because we are not using continuity axioms.
*)

(** This corresponds to l8_22 in Tarski's book. *)

Lemma midpoint_existence : forall A B, exists X, 中点 X A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst B.
      exists A.
      apply A是AA中点.
    cut(exists Q, Perp A B B Q).
      intro.
      ex_elim H0 Q.
      cut(exists P, exists T, Perp A B P A /\ Col A B T /\ Bet Q T P).
        intros.
        ex_elim H0 P.
        ex_and H2 T.
        assert (Le A P B Q \/ Le B Q A P) by (apply 长度小于等于的决定性).
        induction H4.
          apply midpoint_existence_aux with P Q T; Perp.
        assert (exists X : Tpoint, 中点 X B A)
          by (apply (midpoint_existence_aux B A Q P T); finish).
        ex_elim H5 X.
        exists X.
        中点.
       apply l8_21;assumption.
    assert (exists P : Tpoint, (exists T : Tpoint, Perp B A P B /\ Col B A T /\ Bet A T P)) by (apply (l8_21 B A);auto).
    ex_elim H0 P.
    ex_elim H1 T.
    spliter.
    exists P.
    Perp.
Qed.


Lemma perp_in_id : forall A B C X, 垂直于 X A B C A -> X = A.
Proof.
    intros.
    assert (Perp A B C A).
      unfold Perp.
      exists X.
      assumption.
    assert (A <> B /\ C <> A).
      apply perp_distinct.
      assumption.
    spliter.
    assert (HH:=H0).
    apply perp_perp_in in HH.
    assert (l8_16_1:=l8_16_1 A B C B A).
    assert (~Col A B C /\ Per C A B).
      apply l8_16_1;Col.
    spliter.
    unfold 垂直于 in H.
    spliter.
    apply l8_18_uniqueness with A B C; Col.
      apply perp_sym.
      eapply perp_col with A; Col; Perp.
        intro.
        subst X.
        Col.
Qed.


Lemma l8_22 : forall A B P R X ,
 A <> B -> A <> P ->
 Per B A P -> Per A B R ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B /\ 中点 X A B /\ 中点 X P R.
Proof.
    intros.
    assert (Cong A R P B).
      apply (per_cong A B P R X); assumption.
    split.
      assumption.
    assert (~ Col B A P).
      apply per_not_col.
        auto.
        assumption.
      assumption.
    apply 四点对边等长则对角线交点平分对角线; Col; Cong.
    intro; treat_equalities; Col.
Qed.

Lemma l8_22_bis : forall A B P R X,
 A <> B -> A <> P ->
 Perp A B P A -> Perp A B R B ->
 Cong A P B R -> Col A B X -> Bet P X R ->
 Cong A R P B /\ 中点 X A B /\ 中点 X P R.
Proof.
    intros.
    apply l8_22; auto.
       apply perp_per_1;auto.
       apply perp_per_1;Perp.
Qed.

Lemma perp_in_perp : forall A B C D X, 垂直于 X A B C D -> Perp A B C D.
Proof.
    intros.
    unfold Perp.
    exists X.
    assumption.
Qed.

End T8_4.

Hint Resolve perp_per_1 perp_per_2 perp_col perp_perp_in perp_in_perp : perp.

Section T8_5.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma perp_proj : forall A B C D, Perp A B C D -> ~Col A C D -> exists X, Col A B X /\ Perp A X C D.
Proof.
    intros.
    unfold Perp in H.
    ex_and H X.
    exists X.
    split.
      unfold 垂直于 in H1.
      spliter.
      apply 等价共线BCA.
      assumption.
    eapply perp_col.
      intro.
      subst X.
      unfold 垂直于 in H1.
      spliter.
      apply H0.
      assumption.
      apply perp_in_perp in H1.
      apply H1.
    unfold 垂直于 in H1.
    spliter.
    apply 等价共线BCA.
    assumption.
Qed.

Lemma l8_24 : forall A B P Q R T,
 Perp P A A B ->
 Perp Q B A B ->
 Col A B T ->
 Bet P T Q ->
 Bet B R Q ->
 Cong A P B R ->
 exists X, 中点 X A B /\ 中点 X P R.
Proof.
    intros.
    unfold Le in H4.
    assert (exists X, Bet T X B /\ Bet R X P).
      eapply 帕施公理.
        apply H2.
      assumption.
    ex_and H5 X.
    assert (Col A B X).
      induction (两点重合的决定性 T B).
        subst T.
        apply 中间性的同一律 in H5.
        subst X.
        apply ABB型共线.
      assert (Col T X B).
        unfold Col.
        left.
        assumption.
      apply 等价共线BAC.
      eapply 共线的传递性2.
        intro.
        apply H7.
        apply sym_equal.
        apply H9.
        apply 等价共线BCA.
        assumption.
      apply 等价共线CAB.
      assumption.
    assert (A <> B).
      apply perp_distinct in H.
      spliter.
      assumption.
    assert (A <> P).
      apply perp_distinct in H.
      spliter.
      auto.
    induction(共线的决定性 A B P).
      assert (B=A \/ P=A).
        eapply l8_9.
          apply perp_per_1.
          apply perp_sym.
          assumption.
        apply 等价共线BAC.
        assumption.
      induction H11.
        exists A.
        subst B.
        absurde.
      subst P.
      absurde.
    assert (B <> R).
      intro.
      subst R.
      apply 等长的同一性 in H4.
      subst P.
      absurde.
    assert (Q <> B).
      apply perp_distinct in H0.
      spliter.
      assumption.
    assert (~Col A B Q).
      intro.
      assert (A=B \/ Q=B).
        eapply l8_9.
          apply perp_per_2.
            auto.
          apply perp_comm.
          apply perp_sym.
          assumption.
        assumption.
      induction H14.
        contradiction.
      subst Q.
      absurde.
    assert (~Col A B R).
      intro.
      assert (Col B A Q).
        eapply 共线的传递性2.
          apply H11.
          apply 等价共线BCA.
          assumption.
        unfold Col.
        left.
        assumption.
      apply H13.
      apply 等价共线BAC.
      assumption.
    assert (P <> R).
      intro.
      subst R.
      apply 中间性的同一律 in H6.
      subst X.
      contradiction.
    induction (两点重合的决定性 A P).
      subst P.
      apply perp_distinct in H.
      spliter.
      absurde.
    assert (Perp A B R B).
      eapply perp_col.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col.
          assumption.
          apply perp_left_comm.
          apply H0.
        unfold Col.
        right; left.
        apply 中间性的对称性.
        assumption.
      apply ABB型共线.
    assert (Cong A R P B).
      apply (perp_cong A B P R X).
        assumption.
        assumption.
        apply perp_sym.
        assumption.
        assumption.
        assumption.
        assumption.
      apply 中间性的对称性.
      assumption.
    intros.
    assert (中点 X A B /\ 中点 X P R).
      apply (四点对边等长则对角线交点平分对角线 A P B R X).
        intro.
        apply H10.
        apply 等价共线ACB.
        assumption.
        assumption.
        assumption.
        apply 等长的右交换性.
        apply 等长的对称性.
        assumption.
        apply 等价共线ACB.
        assumption.
      unfold Col.
      left.
      apply 中间性的对称性.
      assumption.
    exists X.
    assumption.
Qed.

Lemma col_per2__per : forall A B C P X, A <> B -> Col A B C -> Per A X P -> Per B X P -> Per C X P.
Proof.
    intros.
    destruct (构造对称点 P X) as [Q].
    exists Q; split.
      assumption.
    apply (l4_17 A B); try apply per_double_cong with X; assumption.
Qed.

Lemma perp_in_per_1 :
 forall A B C D X,
  垂直于 X A B C D ->
  Per A X C.
Proof.
intros.
unfold 垂直于 in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_2 :
 forall A B C D X,
  垂直于 X A B C D ->
  Per A X D.
Proof.
intros.
unfold 垂直于 in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_3 :
 forall A B C D X,
  垂直于 X A B C D ->
  Per B X C.
Proof.
intros.
unfold 垂直于 in *.
decompose [and] H.
apply H5;
Col.
Qed.

Lemma perp_in_per_4 :
 forall A B C D X,
  垂直于 X A B C D ->
  Per B X D.
Proof.
intros.
unfold 垂直于 in *.
decompose [and] H.
apply H5;
Col.
Qed.

End T8_5.

Hint Resolve perp_in_per_1 perp_in_per_2 perp_in_per_3 perp_in_per_4 : perp.

Ltac midpoint M A B :=
 let T:= fresh in assert (T:= midpoint_existence A B);
 ex_and T M.

Tactic Notation "Name" ident(M) "the" "midpoint" "of" ident(A) "and" ident(B) :=
 midpoint M A B.
