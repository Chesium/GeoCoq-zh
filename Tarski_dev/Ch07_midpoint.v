Require Export GeoCoq.Tarski_dev.Ch06_out_lines.
Require Export GeoCoq.Tarski_dev.Tactics.ColR.

Ltac not_exist_hyp_comm A B := not_exist_hyp (A<>B);not_exist_hyp (B<>A).

Ltac not_exist_hyp2 A B C D := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D].
Ltac not_exist_hyp3 A B C D E F := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F].

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

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
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; assert_diffs; Col_refl tpoint col.

Section T7_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma midpoint_dec :
 forall I A B, 中点 I A B \/ ~ 中点 I A B.
Proof.
    intros.
    unfold 中点.
    elim (bet_dec A I B);intro; elim (cong_dec A I I B);intro; tauto.
Qed.

Lemma is_midpoint_id : forall A B, 中点 A A B -> A = B.
Proof.
    intros.
    unfold 中点 in H.
    spliter.
    treat_equalities;reflexivity.
Qed.

Lemma is_midpoint_id_2 : forall A B, 中点 A B A -> A=B.
Proof.
    intros.
    unfold 中点 in *.
    spliter.
    apply 等长的同一性 in H0.
    auto.
Qed.

Lemma l7_2 : forall M A B, 中点 M A B -> 中点 M B A.
Proof.
    unfold 中点.
    intuition.
Qed.

Lemma l7_3 : forall M A, 中点 M A A -> M=A.
Proof.
    unfold 中点.
    intros;spliter;treat_equalities;reflexivity.
Qed.


Lemma l7_3_2 : forall A, 中点 A A A.
Proof.
    unfold 中点.
    intros;repeat split;Between;Cong.
Qed.

(** This corresponds to l7_8 in Tarski's book. *)

Lemma symmetric_point_construction : forall P A, exists P', 中点 A P P'.
Proof.
    unfold 中点.
    intros.
    prolong P A E P A.
    exists E.
    split;Cong;Between.
Qed.

Lemma symmetric_point_uniqueness : forall A P P1 P2, 中点 P A P1 -> 中点 P A P2 -> P1=P2.
Proof.
    unfold 中点.
    intros.
    spliter.
    elim (两点重合的决定性 A P); intros.
      treat_equalities;auto.
    apply (点的唯一构造 A P A P);Cong.
Qed.

Lemma l7_9 : forall P Q A X, 中点 A P X -> 中点 A Q X -> P=Q.
Proof.
    unfold 中点.
    intros.
    spliter.
    induction (两点重合的决定性 A X).
      treat_equalities;reflexivity.
    apply (点的唯一构造 X A X A);Cong;Between.
Qed.

Lemma l7_9_bis : forall P Q A X, 中点 A P X -> 中点 A X Q -> P=Q.
Proof.
intros; apply l7_9 with A X; unfold 中点 in *; split; spliter; Cong; Between.
Qed.

Lemma l7_13 : forall A P Q P' Q',  中点 A P' P -> 中点 A Q' Q -> Cong P Q P' Q'.
Proof.
    unfold 中点.
    intros.
    spliter.
    induction (两点重合的决定性 P A).
      treat_equalities;Cong.
    prolong P' P X Q A.
    prolong X P' X' Q A.
    prolong Q' Q Y P A.
    prolong Y Q' Y' P A.
    assert (Bet Y A Q') by eBetween.
    assert (Bet P' A X) by eBetween.
    assert (Bet A P X) by eBetween.
    assert(Bet Y Q A) by eBetween.
    assert (Bet A Q' Y') by eBetween.
    assert (Bet X' P' A) by eBetween.
    assert(Bet X A X') by eBetween.
    assert(Bet Y A Y') by eBetween.
    assert (Cong A X Y A) by (apply 两组连续三点分段等则全体等 with P Q; Cong).
    assert (Cong A Y' X' A).
      apply 两组连续三点分段等则全体等 with Q' P'; Between.
        apply 等长的传递性 with A Q; Cong.
      apply 等长的传递性 with A P; Cong.
    assert (Cong A Y A Y').
      apply (两组连续三点分段等则全体等 A Q Y _ Q' Y'); Between; Cong.
      apply 等长的传递性 with A P; Cong.
    assert (Cong X A Y' A) by (apply 等长的传递性 with A Y; Cong).
    assert (Cong A X' A Y) by (apply 等长的传递性 with A Y'; Cong).
    assert (五线段形式 X A X' Y' Y' A Y X).
      unfold 五线段形式;repeat split; Cong.
        apply 中间性转共线;auto.
      eapply (两组连续三点分段等则全体等 X A X' Y' A Y);Between.
    assert (A <> X).
      eapply bet_neq12__neq.
        apply H14.
      auto.
    assert (Cong X' Y' Y X) by eauto using l4_16.
    assert (Cong A X A X') by (apply 等长的传递性 with A Y; Cong).
    assert (内五线段形式 Y Q A X Y' Q' A X') by (unfold 内五线段形式, 五线段形式 in *;spliter;repeat split;Between; Cong).
    assert (Cong Q X Q' X') by eauto using l4_2.
    assert (内五线段形式 X P A Q X' P' A Q') by (unfold 内五线段形式;repeat split;Between;Cong).
    eauto using l4_2.
Qed.

Lemma l7_15 : forall P Q R P' Q' R' A,
 中点 A P P' -> 中点 A Q Q' -> 中点 A R R' -> Bet P Q R -> Bet P' Q' R'.
Proof.
    intros.
    spliter.
    eapply l4_6.
      apply H2.
    unfold 三角形全等.
    repeat split.
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      assumption.
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      assumption.
    eapply l7_13.
      apply l7_2.
      apply H0.
    apply l7_2.
    assumption.
Qed.


Lemma l7_16 : forall P Q R S P' Q' R' S' A,
  中点 A P P' -> 中点 A Q Q' ->
  中点 A R R' -> 中点 A S S' ->
  Cong P Q R S -> Cong P' Q' R' S'.
Proof.
    intros.
    assert (Cong P Q P' Q').
      eapply l7_13.
        apply l7_2.
        apply H.
      apply l7_2.
      apply H0.
    assert (Cong R S R' S').
      eapply l7_13.
        apply l7_2.
        apply H1.
      apply l7_2.
      apply H2.
    apply 等长的传递性 with P Q; Cong.
    apply 等长的传递性 with R S; Cong.
Qed.


Lemma symmetry_preserves_midpoint :
   forall A B C D E F Z,
 中点 Z A D -> 中点 Z B E ->
 中点 Z C F -> 中点 B A C -> 中点 E D F.
Proof.
    intros.
    unfold 中点.
    unfold 中点 in H2.
    spliter.
    split.
      eapply l7_15;eauto.
    eapply l7_16;eauto.
Qed.

End T7_1.

Hint Resolve l7_13 : cong.
Hint Resolve l7_2 l7_3_2 : midpoint.

Ltac 中点 := auto with midpoint.

Section T7_2.

Context {Tn:无维度中性塔斯基公理系统}.
Context {TnEQD:无维度中性塔斯基公理系统_带两点重合决定性 Tn}.

Lemma Mid_cases :
  forall A B C,
  中点 A B C \/ 中点 A C B ->
  中点 A B C.
Proof.
    intros.
    decompose [or] H; 中点.
Qed.

Lemma Mid_perm :
  forall A B C,
  中点 A B C ->
  中点 A B C /\ 中点 A C B.
Proof.
    unfold 中点.
    intros.
    spliter.
    repeat split; Between; Cong.
Qed.

Lemma l7_17 : forall P P' A B, 中点 A P P' -> 中点 B P P' -> A=B.
Proof.
    intros.
    assert (Cong P B P' B).
      unfold 中点 in *.
      spliter.
      Cong.
    assert (exists B', 中点 A B B') by (apply symmetric_point_construction).
    induction H2.
    assert (Cong P' B P x) by eauto with midpoint cong.
    assert (Cong P B P x) by (apply 等长的传递性 with P' B; Cong).
    assert (Cong P B P' x) by eauto with midpoint cong.
    assert (Cong P' B P' x) by (apply 等长的传递性 with P x; Cong; apply 等长的传递性 with P B; Cong).
    assert (Bet P B P') by (unfold 中点 in *;spliter;assumption).
    assert (B=x) by (apply (l4_19 P P' B x);Between).
    subst x.
    apply l7_3.
    assumption.
Qed.

Lemma l7_17_bis : forall P P' A B, 中点 A P P' -> 中点 B P' P -> A=B.
Proof.
    intros.
    apply l7_17 with P P'; 中点.
Qed.

Lemma l7_20 : forall M A B,
  Col A M B -> Cong M A M B -> A=B \/ 中点 M A B.
Proof.
    unfold Col.
    intros.
    induction H.
      right.
      unfold 中点.
      split.
        assumption.
      Cong.
    induction H.
      assert (Cong A B B B) by (apply (l4_3 A B M B B M);Between;Cong).
      treat_equalities;auto.
    assert (Cong B A A A) by (apply (l4_3 B A M A A M);Cong;Between).
    treat_equalities;auto.
Qed.

Lemma l7_20_bis : forall M A B, A<>B ->
  Col A M B -> Cong M A M B -> 中点 M A B.
Proof.
   intros.
   induction (l7_20 M A B H0 H1);intuition.
Qed.

Lemma cong_col_mid : forall A B C,
 A <> C -> Col A B C -> Cong A B B C ->
 中点 B A C.
Proof.
    intros.
    apply l7_20 in H0.
      intuition subst.
    Cong.
Qed.

Lemma l7_21 : forall A B C D P,
  ~ Col A B C -> B<>D ->
  Cong A B C D -> Cong B C D A ->
  Col A P C -> Col B P D ->
  中点 P A C /\ 中点 P B D.
Proof.
    intros.
    assert_diffs.
    assert (exists P', 三角形全等 B D P D B P').
      eapply l4_14.
        Col.
      Cong.
    induction H9.
    assert (Col D B x) by
      (apply 全等于退化的三角形 with B D P;Col).
    assert (五线段形式 B D P A D B x C).
      unfold 五线段形式.
      unfold 三角形全等 in *.
      spliter.
      repeat split; Cong; Col.
    assert (五线段形式 B D P C D B x A).
      unfold 五线段形式.
      unfold 三角形全等 in *.
      spliter.
      repeat split; Col; Cong.
    assert (Cong P A x C) by (eauto using l4_16).
    assert (Cong P C x A) by (eauto using l4_16).
    assert (三角形全等 A P C C x A) by (unfold 三角形全等;repeat split; Cong).
    assert (Col C x A) by (eauto using 全等于退化的三角形).
    assert (P=x).
      unfold 五线段形式 in *.
      spliter.
      apply (l6_21 A C B D); Col.
    subst x.
    unfold 三角形全等 in *;spliter.
    split;apply l7_20_bis;Col;Cong.
Qed.

Lemma l7_22_aux : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   中点 M1 A1 B1 -> 中点 M2 A2 B2 ->
   Le C A1 C A2 ->
   Bet M1 C M2.
Proof.
    intros.
    induction (两点重合的决定性 A2 C).
      subst C.
      apply le_zero in H5.
      subst A2.
      apply 等长的反向同一性 in H1.
      subst B1.
      apply 等长的反向同一性 in H2.
      subst B2.
      apply l7_3 in H4.
      subst A1.
      apply ABB中间性.
    assert (exists A, 中点 C A2 A).
      apply symmetric_point_construction.
    induction H7.
    assert (exists B, 中点 C B2 B).
      apply symmetric_point_construction.
    induction H8.
    assert (exists M, 中点 C M2 M).
      apply symmetric_point_construction.
    induction H9.
    assert(中点 x1 x x0).
      unfold 中点.
      split.
        eapply l7_15.
          apply H7.
          apply H9.
          apply H8.
        unfold 中点 in H4.
        spliter.
        assumption.
      eapply l7_16.
        apply H7.
        apply H9.
        apply H9.
        apply H8.
      unfold 中点 in H4.
      spliter.
      assumption.
    assert (Le C A1 C x).
      eapply l5_6.
      repeat split.
        apply H5.
        apply 等长的自反性.
      unfold 中点 in H7.
      spliter.
      apply 等长的左交换性.
      assumption.
    assert (Bet C A1 x).
      induction (两点重合的决定性 A1 C).
        subst A1.
        apply AAB中间性.
      apply l6_13_1; [|assumption].
      unfold Out.
      repeat split.
        assumption.
        intro.
        subst x.
        apply le_zero in H11.
        apply H12.
        subst A1.
        reflexivity.
      eapply l5_2.
        apply H6.
        apply 中间性的对称性.
        assumption; intro.
      unfold 中点 in H7.
      spliter.
      assumption.
    (* assert (M1=x).
    eauto with 中点.
    *)
    assert (Le C B1 C x0).
      eapply l5_6.
        apply H11.
        assumption.
      unfold 中点 in *.
      spliter.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H16.
      apply 等长的传递性 with B2 C.
        apply 等长的交换性.
        assumption.
      assumption.
    assert (Bet C B1 x0).
      induction (两点重合的决定性 B1 C).
        subst B1.
        apply 等长的对称性 in H1.
        apply 等长的反向同一性 in H1.
        subst A1.
        apply AAB中间性.
      induction (两点重合的决定性 x0 C).
        subst x0.
        apply le_zero in H13.
        subst B1.
        apply ABB中间性.
      induction (两点重合的决定性 B2 C).
        subst B2.
        apply 等长的对称性 in H2.
        eapply 等长的反向同一性 in H2.
        subst A2.
        apply le_zero in H5.
        subst A1.
        apply 等长的反向同一性 in H1.
        subst B1.
        apply False_ind.
        apply H14.
        reflexivity.
      eapply l6_13_1.
        unfold Out.
        repeat split.
          assumption.
          assumption.
        apply l5_2 with B2; Between.
        unfold 中点 in H8.
        spliter.
        assumption.
      assumption.
    assert (exists Q, Bet x1 Q C /\ Bet A1 Q B1).
      eapply l3_17.
        apply 中间性的对称性.
        apply H12.
        apply 中间性的对称性.
        apply H14.
      unfold 中点 in H10.
      spliter.
      assumption.
    ex_and H15 Q.
    assert (内五线段形式 x A1 C x1 x0 B1 C x1).
      unfold 内五线段形式.
      unfold 中点 in *.
      spliter.
      repeat split.
        apply 中间性的对称性.
        assumption.
        apply 中间性的对称性.
        assumption.
        eapply 等长的传递性.
          apply 等长的交换性.
          apply 等长的对称性.
          apply H20.
        eapply 等长的传递性.
          apply H2.
        apply 等长的交换性.
        assumption.
        apply 等长的交换性.
        assumption.
        apply 等长的右交换性.
        assumption.
      apply 等长的自反性.
    assert (Cong A1 x1 B1 x1).
      eapply l4_2.
      apply H17.
    assert (Cong Q A1 Q B1).
      induction(两点重合的决定性 C x1).
        subst x1.
        apply 中间性的同一律 in H15.
        subst Q.
        apply 等长的交换性.
        assumption.
      eapply l4_17.
        apply H19.
        unfold Col.
        right; left.
        assumption.
        assumption.
      apply 等长的交换性.
      assumption.
    assert (中点 Q A1 B1).
      unfold 中点.
      split.
        assumption.
      apply 等长的左交换性.
      assumption.
    assert (Q=M1).
      eapply l7_17.
        apply H20.
      assumption.
    subst Q.
    eapply between_exchange3.
      apply H15.
    unfold 中点 in H9.
    spliter.
    apply 中间性的对称性.
    assumption.
Qed.

(** This is Krippen lemma , proved by Gupta in its PhD in 1965 as Theorem 3.45 *)

Lemma l7_22 : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   中点 M1 A1 B1 -> 中点 M2 A2 B2 ->
   Bet M1 C M2.
Proof.
    intros.
    assert (Le C A1 C A2 \/ Le C A2 C A1).
      eapply le_cases.
    induction H5.
      eapply l7_22_aux.
        apply H.
        apply H0.
        apply H1.
        apply H2.
        assumption.
        assumption.
      assumption.
    apply 中间性的对称性.
    eapply l7_22_aux with A2 A1 B2 B1; finish.
Qed.

Lemma 中间性转共线1 : forall A B C D, Bet A B D -> Bet A C D -> Col A B C.
Proof.
    intros.
    assert(Bet A B C \/ Bet A C B).
      eapply l5_3.
        apply H.
      assumption.
    unfold Col.
    induction H1.
      left.
      assumption.
    right; left.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma l7_25 : forall A B C,
  Cong C A C B ->
  exists X, 中点 X A B.
Proof.
    intros.
    induction(col_dec A B C).
      assert(A = B \/ 中点 C A B).
        apply l7_20.
          unfold Col in *.
          intuition.
        assumption.
      induction H1.
        subst B.
        exists A.
        apply l7_3_2.
      exists C.
      assumption.
    assert (exists P, Bet C A P /\ A<>P).
      apply point_construction_different.
    ex_and H1 P.
    prolong C B Q A P.
    assert (exists R, Bet A R Q /\ Bet B R P).
      eapply 帕施公理.
        apply 中间性的对称性.
        apply H1.
      apply 中间性的对称性.
      assumption.
    ex_and H5 R.
    assert (exists X, Bet A X B /\ Bet R X C).
      eapply 帕施公理.
        apply H1.
      assumption.
    ex_and H7 X.
    exists X.
    unfold 中点.
    split.
      assumption.
    apply 等长的左交换性.
    cut(Cong R A R B).
      intros.
      induction(两点重合的决定性 R C).
        subst R.
        assert (C = X).
          apply 中间性的同一律.
          assumption.
        subst X.
        assumption.
      eapply l4_17.
        apply H10.
        unfold Col.
        right; left.
        apply 中间性的对称性.
        assumption.
        assumption.
      assumption.
    assert (外五线段形式 C A P B C B Q A).
      unfold 外五线段形式.
      repeat split.
        assumption.
        assumption.
        assumption.
        apply 等长的对称性.
        assumption.
        apply 等长的对称性.
        assumption.
      apply 等长的伪自反性.
    assert (Cong P B Q A).
      eapply 五线段公理_等价SAS_with_def.
        eapply H9.
      unfold Col in H0.
      intuition.
      apply H0.
      subst A.
      apply ABB中间性.
    assert (exists R', Bet A R' Q /\ 三角形全等 B R P A R' Q).
      eapply l4_5.
        assumption.
      apply 等长的交换性.
      assumption.
    ex_and H11 R'.
    assert (内五线段形式 B R P A A R' Q B).
      unfold 内五线段形式.
      repeat split.
        assumption.
        assumption.
        apply 等长的交换性.
        assumption.
        unfold 三角形全等 in H12.
        spliter.
        assumption.
        apply 等长的伪自反性.
      apply 等长的交换性.
      apply 等长的对称性.
      assumption.
    assert (内五线段形式 B R P Q A R' Q P).
      unfold 内五线段形式.
      repeat split;try assumption.
        apply 等长的交换性.
        assumption.
        unfold 三角形全等 in H12.
        spliter.
        assumption.
      apply 等长的伪自反性.
    assert (Cong R A R' B).
      eapply l4_2.
      apply H13.
    assert (Cong R Q R' P).
      eapply l4_2.
      apply H14.
    assert (三角形全等 A R Q B R' P).
      unfold 三角形全等.
      repeat split.
        apply 等长的交换性.
        assumption.
        apply 等长的交换性.
        apply 等长的对称性.
        assumption.
      assumption.
    assert (Col B R' P).
      apply (全等于退化的三角形 A R Q); Col.
    cut(R=R').
      intro.
      subst R'.
      assumption.
    assert (B <> P).
      unfold 内五线段形式, 外五线段形式, 三角形全等 in *.
      spliter.
      intro.
      subst P.
      apply 中间性的同一律 in H14.
      subst R.
      apply 等长的反向同一性 in H12.
      subst R'.
      apply 等长的反向同一性 in H32.
      subst Q.
      apply 中间性的同一律 in H5.
      apply H2.
      assumption.
    assert (A <> Q).
      unfold 内五线段形式, 外五线段形式, 三角形全等 in *.
      spliter.
      intro.
      subst Q.
      apply 等长的反向同一性 in H20.
      subst P.
      apply H19.
      reflexivity.
    assert(B <> Q).
      intro.
      subst Q.
      apply 等长的对称性 in H4.
      apply 等长的同一性 in H4.
      subst P.
      apply H2.
      reflexivity.
    assert (B <> R).
      intro.
      unfold 三角形全等, 内五线段形式, 外五线段形式 in *.
      spliter.
      subst R.
      clean_duplicated_hyps.
      assert (Col B A C).
        apply col_transitivity_1 with X; Col.
        intro.
        apply 等长的对称性 in H12.
        apply 等长的同一性 in H12.
        subst R'.
        subst X.
        clean_duplicated_hyps.
        assert (Bet B A C \/ Bet B C A).
          apply l5_2 with Q; Between.
        apply H0.
        unfold Col.
        induction H9.
          right;right.
          apply 中间性的对称性.
          assumption.
        right; left.
        assumption.
      apply H0.
      apply col_permutation_4.
      assumption.
    eapply (l6_21 A Q B P R R' ).
      intro.
      unfold Col in H23.
      induction H23.
        assert(Bet A B C).
          eapply outer_transitivity_between2.
            apply H23.
            apply 中间性的对称性.
            assumption.
          intro.
          apply H21.
          rewrite H24.
          reflexivity.
        apply H0.
        unfold Col.
        left.
        assumption.
      induction H23.
        assert(Bet B A C \/ Bet B C A).
          apply (l5_2 Q); Between.
        apply H0.
        unfold Col.
        induction H24.
          right;right.
          apply 中间性的对称性.
          assumption.
        right; left.
        assumption.
      assert(Bet A B C).
        eapply between_exchange3.
          apply 中间性的对称性.
          apply H23.
        apply 中间性的对称性.
        assumption.
      apply H0.
      unfold Col.
      left.
      assumption.
      assumption.
      unfold Col.
      right; left.
      apply 中间性的对称性.
      assumption.
      unfold Col.
      right; left.
      apply 中间性的对称性.
      assumption.
      unfold Col.
      right; left.
      apply 中间性的对称性.
      assumption.
    unfold Col.
    unfold Col in H18.
    induction H18.
      right; left.
      apply 中间性的对称性.
      assumption.
    induction H18.
      left.
      apply 中间性的对称性.
      assumption.
    right;right.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma midpoint_distinct_1 : forall I A B,
 A<>B ->
 中点 I A B ->
 I<>A /\ I<>B.
Proof.
    intros.
    split.
      intro.
      subst.
      unfold 中点 in *.
      decompose [and] H0.
      treat_equalities.
      intuition.
    intro;subst.
    unfold 中点 in *.
    decompose [and] H0.
    treat_equalities.
    intuition.
Qed.

Lemma midpoint_distinct_2 : forall I A B,
 I<>A ->
 中点 I A B ->
 A<>B /\ I<>B.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold 中点 in *;spliter.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
      intuition.
    intuition.
Qed.


Lemma midpoint_distinct_3 : forall I A B,
 I<>B ->
 中点 I A B ->
 A<>B /\ I<>A.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold 中点 in *;spliter.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply midpoint_distinct_1 in H0.
      intuition.
    intuition.
Qed.


Lemma midpoint_def : forall A B C, Bet A B C -> Cong A B B C -> 中点 B A C.
Proof.
    intros.
    unfold 中点.
    split;assumption.
Qed.

Lemma midpoint_bet : forall A B C, 中点 B A C -> Bet A B C.
Proof.
    unfold 中点.
    intros.
    elim H.
    intros.
    assumption.
Qed.

Lemma midpoint_col : forall A M B, 中点 M A B -> Col M A B.
Proof.
    intros.
    unfold Col.
    right;right.
    apply midpoint_bet.
    apply l7_2.
    assumption.
Qed.

Lemma midpoint_cong : forall A B C, 中点 B A C -> Cong A B B C.
Proof.
    unfold 中点.
    intros.
    elim H.
    intros.
    assumption.
Qed.

Lemma midpoint_out : forall A B C, A <> C -> 中点 B A C -> Out A B C.
Proof.
    intros.
    repeat split.
      apply midpoint_distinct_1 in H0; spliter; auto.
      auto.
    left.
    apply midpoint_bet.
    assumption.
Qed.

Lemma midpoint_out_1 : forall A B C, A <> C -> 中点 B A C -> Out C A B.
Proof.
    intros.
    apply l6_6, midpoint_out; 中点.
Qed.

Lemma midpoint_not_midpoint : forall I A B,
  A<>B ->
  中点 I A B ->
~ 中点 B A I.
Proof.
    intros.
    assert (I<>B).
      apply midpoint_distinct_1 in H0.
        tauto.
      assumption.
    apply midpoint_bet in H0.
    intro.
    apply midpoint_bet in H2.
    assert (I=B).
      apply 中间性的对称性 in H0.
      apply 中间性的对称性 in H2.
      eapply between_equality.
        apply H2.
      apply H0.
    intuition.
Qed.

Lemma swap_diff : forall (A B : Tpoint), A<>B -> B<>A.
Proof.
    intuition.
Qed.

Lemma cong_cong_half_1 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Cong A B A' B' -> Cong A M A' M'.
Proof.
    intros.
    unfold 中点 in *.
    spliter.
    assert(exists M'', Bet A' M'' B' /\ 三角形全等 A M B A' M'' B').
      eapply l4_5.
        assumption.
      assumption.
    ex_and H4 M''.
    assert (中点 M'' A' B').
      unfold 中点.
      split.
        assumption.
      unfold 三角形全等 in H5.
      spliter.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H5.
      eapply 等长的传递性.
        apply H3.
      assumption.
    assert(M'=M'').
      eapply l7_17; unfold 中点; split.
        apply H0.
        apply H2.
        apply H4.
      unfold 中点 in H6.
      spliter.
      assumption.
    subst M''.
    unfold 三角形全等 in H5.
    spliter.
    assumption.
Qed.

Lemma cong_cong_half_2 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Cong A B A' B' -> Cong B M B' M'.
Proof.
    intros.
    apply cong_cong_half_1 with A A'.
      中点.
      中点.
    Cong.
Qed.

Lemma cong_mid2__cong : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Cong A M A' M' -> Cong A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' HCong.
    destruct HM.
    destruct HM'.
    apply (两组连续三点分段等则全体等 _ M _ _ M'); auto.
    apply (等长的传递性 _ _ A' M'); auto.
    apply (等长的传递性 _ _ A M); Cong.
Qed.

Lemma mid__lt : forall A M B,
 A <> B -> 中点 M A B ->
 Lt A M A B.
Proof.
    intros A M B HAB HM.
    destruct (midpoint_distinct_1 M A B HAB HM) as [HMA HMB].
    destruct HM.
    split.
      exists M; Cong.
    intro.
    apply HMB, between_cong with A; auto.
Qed.

Lemma le_mid2__le13 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Le A M A' M' -> Le A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    destruct HM.
    destruct HM'.
    apply (bet2_le2__le1346 _ M _ _ M'); auto.
    apply (l5_6 A M A' M'); auto.
Qed.

Lemma le_mid2__le12 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Le A B A' B' -> Le A M A' M'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    elim(le_cases A M A' M'); auto.
    intro.
    assert(Le A' B' A B) by (apply (le_mid2__le13 _ M' _ _ M); auto).
    apply cong__le.
    apply (cong_cong_half_1 _ _ B _ _ B'); auto.
    apply le_anti_symmetry; auto.
Qed.

Lemma lt_mid2__lt13 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Lt A M A' M' -> Lt A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' [HLe HNcong].
    split.
      apply le_mid2__le13 with M M'; trivial.
    intro.
    apply HNcong, cong_cong_half_1 with B B'; trivial.
Qed.

Lemma lt_mid2__lt12 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Lt A B A' B' -> Lt A M A' M'.
Proof.
    intros A M B A' M' B' HM HM' [HLe HNcong].
    split.
      apply le_mid2__le12 with B B'; trivial.
    intro.
    apply HNcong, cong_mid2__cong with M M'; trivial.
Qed.

Lemma midpoint_preserves_out :
 forall A B C A' B' C' M,
  Out A B C ->
  中点 M A A' ->
  中点 M B B' ->
  中点 M C C' ->
 Out A' B' C'.
Proof.
    intros.
    unfold Out in H.
    spliter.
    unfold Out.
    repeat split.
      intro.
      subst B'.
      assert (A = B).
        eapply symmetric_point_uniqueness.
          apply l7_2.
          apply H0.
        apply l7_2.
        assumption.
      auto.
      intro.
      subst C'.
      assert (A = C).
        eapply symmetric_point_uniqueness.
          apply l7_2.
          apply H0.
        apply l7_2.
        assumption.
      auto.
    induction H4.
      left.
      apply (l7_15 A B C A' B' C' M); assumption.
    right.
    eapply (l7_15 A C B A' C' B' M); assumption.
Qed.

Lemma col_cong_bet : forall A B C D, Col A B D -> Cong A B C D -> Bet A C B -> Bet  C A D \/ Bet C B D.
Proof.
intros.

prolong B A D1 B C.
prolong A B D2 A C.

assert(Cong A B C D1).
eapply (两组连续三点分段等则全体等 A C B C A D1).
assumption.
eapply between_exchange3.
apply 中间性的对称性.
apply H1.
assumption.
apply 等长的伪自反性.
Cong.
assert(D = D1 \/ 中点 C D D1).
eapply l7_20.
apply 中间性转共线 in H1.
apply 中间性转共线 in H2.

induction (两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H0.
apply 等长的同一性 in H0.
subst D.
Col.
eapply (col3 A B); Col.

CongR.

induction H7.
subst D1.
left.
eapply between_exchange3.
apply 中间性的对称性.
apply H1.
assumption.

assert(Cong B A C D2).
eapply (两组连续三点分段等则全体等 B C A C B D2).
Between.
eapply between_exchange3.
apply H1.
assumption.
apply 等长的伪自反性.
Cong.

assert(中点 C D2 D1).
unfold 中点.
split.

induction(两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H0.
apply 等长的同一性 in H0.
subst D.
apply is_midpoint_id in H7.
subst D1.
Between.
apply 中间性的对称性.

induction(两点重合的决定性 B C).
subst C.
apply 中间性的对称性.
apply 等长的同一性 in H3.
subst D1.
Between.

assert(Bet D1 C B).
eBetween.
assert(Bet C B D2).
eBetween.
eapply (outer_transitivity_between).
apply H11.
assumption.
auto.
unfold 中点 in H7.
spliter.
eapply 等长的传递性.
apply 等长的对称性.
apply 等长的交换性.
apply H8.
eapply 等长的传递性.
apply H0.
Cong.
assert(D = D2).
eapply symmetric_point_uniqueness.
apply l7_2.
apply H7.
apply l7_2.
assumption.
subst D2.
right.
eapply between_exchange3.
apply H1.
assumption.
Qed.

Lemma col_cong2_bet1 : forall A B C D, Col A B D -> Bet A C B -> Cong A B C D -> Cong A C B D -> Bet C B D.
Proof.
intros.
induction(两点重合的决定性 A C).
subst C.
apply 等长的对称性 in H2.
apply 等长的同一性 in H2.
subst D.
Between.

assert(HH:=col_cong_bet A B C D H H1 H0).
induction HH.
assert(A = D /\ B = C).
eapply bet_cong_eq.
Between.
eBetween.
Cong.
spliter.
subst D.
subst C.
Between.
assumption.
Qed.

Lemma col_cong2_bet2 : forall A B C D, Col A B D -> Bet A C B -> Cong A B C D -> Cong A D B C -> Bet C A D.
Proof.
intros.

induction(两点重合的决定性 B C).
subst C.
apply 等长的同一性 in H2.
subst D.
Between.

assert(HH:=col_cong_bet A B C D H H1 H0).
induction HH.
assumption.

assert(C = A /\ D = B).
eapply bet_cong_eq.
Between.
eBetween.
Cong.
spliter.
subst D.
subst C.
Between.
Qed.

Lemma col_cong2_bet3 : forall A B C D, Col A B D -> Bet A B C -> Cong A B C D -> Cong A C B D -> Bet B C D.
Proof.
intros.

induction(两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H1.
apply 等长的同一性 in H1.
subst D.
Between.


eapply (col_cong2_bet2 _ A).
apply 中间性转共线 in H0.
ColR.
Between.
Cong.
Cong.
Qed.

Lemma col_cong2_bet4 : forall A B C D, Col A B C -> Bet A B D -> Cong A B C D -> Cong A D B C -> Bet B D C.
Proof.
intros.
induction(两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H1.
apply 等长的同一性 in H1.
subst D.
Between.
apply (col_cong2_bet1 A D B C).
apply 中间性转共线 in H0.
ColR.
assumption.
Cong.
Cong.
Qed.

Lemma col_bet2_cong1 : forall A B C D, Col A B D -> Bet A C B -> Cong A B C D -> Bet C B D -> Cong A C D B.
Proof.
intros.
apply (l4_3 A C B D B C); Between; Cong.
Qed.

Lemma col_bet2_cong2 : forall A B C D, Col A B D -> Bet A C B -> Cong A B C D -> Bet C A D -> Cong D A B C.
Proof.
intros.
apply (l4_3 D A C B C A); Between; Cong.
Qed.


Lemma bet2_lt2__lt : forall O o A B a b : Tpoint,
       Bet a o b -> Bet A O B -> Lt o a O A -> Lt o b O B -> Lt a b A B.
Proof.
intros.
unfold Lt.
split.
unfold Lt in *.
spliter.
apply(bet2_le2__le O o A B a b); auto.
intro.

induction(两点重合的决定性 O A).
treat_equalities.
unfold Lt in H1.
spliter.
apply le_zero in H0.
treat_equalities.
apply H1.
apply 等长的平凡同一性.

induction(两点重合的决定性 O B).
treat_equalities.
unfold Lt in H2.
spliter.
apply le_zero in H0.
treat_equalities.
apply H2.
apply 等长的平凡同一性.

unfold Lt in *.
spliter.

unfold Le in H1.
ex_and H1 a'.
unfold Le in H2.
ex_and H2 b'.

assert(Bet a' O b').
  apply between_inner_transitivity with B.
    apply between_exchange3 with A.
      Between.
    assumption.
  Between.
assert(Cong a b a' b').
{
  apply (两组连续三点分段等则全体等 a o b a' O b'); Cong.
}
assert(Cong a' b' A B) by (apply 等长的传递性 with a b; Cong).
assert(Bet A b' B) by eBetween.

induction(两点重合的决定性 A a').
treat_equalities.
assert(b'=B \/ 中点 A b' B).
{
  apply l7_20.
  Col.
  Cong.
}
induction H1.
treat_equalities.
contradiction.
unfold 中点 in *.
spliter.
assert(b' = B).
{
  apply (between_cong A).
  Between.
  Cong.
}
treat_equalities; tauto.

assert(Bet B a' A) by eBetween.
induction(两点重合的决定性 B b').
treat_equalities.
assert(a'=A \/ 中点 B a' A).
{
  apply l7_20.
  Col.
  Cong.
}
induction H2.
treat_equalities.
contradiction.
unfold 中点 in *.
spliter.
assert(a' = A).
{
  apply (between_cong B).
  Between.
  Cong.
}
treat_equalities; tauto.

assert(Bet a' A b' \/ Bet a' B b').
{
  apply(col_cong_bet A B a' b').
  Col.
  Cong.
  eBetween.
}
induction H17.
assert(A = a').
{
  apply(between_equality _ _ b').
    apply between_exchange4 with O.
      Between.
      apply between_inner_transitivity with B.
        assumption.
      assumption.
  assumption.
}
treat_equalities; tauto.
assert(b' = B).
{
  apply(between_equality _ _ a').
  Between.
  apply between_exchange4 with O.
    Between.
  apply between_inner_transitivity with A.
    Between.
  Between.
}
treat_equalities; tauto.
Qed.

Lemma bet2_lt_le__lt : forall O o A B a b : Tpoint,
       Bet a o b -> Bet A O B -> Cong o a O A -> Lt o b O B -> Lt a b A B.
Proof.
intros.
unfold Lt.
split.
unfold Lt in *.
spliter.
assert(Le o a O A).
{
  unfold Le.
  exists A.
  split; Between.
}
apply(bet2_le2__le O o A B a b); auto.
intro.

assert(HH:=由一点往一方向构造等长线段 A O o b).
ex_and HH b'.

unfold Lt in H2.
spliter.
apply H6.

apply(l4_3_1 a o b A O B H H0 ); Cong.
Qed.

End T7_2.

Hint Resolve midpoint_bet : between.
Hint Resolve midpoint_col : col.
Hint Resolve midpoint_cong : cong.
Hint Resolve midpoint_out midpoint_out_1 : out.