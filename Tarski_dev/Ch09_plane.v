Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.
Require Export GeoCoq.Tarski_dev.Annexes.coplanar.

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
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
   | H:(Per ?A ?D ?C), H2 : (Per ?C ?D ?A) |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?A ?B ?D ?C |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?C ?D ?A ?B |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?C ?D ?B ?A |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?D ?C ?B ?A |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?D ?C ?A ?B |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?B ?A ?C ?D |- _ => clear H2
   | H:(垂直于 ?X ?A ?B ?C ?D), H2 : 垂直于 ?X ?B ?A ?D ?C |- _ => clear H2
end.

Ltac 统计不重合点 :=
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
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D (不重合的对称性 B A H2) H);clean_reap_hyps
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

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H (不重合的对称性 B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H (不重合的对称性 C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直推出不重合 A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:垂直于 ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直于推出不重合 X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; 统计不重合点; Col_refl tpoint col.

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
   | H:(Per ?X1 ?X2 ?X2)     |- _ => clear H
   | H:(Per ?X1 ?X1 ?X2)     |- _ => clear H
   | H:(中点 ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac clean := clean_trivial_hyps;clean_reap_hyps.

Section T9.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma ts_distincts : forall A B P Q, TS A B P Q ->
  A <> B /\ A <> P /\ A <> Q /\ B <> P /\ B <> Q /\ P <> Q.
Proof.
  intros A B P Q HTS.
  destruct HTS as [HNCol1 [HNCol2 [T [HCol HBet]]]].
  统计不重合点.
  repeat split; auto.
  intro; treat_equalities; auto.
Qed.

Lemma l9_2 : forall A B P Q, TS A B P Q -> TS A B Q P.
Proof.
    unfold TS.
    intros.
    分离合取式.
    repeat split; Col.
    destruct H1 as [T [HCol1 HCol2]].
    exists T; Col; Between.
Qed.

Lemma invert_two_sides : forall A B P Q,
 TS A B P Q -> TS B A P Q.
Proof with Col.
    unfold TS.
    intros.
    分离合取式.
    repeat split...
    ex_and H1 T.
    exists T;split...
Qed.


Lemma l9_3 : forall P Q A C M R B,
 TS P Q A C -> Col M P Q ->
 中点 M A C -> Col R P Q ->
 Out R A B -> TS P Q B C.
Proof with Col.
    intros.
    unfold TS in *.
    assert (~ Col A P Q).
      分离合取式.
      assumption.
    分离合取式.
    clear H.
    assert (P <> Q).
      intro.
      subst Q.
      Col.
    ex_and H6 T.
    show_distinct A C.
      intuition.
    assert (T = M).
      assert_bets.
      assert_cols.
      eapply l6_21_两线交点的唯一性 with P Q A C...
    subst T.
    repeat split...
      induction(两点重合的决定性 C M).
        subst M.
        intuition.
      intro.
      clear H0.
      assert (B <> R).
        intro.
        subst B.
        unfold Out in H3.
        分离合取式.
        absurde.
      assert (Col P R B) by ColR.
      assert (Col P R A).
        induction (两点重合的决定性 P B).
          subst B.
          assert_cols...
        apply 等价共线CAB.
        eapply 共线的传递性3.
          apply H0.
          assert_cols...
        Col.
      induction (两点重合的决定性 P R).
        subst R.
        apply H4.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ B).
          统计不重合点;intuition.
          apply 等价共线BAC.
          assumption.
        assert_cols...
      assert (Col P B A ).
        eapply 共线的传递性2.
          apply H13.
          assumption.
        assumption.
      induction (两点重合的决定性 P B).
        subst B.
        apply H4.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ R).
          apply H0.
          apply 等价共线BAC.
          assumption.
        unfold Out in H3.
        分离合取式.
        unfold Col.
        induction H16.
          right; left.
          assumption.
        right;right.
        Between.
      apply H4.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H15.
        Col.
      assumption.
    induction H3.
    分离合取式.
    induction H10.
      double B M B'.
      double R M R'.
      assert (Bet B' C R').
        eapply l7_15.
          apply H11.
          apply H1.
          apply H12.
        Between.
      assert (exists X, Bet M X R' /\ Bet C X B).
        eapply 帕施公理.
          (* assert_bets.
          Between.
          *)
          apply midpoint_bet.
          apply H11.
        apply 中间性的对称性.
        assumption.
      ex_and H14 X.
      exists X.
      split.
        assert (Col P M R ).
          eapply 共线的传递性2.
            apply H.
            Col.
          Col.
        assert (Col Q M R).
          eapply (共线的传递性2 _ P).
            auto.
            Col.
          Col.
        induction (两点重合的决定性 M X).
          subst X.
          assumption.
        show_distinct M R'.
          intuition.
        assert (M <> R).
          intro.
          subst R.
          eapply (中点组的唯一性1) in H12.
            apply H19.
            apply H12.
          apply A是AA中点.
        apply 等价共线CAB.
        ColR.
      Between.
    assert (exists X, Bet B X C /\ Bet M X R).
      eapply 帕施公理.
        apply H10.
      Between.
    ex_and H11 X.
    exists X.
    induction (两点重合的决定性 M R).
      subst R.
      apply 中间性的同一律 in H12.
      subst X.
      split; assumption.
    induction (两点重合的决定性 R X).
      subst X.
      split; assumption.
    split.
      induction (两点重合的决定性 X M).
        subst X.
        assumption.
      assert (Col P M R ).
        eapply 共线的传递性2.
          apply H.
          Col.
        Col.
      assert (Col X P Q).
        apply 等价共线CAB.
        ColR.
      assumption.
    assumption.
Qed.

(*
Lemma sym_sym : forall A C A', 中点 C A A' -> 对称P A' A C.
Proof.
    intros.
    apply M是AB中点则M是BA中点.
    assumption.
Qed.
*)

Lemma mid_preserves_col : forall A B C M A' B' C',
  Col A B C ->
  中点 M A A' ->
  中点 M B B' ->
  中点 M C C' ->
  Col A' B' C'.
Proof.
    intros.
    induction H.
      assert (Bet A' B' C').
        eapply l7_15 with A B C M;auto.
      Col.
    induction H.
      assert (Bet B' C' A').
        eapply l7_15 with B C A M;auto.
      Col.
    assert (Bet C' A' B').
      eapply l7_15 with C A B M;auto.
    Col.
Qed.

Lemma per_mid_per : forall A B X Y M,
   A <> B -> Per X A B ->
   中点 M A B -> 中点 M X Y ->
   Cong A X B Y /\ Per Y B A.
Proof.
    intros.
    assert (Cong A X B Y).
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H1.
      apply M是AB中点则M是BA中点.
      assumption.
    split.
      assumption.
    unfold Per in H0.
    ex_and H0 B'.
    double A B A'.
    assert (Cong B X A Y).
      eapply l7_13_同中点组两侧等长.
        apply H1.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (外五线段形式 B A B' X A B A' Y).
      unfold 外五线段形式.
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        assumption.
        apply 等长的伪自反性.
        unfold 中点 in *.
        分离合取式.
        eapply 等长的传递性.
          apply 等长的对称性.
          apply H8.
        apply 等长的左交换性.
        assumption.
        assumption.
      assumption.
    unfold Per.
    exists A'.
    split.
      assumption.
    assert (Cong B' X A' Y).
      eapply 五线段公理_等价SAS_with_def.
        apply H7.
      intro.
      apply H.
      subst B.
      reflexivity.
    eapply 等长的传递性.
      apply 等长的交换性.
      apply 等长的对称性.
      apply H6.
    eapply 等长的传递性.
      apply H4.
    apply 等长的交换性.
    assumption.
Qed.


Lemma sym_preserve_diff : forall A B M A' B',
 A <> B -> 中点 M A A' -> 中点 M B B' -> A'<> B'.
Proof.
    intros.
    intro.
    subst B'.
    assert (A = B).
      eapply 中点组的唯一性2.
        apply H0.
      assumption.
    contradiction.
Qed.


Lemma l9_4_1_aux : forall P Q A C R S M,
 Le S C R A ->
 TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> 中点 M R S ->
 (forall U C',中点 M U C' -> (Out R U A <-> Out S C C')).
Proof.
    intros.
    induction (两点重合的决定性 R S).
      subst S.
      apply M是AA中点则M与A重合 in H5.
      subst R.
      unfold TS in H0.
      assert (~ Col A P Q).
        分离合取式.
        assumption.
      分离合取式.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H8 T.
      induction (两点重合的决定性 M T).
        subst T.
        split.
          intro.
          unfold Out in *.
          分离合取式.
          repeat split.
            intro.
            subst C.
            apply 垂直推出不重合 in H4.
            分离合取式.
            absurde.
            intro.
            subst C'.
            apply M是AB中点则M是BA中点 in H6.
            eapply (中点组的唯一性1 _ _ M) in H6.
              apply H10.
              apply sym_equal.
              apply H6.
            apply A是AA中点.
          induction H12.
            assert (Bet U M C).
              eapply 中间性的交换传递性1.
                apply 中间性的对称性.
                apply H12.
              assumption.
            unfold 中点 in H13.
            分离合取式.
            eapply l5_2.
              apply H10.
              assumption.
            apply midpoint_bet.
            assumption.
          assert (Bet U M C).
            eapply 中间性的外传递性1.
              apply 中间性的对称性.
              apply H12.
              assumption.
            assumption.
          eapply l5_2.
            apply H10.
            assumption.
          unfold 中点 in H6.
          分离合取式.
          assumption.
        intro.
        unfold Out in *.
        分离合取式.
        repeat split.
          intro.
          subst U.
          eapply A是AB中点则A与B重合 in H6.
          subst C'.
          apply H11.
          reflexivity.
          intro.
          subst A.
          apply 垂直推出不重合 in H2.
          分离合取式.
          apply H13.
          reflexivity.
        unfold 中点 in H6.
        分离合取式.
        assert (Bet A M C').
          induction H12.
            eapply 中间性的外传递性2.
              apply H9.
              assumption.
            intro.
            apply H10.
            subst C.
            reflexivity.
          eapply 中间性的内传递性1.
            apply H9.
          assumption.
        eapply l5_2.
          apply H11.
          apply 中间性的对称性.
          assumption.
        apply 中间性的对称性.
        assumption.
      assert (Perp M T A M) by (eapply 与垂线共线之线也为垂线2  with P Q;Col).
      apply L形垂直转垂直于 in H11.
      apply 垂直于的交换性 in H11.
      eapply L形垂直于转直角 in H11.
      assert (Perp M T C M) by (eapply 与垂线共线之线也为垂线2  with P Q;Col).
      apply L形垂直转垂直于 in H12.
      apply 垂直于的交换性 in H12.
      eapply L形垂直于转直角 in H12.
      assert (M = T).
        apply (l8_6 C M T A).
          apply 直角的对称性;auto.
          apply 直角的对称性;auto.
        Between.
      subst T.
      split.
        intro.
        unfold Out in *.
        分离合取式.
        repeat split.
          intro.
          subst C.
          apply 垂直推出不重合 in H4.
          分离合取式.
          absurde.
          intro.
          subst C'.
          intuition.
        intuition.
      intuition.
    (*   R <> S  *)
    unfold Le in H.
    ex_and H D.
    assert (C <> S).
      intro.
      subst S.
      apply 垂直推出不重合 in H4.
      分离合取式.
      absurde.
    assert (R <> D).
      intro.
      subst D.
      apply 等长的同一性 in H8.
      apply H9.
      subst S.
      reflexivity.
    assert (Perp R S A R).
      eapply 与垂线共线之线也为垂线2.
        apply H2.
        assumption.
        apply 等价共线BCA.
        assumption.
        apply 等价共线BCA.
        assumption.
    assert(exists M, 中点 M S R /\ 中点 M C D).
      unfold TS in H0.
      assert (~ Col A P Q).
        分离合取式.
        assumption.
      分离合取式.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H14 T.
      eapply (四点成双垂直S形则存在一点平分两对角线 S R C A D T).
        apply 垂直的对称性.
        apply 垂直的左交换性.
        eapply 与垂线共线之线也为垂线2.
          apply H4.
          assumption.
          apply 等价共线BCA.
          assumption.
          apply 等价共线BCA.
          assumption.
        apply 垂直的右交换性.
        apply 垂直的对称性.
        assumption.
        eapply 共线的传递性4.
          apply H0.
          apply 等价共线BCA.
          assumption.
          apply 等价共线BCA.
          assumption.
        apply 等价共线BCA.
        assumption.
        apply 中间性的对称性.
        assumption.
        assumption.
      assumption.
    ex_and H12 M'.
    apply M是AB中点则M是BA中点 in H12.
    assert (M = M').
      eapply 中点的唯一性1.
        apply H5.
      apply H12.
    subst M'.
    split.
      intro.
      unfold Out in H14.
      分离合取式.
      unfold Out.
      repeat split.
        assumption.
        apply (sym_preserve_diff U R M); auto.
      induction H16.
        assert(Bet R U D \/ Bet R D U).
          eapply l5_3.
            apply H16.
          assumption.
        induction H17.
          right.
          eapply l7_15.
            apply H5.
            apply H6.
            apply M是AB中点则M是BA中点.
            apply H13.
          assumption.
        left.
        eapply l7_15.
          apply H5.
          apply M是AB中点则M是BA中点.
          apply H13.
          apply H6.
        assumption.
      left.
      eapply l7_15.
        apply H5.
        apply M是AB中点则M是BA中点.
        apply H13.
        apply H6.
      eapply 中间性的交换传递性2.
        apply H.
      apply H16.
    unfold Out.
    intros.
    分离合取式.
    repeat split.
      eapply sym_preserve_diff.
        apply H15.
        apply M是AB中点则M是BA中点.
        apply H6.
      apply M是AB中点则M是BA中点.
      assumption.
      intro.
      subst R.
      apply 垂直推出不重合 in H11.
      分离合取式.
      absurde.
    induction H16.
      eapply l5_1.
        apply H10.
        eapply l7_15.
          apply M是AB中点则M是BA中点.
          apply H12.
          apply H13.
          apply M是AB中点则M是BA中点.
          apply H6.
        assumption.
      assumption.
    left.
    eapply 中间性的交换传递性2.
      eapply l7_15.
        apply M是AB中点则M是BA中点.
        apply H12.
        apply M是AB中点则M是BA中点.
        apply H6.
        apply H13.
      assumption.
    assumption.
Qed.

Lemma 直角边共线点也构成直角2_eq : forall A B C, Per A B C -> Col A B C -> B <> C -> A = B.
Proof.
    intros.
    unfold Per in H.
    ex_and H C'.
    assert_bets.
    assert_cols.
    assert (Col A C C') by ColR.
    assert (C = C' \/ 中点 A C C') by (eapply 共线点间距相同要么重合要么中点;Col).
    induction H6.
      treat_equalities.
      intuition.
    eapply 中点的唯一性1;eauto.
Qed.


Lemma l9_4_1 : forall P Q A C R S M,
 TS P Q A C -> Col R P Q ->
 Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> 中点 M R S ->
 (forall U C',中点 M U C' -> (Out R U A <-> Out S C C')).
Proof.
    intros.
    assert (Le S C R A \/ Le R A S C).
      apply 长度小于等于的决定性.
    induction H6.
      apply (l9_4_1_aux P Q A C R S M); assumption.
    assert((Out R A U <-> Out S C' C) -> (Out R U A <-> Out S C C')).
      intro.
      induction H7.
      split.
        intro.
        eapply l6_6.
        apply H7.
        apply l6_6.
        assumption.
      intro.
      apply l6_6.
      apply H8.
      apply l6_6.
      assumption.
    apply H7.
    assert((Out S C' C <-> Out R A U) -> (Out R A U <-> Out S C' C)).
      intro.
      induction H8.
      split.
        intro.
        apply H9.
        assumption.
      intro.
      apply H8.
      assumption.
    apply H8.
    eapply (l9_4_1_aux).
      assumption.
      apply l9_2.
      apply H.
      assumption.
      assumption.
      assumption.
      assumption.
      apply M是AB中点则M是BA中点.
      apply H4.
    apply M是AB中点则M是BA中点.
    assumption.
Qed.

Lemma mid_two_sides : forall A B M X Y,
 中点 M A B -> ~ Col A B X -> 中点 M X Y ->
 TS A B X Y.
Proof.
    intros A B M X Y HM1 HNCol HM2.
    repeat split; Col.
      统计不重合点.
      assert (X<>Y) by (intro; treat_equalities; apply HNCol; Col).
      intro; apply HNCol; ColR.
    exists M; split; Col; Between.
Qed.

Lemma col_preserves_two_sides : forall A B C D X Y,
 C <> D -> Col A B C -> Col A B D ->
 TS A B X Y ->
 TS C D X Y.
Proof.
    intros A B C D X Y.
    assert (H := A).
    intros.
    unfold TS in *.
    assert (~ Col X A B).
      分离合取式.
      assumption.
    clear H.
    assert (A <> B).
      intro.
      subst B.
      Col.
    分离合取式.
    repeat split.
      intro.
      apply H4.
      apply 等价共线CAB.
      apply (共线的传递性5 C D); Col.
      intro.
      apply H5.
      apply 等价共线CAB.
      apply (共线的传递性5 C D); Col.
    ex_and H6 T.
    exists T.
    split.
      eapply 共线的传递性4.
        apply H.
        apply 等价共线BCA.
        assumption.
        assumption.
      assumption.
    assumption.
Qed.


Lemma out_out_two_sides : forall A B X Y U V I,
  A <> B ->
  TS A B X Y ->
  Col I A B -> Col I X Y ->
  Out I X U -> Out I Y V ->
  TS A B U V.
Proof.
    intros.
    unfold TS in *.
    assert (~ Col X A B).
      分离合取式.
      assumption.
    分离合取式.
    repeat split.
      intro.
      apply H5.
      unfold Out in H3.
      分离合取式.
      induction H10.
      ColR.
      ColR.
      intro.
      apply H6.
      unfold Out in H4.
      分离合取式.
      induction H10.
      ColR.
      ColR.
    ex_and H7 T.
    assert (I = T).
     {
      apply l6_21_两线交点的唯一性 with A B X Y; Col.
      intro; treat_equalities; Col.
      }
    subst I.
    exists T.
    split.
      assumption.
    apply bet_out_out_bet with X Y; assumption.
Qed.

Lemma l9_4_2_aux : forall P Q A C R S U V, Le S C R A -> TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> Out R U A -> Out S V C -> TS P Q U V.
Proof.
    intros.
    induction (两点重合的决定性 R S).
      subst S.
      assert (TT:= H0).
      unfold TS in H0.
      assert (~ Col A P Q).
        分离合取式.
        assumption.
      分离合取式.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H9 T.
      induction (两点重合的决定性 R T).
        subst T.
        clear H9 H3.
        apply (out_out_two_sides P Q A C U V R); auto using l6_6, 中间性蕴含共线1 with col.
      assert (Perp R T A R) by (eapply 与垂线共线之线也为垂线2  with P Q;Col).
      apply L形垂直转垂直于 in H12.
      apply 垂直于的交换性 in H12.
      eapply L形垂直于转直角 in H12.
      assert (Perp R T C R) by (eapply 与垂线共线之线也为垂线2  with P Q;Col).
      apply L形垂直转垂直于 in H13.
      apply 垂直于的交换性 in H13.
      eapply L形垂直于转直角 in H13.
      assert (R = T).
        apply (l8_6 C R T A).
          apply 直角的对称性;auto.
          apply 直角的对称性;auto.
        Between.
      subst.
      intuition.
    (********* R <> S ***************)
    assert(P <> Q).
      apply 垂直推出不重合 in H4.
      分离合取式.
      assumption.
    assert (TS R S A C).
      eapply (col_preserves_two_sides P Q).
        apply H7.
        apply 等价共线BCA.
        assumption.
        apply 等价共线BCA.
        assumption.
      assumption.
    eapply (col_preserves_two_sides R S).
      assumption.
      eapply 等价共线BCA.
      eapply 共线的传递性2.
        apply H8.
        apply 等价共线BCA.
        assumption.
      apply 等价共线BCA.
      assumption.
      apply 等价共线BCA.
      eapply (共线的传递性2 _ P).
        auto.
        apply 等价共线CBA.
        assumption.
      apply 等价共线CBA.
      assumption.
    assert (Perp R S A R).
      eapply 与垂线共线之线也为垂线2.
        apply H2.
        assumption.
        apply 等价共线BCA.
        assumption.
        apply 等价共线BCA.
        assumption.
    assert (Perp R S C S).
      eapply 与垂线共线之线也为垂线2.
        apply H4.
        assumption.
        apply 等价共线BCA.
        assumption.
        apply 等价共线BCA.
        assumption.
    assert (HH9:=H9).
    unfold TS in HH9.
    assert (~ Col A R S).
      分离合取式.
      assumption.
    分离合取式.
    ex_and H15 T.
    unfold Le in H.
    ex_and H C'.
    assert (exists M, 中点 M S R /\ 中点 M C C').
      eapply (四点成双垂直S形则存在一点平分两对角线 S R C A C' T).
        apply 垂直的对称性.
        apply 垂直的左交换性.
        assumption.
        apply 垂直的对称性.
        apply 垂直的左交换性.
        assumption.
        apply 等价共线CBA.
        assumption.
        apply 中间性的对称性.
        assumption.
        assumption.
      assumption.
    ex_and H18 M.
    double U M U'.
    assert (R <> U).
      intro.
      subst U.
      unfold Out in H5.
      分离合取式.
      absurde.
    assert (TS R S U U').
      eapply mid_two_sides.
        apply M是AB中点则M是BA中点.
        apply H18.
        intro.
        apply H13.
        eapply 等价共线CAB.
        eapply 共线的传递性2.
          apply H21.
          apply 等价共线ACB.
          assumption.
        induction H5.
        分离合取式.
        induction H24.
          unfold Col.
          left.
          assumption.
        unfold Col.
        right; left.
        apply 中间性的对称性.
        assumption.
      assumption.
    apply l9_2.
    eapply l9_3.
      apply l9_2.
      apply H22.
      unfold Col.
      right; right.
      apply midpoint_bet.
      apply H18.
      apply M是AB中点则M是BA中点.
      assumption.
      apply ABA型共线.
    assert (forall X Y, 中点 M X Y -> (Out R X A <-> Out S C Y)).
      eapply l9_4_1.
        apply H9.
        apply AAB型共线.
        assumption.
        apply ABA型共线.
        assumption.
      apply M是AB中点则M是BA中点.
      assumption.
    assert (Out R U A <-> Out S C U').
      eapply H23.
      assumption.
    destruct H24.
    eapply l6_7.
      apply l6_6.
      apply H24.
      assumption.
    apply l6_6.
    assumption.
Qed.


Lemma l9_4_2 : forall P Q A C R S U V,
TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> Out R U A -> Out S V C -> TS P Q U V.
Proof.
    intros.
    assert(Le S C R A \/ Le R A S C) by (apply 长度小于等于的决定性).
    induction H6.
      eapply l9_4_2_aux with A C R S;assumption.
    apply l9_2.
    apply l9_2 in H.
    eapply l9_4_2_aux with C A S R;auto.
Qed.

Lemma l9_5 : forall P Q A C R B,
 TS P Q A C -> Col R P Q -> Out R A B -> TS P Q B C.
Proof.
    intros.
    assert (P <> Q).
      unfold TS in H.
      分离合取式.
      intro.
      subst Q.
      Col.
    assert(exists A0, Col P Q A0 /\ Perp P Q A A0).
      eapply l8_18_过一点垂线之垂点的存在性.
      intro.
      unfold TS in H.
      分离合取式.
      apply H.
      apply 等价共线CAB.
      assumption.
    assert(exists C0, Col P Q C0 /\ Perp P Q C C0).
      eapply l8_18_过一点垂线之垂点的存在性.
      unfold TS in H.
      分离合取式.
      intro.
      apply H4.
      apply 等价共线CAB.
      assumption.
    assert(exists B0, Col P Q B0 /\ Perp P Q B B0).
      eapply l8_18_过一点垂线之垂点的存在性.
      assert (HH1:=H1).
      unfold Out in HH1.
      unfold TS in H.
      分离合取式.
      intro.
      assert (Col P B R).
        eapply 共线的传递性2.
          apply H2.
          assumption.
        apply 等价共线BCA.
        assumption.
      assert (R <> B).
        intro.
        subst B.
        absurde.
      assert(Col R P A ).
        eapply 共线的传递性2.
          apply H12.
          eapply 等价共线CBA.
          assumption.
        apply 等价共线ACB.
        apply out_col.
        assumption.
      apply H.
      ColR.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H5 B'.
    assert (exists M, 中点 M A' C').
      apply 中点的存在性.
    ex_and H9 M.
    double A M D.
    assert (Out C' D C <-> Out A' A A).
      eapply l9_4_1.
        apply l9_2.
        apply H.
        apply 等价共线CAB.
        assumption.
        assumption.
        apply 等价共线CAB.
        assumption.
        assumption.
        apply M是AB中点则M是BA中点.
        apply H10.
      apply M是AB中点则M是BA中点.
      assumption.
    destruct H11.
    assert (Out C' D C).
      apply H12.
      unfold Out.
      repeat split.
        intro.
        subst A'.
        apply 垂直推出不重合 in H6.
        分离合取式.
        absurde.
        intro.
        subst A'.
        apply 垂直推出不重合 in H6.
        分离合取式.
        absurde.
      left.
      apply ABB中间性.
    assert (TS P Q A D).
      eapply l9_4_2.
        apply H.
        apply 等价共线CAB.
        apply H3.
        assumption.
        apply 等价共线CAB.
        apply H4.
        apply H7.
        unfold Out.
        repeat split.
          intro.
          subst A'.
          apply 垂直推出不重合 in H6.
          分离合取式.
          absurde.
          intro.
          subst A'.
          apply 垂直推出不重合 in H6.
          分离合取式.
          absurde.
        left.
        apply ABB中间性.
      assumption.
    assert (TS P Q B D).
      apply l9_3 with A M R; trivial.
      induction (两点重合的决定性 A' C').
        subst C'.
        apply M是AA中点则M与A重合 in H10.
        subst A'.
        apply 等价共线CAB.
        assumption.
      ColR.
    apply l9_4_2 with B D B' C'; Col.
      apply 垂直的对称性.
      apply 垂直的左交换性.
      eapply 垂线共线点也构成垂直1.
        intro.
        subst D.
        unfold Out in H13.
        分离合取式.
        absurde.
        apply 垂直的对称性.
        apply 垂直的右交换性.
        apply H7.
      apply 等价共线ACB.
      apply out_col.
      assumption.
      apply out_trivial.
      intro.
      subst B.
      apply 垂直推出不重合 in H8.
      分离合取式.
      absurde.
    apply l6_6.
    assumption.
Qed.

(** This lemma used to be an axiom in previous versions of Tarski's axiom system.
    It is a been shown to a theorem by Gupta in his Phd 1965. *)
(** This corresponds to l9_6 in Tarski's book. *)

Lemma outer_pasch : forall A B C P Q,
 Bet A C P -> Bet B Q C -> exists X, Bet A X B /\ Bet P Q X.
Proof.
    intros.
    induction(共线的决定性 P Q C).
      induction(中间性的决定性 P Q C).
        exists A.
        split.
          Between.
        eapply 中间性的交换传递性2 with C;Between.
      assert (Out Q P C) by (apply l6_4_2;auto).
      exists B.
      split.
        Between.
      unfold Out in H3.
      分离合取式.
      induction H5.
        apply 中间性的交换传递性1 with C;Between.
      apply 中间性的外传递性1 with C;Between.
    induction (两点重合的决定性 B Q).
      subst Q;exists B;Between.
    show_distinct A P.
      intuition.
    show_distinct P Q.
      intuition.
    show_distinct P B.
      intuition.
    assert(TS P Q C B).
      unfold TS.
      repeat split.
        Col.
        assert_cols.
        intro;apply H1; ColR.
      exists Q; split;Col;Between.
    统计不重合点.
    assert (TS P Q A B) by (apply l9_5 with C P;unfold Out;intuition).
    unfold TS in H8.
    分离合取式.
    ex_and H11 X.
    exists X.
    split.
      assumption.
    assert (exists T, Bet X T P /\ Bet C T B) by (apply 帕施公理 with A;Between).
    ex_and H14 T.
    show_distinct B C.
      intuition.
    assert (T = Q).
      apply l6_21_两线交点的唯一性 with X P B C; Col.
      intro.
      apply H10.
      eapply 等价共线CAB.
      apply 共线的传递性2 with X.
        intro.
        treat_equalities.
        apply H10.
        ColR.
        Col.
      Col.
    subst T;Between.
Qed.

Lemma os_distincts : forall A B X Y, OS A B X Y ->
  A <> B /\ A <> X /\ A <> Y /\ B <> X /\ B <> Y.
Proof.
  intros A B P Q HOS.
  destruct HOS as [Z [HTS1 HTS2]].
  apply ts_distincts in HTS1.
  apply ts_distincts in HTS2.
  分离合取式.
  repeat split; auto.
Qed.

Lemma invert_one_side : forall A B P Q,
 OS A B P Q -> OS B A P Q.
Proof.
    unfold OS.
    intros.
    ex_and H T.
    exists T.
    split; apply invert_two_sides; assumption.
Qed.

Lemma l9_8_1 : forall P Q A B C, TS P Q A C -> TS P Q B C -> OS P Q A B.
Proof.
    intros.
    unfold OS.
    exists C.
    split; assumption.
Qed.

Lemma not_two_sides_id : forall A P Q, ~ TS P Q A A.
Proof.
    intros.
    intro.
    unfold TS in H.
    分离合取式.
    ex_and H1 T.
    apply 中间性的同一律 in H2.
    subst T.
    apply H0.
    apply H1.
Qed.

Lemma l9_8_2 : forall P Q A B C,
 TS P Q A C ->
 OS P Q A B ->
 TS P Q B C.
Proof.
    intros.
    unfold OS in H0.
    ex_and H0 D.
    assert (HH:= H).
    assert (HH0:=H0).
    assert (HH1:=H1).
    unfold TS in HH1.
    assert (P <> Q).
      intro.
      subst Q.
      分离合取式.
      Col.
    分离合取式.
    unfold TS in HH0.
    assert (P <> Q).
      intro.
      subst Q.
      分离合取式.
      Col.
    分离合取式.
    unfold TS in HH.
    assert (P <> Q).
      intro.
      subst Q.
      分离合取式.
      Col.
    分离合取式.
    ex_and H13 T.
    ex_and H9 X.
    ex_and H5 Y.
    assert (exists M , Bet Y M A /\ Bet X M B).
      eapply 帕施公理.
        apply H16.
      apply H15.
    ex_and H17 M.
    assert (A <> D).
      intro.
      subst D.
      apply not_two_sides_id in H0.
      assumption.
    assert (B <> D).
      intro.
      subst D.
      apply not_two_sides_id in H1.
      assumption.
    induction (共线的决定性 A B D).
      induction (两点重合的决定性 M Y).
        subst M.
        assert (X = Y).
          apply l6_21_两线交点的唯一性 with P Q A D; Col; ColR.
        subst Y.
        eapply l9_5.
          apply H.
          apply H9.
        unfold Out.
        repeat split.
          intro.
          subst X.
          apply H11.
          assumption.
          intro.
          subst X.
          apply H3.
          assumption.
        unfold Col in H21.
        induction H21.
          right.
          eapply 中间性的交换传递性1.
            apply 中间性的对称性.
            apply H16.
          apply 中间性的对称性.
          assumption.
        induction H21.
          assert (Bet D B A \/ Bet D A B).
            eapply (l5_1 _ X).
              intro.
              subst X.
              apply H4.
              assumption.
              apply 中间性的对称性.
              assumption.
            apply 中间性的对称性.
            assumption.
          induction H22.
            assert (D = B).
              eapply 双中间性推出点重合.
                apply H22.
              apply H21.
            subst D.
            absurde.
          assert (D = A).
            eapply 双中间性推出点重合.
              apply H22.
            apply 中间性的对称性.
            assumption.
          subst D.
          absurde.
        eapply (l5_2 D).
          intro.
          subst X.
          apply H8.
          assumption.
          apply 中间性的对称性.
          assumption.
        apply 中间性的对称性.
        assumption.
      induction (两点重合的决定性 M X).
        subst M.
        assert (X = Y).
          apply l6_21_两线交点的唯一性 with P Q A D; Col; ColR.
        subst Y.
        absurde.
      eapply (l9_5 _ _ M _ X).
        eapply l9_5.
          apply H.
          apply H5.
        unfold Out.
        repeat split.
          intro.
          subst Y.
          apply 中间性的同一律 in H17.
          subst M.
          absurde.
          assumption.
        right.
        assumption.
        assumption.
      unfold Out.
      assert (Out Y M  A).
        unfold Out.
        repeat split.
          assumption.
          intro.
          subst Y.
          apply H11.
          assumption.
        left.
        assumption.
      repeat split.
        assumption.
        intro.
        subst X.
        apply 中间性的同一律 in H18.
        subst M.
        absurde.
      left.
      apply H18.
    eapply (l9_5 _ _ M).
      eapply l9_5.
        apply H.
        apply H5.
      unfold Out.
      repeat split.
        intro.
        subst Y.
        apply H7.
        assumption.
        intro.
        subst Y.
        assert(Col B D X).
          eapply (共线的传递性2 _ M).
            intro.
            subst M.
            apply H3.
            assumption.
            unfold Col.
            left.
            assumption.
          unfold Col.
          left.
          apply 中间性的对称性.
          assumption.
        apply H21.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ X).
          intro.
          subst X.
          apply H4.
          assumption.
          unfold Col.
          left.
          apply 中间性的对称性.
          assumption.
        apply 等价共线BCA.
        assumption.
      right.
      assumption.
      apply H9.
    unfold Out.
    repeat split.
      intro.
      subst X.
      assert (Col A D Y).
        eapply (共线的传递性2 _ M).
          intro.
          subst M.
          apply H7.
          assumption.
          unfold Col.
          left.
          assumption.
        unfold Col.
        left.
        apply 中间性的对称性.
        assumption.
      apply H21.
      apply 等价共线BCA.
      eapply (共线的传递性2 _ Y).
        intro.
        subst Y.
        apply H4.
        assumption.
        apply 等价共线BCA.
        assumption.
      unfold Col.
      left.
      apply 中间性的对称性.
      assumption.
      intro.
      subst X.
      apply H3.
      assumption.
    left.
    assumption.
Qed.

Lemma l9_9 : forall P Q A B, TS P Q A B -> ~ OS P Q A B.
Proof.
    intros.
    intro.
    apply (l9_8_2 P Q A B B ) in H.
      apply not_two_sides_id in H.
      assumption.
    assumption.
Qed.

Lemma l9_9_bis : forall P Q A B, OS P Q A B -> ~ TS P Q A B.
Proof.
    intros.
    intro.
    unfold OS in H.
    ex_and H C.
    assert (OS P Q A B).
      eapply l9_8_1.
        apply H.
      assumption.
    assert (~ OS P Q A B).
      apply l9_9.
      assumption.
    contradiction.
Qed.

Lemma one_side_chara : forall P Q A B,
 OS P Q A B -> (forall X, Col X P Q -> ~ Bet A X B).
Proof.
    intros.
    assert(~ Col A P Q).
      destruct H as [R [[] _]]; assumption.
    assert(~ Col B P Q).
      destruct H as [R [_ []]]; assumption.
    apply l9_9_bis in H.
    intro.
    apply H.
    unfold TS.
    repeat split.
      assumption.
      assumption.
    exists X.
    intuition.
Qed.

Lemma l9_10 : forall P Q A,
 ~ Col A P Q -> exists C, TS P Q A C.
Proof.
    intros.
    double A P A'.
    exists A'.
    unfold TS.
    repeat split.
      assumption.
      intro.
      apply H.
      eapply 等价共线CAB.
      eapply (共线的传递性2 _ A').
        intro.
        subst A'.
        apply M是AB中点则M是BA中点 in H0.
        eapply A是AB中点则A与B重合 in H0.
        subst A.
        apply H.
        assumption.
        apply 等价共线BAC.
        assumption.
      unfold Col.
      right; right.
      apply midpoint_bet.
      assumption.
    exists P.
    split.
      apply AAB型共线.
    apply midpoint_bet.
    assumption.
Qed.



Lemma one_side_reflexivity : forall P Q A,
 ~ Col A P Q -> OS P Q A A.
Proof.
    intros.
    unfold OS.
    double A P C.
    exists C.
    assert (TS P Q A C).
      repeat split.
        assumption.
        intro.
        apply H.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ C).
          intro.
          subst C.
          apply M是AB中点则M是BA中点 in H0.
          apply A是AB中点则A与B重合 in H0.
          subst A.
          apply H.
          assumption.
          apply 等价共线BAC.
          assumption.
        unfold Col.
        right; right.
        apply midpoint_bet.
        assumption.
      exists P.
      split.
        apply AAB型共线.
      apply midpoint_bet.
      assumption.
    split; assumption.
Qed.


Lemma one_side_symmetry : forall P Q A B,
 OS P Q A B -> OS P Q B A.
Proof.
    unfold OS.
    intros.
    ex_and H C.
    exists C.
    split; assumption.
Qed.

Lemma one_side_transitivity : forall P Q A B C,
OS P Q A B -> OS P Q B C -> OS P Q A C.
Proof.
    intros.
    unfold OS in *.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    split.
      assumption.
    apply l9_2.
    eapply l9_8_2.
      apply l9_2.
      apply H2.
    eapply l9_8_1.
      apply l9_2.
      apply H0.
    apply l9_2.
    assumption.
Qed.

Lemma l9_17 : forall A B C P Q, OS P Q A C -> Bet A B C -> OS P Q A B.
Proof.
    intros.
    induction (两点重合的决定性 A C).
      subst C.
      apply 中间性的同一律 in H0.
      subst B.
      assumption.
    assert( HH:= H).
    unfold OS in H.
    ex_and H D.
    assert(HH1:=H).
    unfold TS in H2.
    assert (P <> Q).
      intro.
      subst Q.
      分离合取式.
      Col.
    分离合取式.
    unfold TS in H.
    assert (P <> Q).
      intro.
      subst Q.
      分离合取式.
      Col.
    分离合取式.
    ex_and H8 X.
    ex_and H5 Y.
    assert (exists T,  Bet B T D /\ Bet X T Y).
      eapply l3_17_三中间性推交点存在性.
        apply H9.
        apply H10.
      assumption.
    ex_and H11 T.
    unfold OS.
    exists D.
    split.
      assumption.
    unfold TS.
    repeat split.
      apply l9_9_bis in HH.
      intro.
      apply HH.
      unfold TS.
      repeat split.
        assumption.
        assumption.
      exists B.
      split.
        assumption.
      assumption.
      unfold TS in HH1.
      分离合取式.
      assumption.
    exists T.
    induction (共线的决定性 A C D).
      assert (X = Y).
        apply l6_21_两线交点的唯一性 with P Q A D; Col.
          intro.
          subst D.
          assert (OS P Q A A).
            apply one_side_reflexivity.
            assumption.
          apply l9_9_bis in H14.
          contradiction.
          apply 等价共线CAB.
          apply (共线的传递性2 _ C).
            intro.
            subst D.
            apply 中间性的同一律 in H10.
            subst Y.
            apply H4.
            assumption.
            Col.
            Col.
      subst Y.
      apply 中间性的同一律 in H12.
      subst X.
      split.
        assumption.
      assumption.
    split.
      assert (X <> Y).
        intro.
        subst Y.
        apply 中间性的同一律 in H12.
        subst X.
        apply H13.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ T).
          intro.
          subst D.
          contradiction.
          unfold Col.
          left.
          apply 中间性的对称性.
          assumption.
        unfold Col.
        left.
        apply 中间性的对称性.
        assumption.
      apply 等价共线CAB.
      apply (共线的传递性5 X Y); Col.
    assumption.
Qed.

Lemma l9_18 : forall X Y A B P,
 Col X Y P -> Col A B P -> (TS X Y A B <-> (Bet A P B /\ ~Col X Y A /\ ~Col X Y B)).
Proof.
    intros.
    split.
      intros.
      unfold TS in H1.
      分离合取式.
      assert (X <> Y).
        intro.
        subst Y.
        分离合取式.
        Col.
      ex_and H3 T.
      assert (P=T).
        apply l6_21_两线交点的唯一性 with X Y A B; Col.
        intro.
        subst B.
        apply 中间性的同一律 in H5.
        subst A.
        contradiction.
      subst T.
      repeat split; Col.
    intro.
    unfold TS.
    分离合取式.
    repeat split; Col.
    exists P.
    split.
      apply 等价共线CAB.
      assumption.
    assumption.
Qed.

Lemma l9_19 : forall X Y A B P ,
 Col X Y P -> Col A B P -> (OS X Y A B <-> (Out P A B /\ ~Col X Y A)).
Proof.
    intros.
    split.
      intro.
      assert (HH2:=H1).
      unfold OS in H1.
      ex_and H1 D.
      unfold TS in H2.
      assert (~ Col B X Y).
        分离合取式.
        assumption.
      分离合取式.
      clear H3.
      assert (X <> Y).
        intro.
        subst Y.
        分离合取式.
        Col.
      unfold TS in H1.
      分离合取式.
      ex_and H5 M.
      ex_and H7 N.
      split.
        unfold Out.
        repeat split.
          intro.
          subst P.
          apply H1.
          apply 等价共线CAB.
          assumption.
          intro.
          subst P.
          apply H2.
          apply 等价共线CAB.
          assumption.
        unfold Col in H0.
        induction H0.
          right.
          apply 中间性的对称性.
          assumption.
        induction H0.
          apply False_ind.
          assert (TS X Y A B).
            unfold TS.
            repeat split.
              assumption.
              assumption.
            exists P.
            split.
              apply 等价共线CAB.
              assumption.
            apply 中间性的对称性.
            assumption.
          apply l9_9_bis in HH2.
          contradiction.
        left.
        assumption.
      intro.
      apply H1.
      Col.
    intros.
    分离合取式.
    assert (exists D, TS X Y A D).
      apply l9_10.
      intro.
      apply H2.
      apply 等价共线BCA.
      assumption.
    ex_elim H3 D.
    unfold OS.
    exists D.
    split.
      assumption.
    eapply l9_5.
      apply H4.
      apply 等价共线CAB.
      apply H.
    assumption.
Qed.

Lemma one_side_not_col123 :
 forall A B X Y,
  OS A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold OS in H.
    ex_and H C.
    unfold TS in *.
    分离合取式.
    intro.
    apply H.
    apply 等价共线CAB.
    assumption.
Qed.

Lemma one_side_not_col124 :
 forall A B X Y,
  OS A B X Y ->
  ~ Col A B Y.
Proof.
  intros A B X Y HOS.
  apply one_side_not_col123 with X.
  apply one_side_symmetry, HOS.
Qed.

Lemma col_two_sides : forall A B C P Q,
 Col A B C -> A <> C -> TS A B P Q ->
 TS A C P Q.
Proof.
    intros.
    unfold TS in *.
    分离合取式.
    ex_and H3 T.
    repeat split.
      intro.
      apply H1.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H0.
        apply 等价共线ACB.
        assumption.
      apply 等价共线BCA.
      assumption.
      intro.
      apply H2.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H0.
        apply 等价共线ACB.
        assumption.
      apply 等价共线BCA.
      assumption.
    exists T.
    split.
      apply 等价共线CAB.
      apply 共线的传递性2 with B.
        intro.
        subst B.
        Col.
        assumption.
      apply 等价共线BCA.
      assumption.
    assumption.
Qed.

Lemma col_one_side : forall A B C P Q,
  Col A B C -> A <> C -> OS A B P Q -> OS A C P Q.
Proof.
    unfold OS.
    intros.
    ex_and H1 T.
    exists T.
    split; eapply (col_two_sides _ B); assumption.
Qed.

Lemma out_out_one_side :
 forall A B X Y Z,
  OS A B X Y ->
  Out A Y Z ->
  OS A B X Z.
Proof.
    intros.
    assert (A <> B).
      unfold OS in H.
      ex_and H C.
      unfold TS in H.
      分离合取式.
      intro.
      subst B.
      Col.
    prolong Y A Y' A Y.
    assert(OS A B Y Z).
      unfold OS.
      exists Y'.
      split.
        unfold TS.
        repeat split.
          apply one_side_symmetry in H.
          eapply one_side_not_col123 in H.
          intro.
          apply H.
          apply 等价共线BCA.
          assumption.
          intro.
          apply one_side_symmetry in H.
          eapply one_side_not_col123 in H.
          apply H.
          assert(Col A B Y).
            eapply (共线的传递性2 _ Y').
              intro.
              subst Y'.
              apply 等长的对称性 in H3.
              apply 等长的同一性 in H3.
              subst Y.
              unfold Out in H0.
              分离合取式.
              absurde.
              apply 等价共线BAC.
              assumption.
            unfold Col.
            right; right.
            assumption.
          assumption.
        exists A.
        split.
          apply AAB型共线.
        assumption.
      unfold TS.
      repeat split.
        intro.
        apply one_side_symmetry in H.
        eapply one_side_not_col123 in H.
        apply H.
        eapply (共线的传递性2 _ Z).
          intro.
          subst Z.
          unfold Out in H0.
          分离合取式.
          absurde.
          apply 等价共线BAC.
          assumption.
        apply out_col in H0.
        apply 等价共线ACB.
        assumption.
        apply one_side_symmetry in H.
        eapply one_side_not_col123 in H.
        intro.
        apply H.
        eapply (共线的传递性2 _ Y').
          intro.
          subst Y'.
          apply 等长的对称性 in H3.
          apply 等长的同一性 in H3.
          subst Y.
          apply H.
          apply ABA型共线.
          apply 等价共线BAC.
          assumption.
        unfold Col.
        right; right.
        assumption.
      exists A.
      split.
        apply AAB型共线.
      unfold Out in H0.
      分离合取式.
      induction H5.
        apply 中间性的对称性.
        eapply 中间性的外传递性2.
          apply 中间性的对称性.
          apply H2.
          assumption.
        auto.
      apply 中间性的对称性.
      eapply 中间性的内传递性1.
        apply 中间性的对称性.
        apply H2; 分离合取式.
      assumption.
    eapply one_side_transitivity.
      apply H.
    apply H4.
Qed.

Lemma out_one_side : forall A B X Y, (~ Col A B X \/ ~ Col A B Y) -> Out A X Y -> OS A B X Y.
Proof.
    intros.
    induction H.
      assert(~ Col X A B).
        intro.
        apply H.
        apply 等价共线BCA.
        assumption.
      assert(HH:=one_side_reflexivity A B X H1).
      apply (out_out_one_side _ _ _ _ _ HH H0).
    assert(~ Col Y A B).
      intro.
      apply H.
      apply 等价共线BCA.
      assumption.
    assert(HH:=one_side_reflexivity A B Y H1).
    apply one_side_symmetry.
    apply (out_out_one_side _ _ _ _ _ HH).
    apply l6_6.
    assumption.
Qed.

Lemma bet__ts : forall A B X Y, A <> Y -> ~ Col A B X -> Bet X A Y -> TS A B X Y.
Proof.
  intros A B X Y HAY HNCol HBet.
  repeat split; Col.
    intro; apply HNCol, 共线的传递性2 with Y; Col.
  exists A; split; Col.
Qed.

Lemma bet_ts__ts : forall A B X Y Z, TS A B X Y -> Bet X Y Z -> TS A B X Z.
Proof.
  intros A B X Y Z [HNCol1 [HNCol2 [T [HT1 HT2]]]] HBet.
  repeat split; trivial.
    intro; assert (Z = T); [apply (l6_21_两线交点的唯一性 A B X Y); Col; intro|]; treat_equalities; auto.
  exists T; split; eBetween.
Qed.

Lemma bet_ts__os : forall A B X Y Z, TS A B X Y -> Bet X Y Z -> OS A B Y Z.
Proof.
  intros A B X Y Z HTS HBet.
  exists X; split; apply l9_2; trivial.
  apply bet_ts__ts with Y; assumption.
Qed.

Lemma l9_31 :
 forall A X Y Z,
  OS A X Y Z ->
  OS A Z Y X ->
  TS A Y X Z.
Proof.
    intros.
    assert(A <> X /\ A <> Z /\ ~ Col Y A X  /\ ~ Col Z A X /\ ~Col Y A Z).
      unfold OS in *.
      ex_and H C.
      ex_and H0 D.
      unfold TS in *.
      分离合取式.
      split.
        intro.
        subst X.
        Col.
      split.
        intro.
        subst Z.
        Col.
      repeat split; assumption.
    分离合取式.
    prolong Z A Z' Z A.
    assert(Z' <> A).
      intro.
      subst Z'.
      apply 等长的对称性 in H7.
      apply 等长的同一性 in H7.
      subst Z.
      absurde.
    assert(TS A X Y Z').
      eapply (l9_8_2 _ _ Z).
        unfold TS.
        repeat split.
          assumption.
          intro.
          apply H4.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ Z').
            auto.
            apply 等价共线BAC.
            assumption.
          apply 等价共线BCA.
          apply 中间性蕴含共线1.
          assumption.
        exists A.
        split.
          apply AAB型共线.
        assumption.
      apply one_side_symmetry.
      assumption.
    unfold TS in H9.
    assert (~ Col Y A X).
      分离合取式.
      assumption.
    分离合取式.
    ex_and H12 T.
    assert(T <> A).
      intro.
      subst T.
      apply H5.
      apply 等价共线CAB.
      eapply (共线的传递性2 _ Z').
        auto.
        apply 等价共线BCA.
        apply 中间性蕴含共线1.
        assumption.
      apply 等价共线BCA.
      apply 中间性蕴含共线1.
      assumption.
    assert(OS Y A Z' T).
      eapply out_one_side.
        left.
        intro.
        apply H5.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ Z').
          auto.
          apply 中间性蕴含共线1 in H6.
          apply 等价共线BCA.
          assumption.
        apply 等价共线BCA.
        assumption.
      apply l6_6.
      apply bet_out.
        intro.
        subst T.
        contradiction.
      assumption.
    unfold Col in H12.
    induction H12.
      assert(OS Z' Z Y T).
        apply out_one_side.
          left.
          intro.
          apply H5.
          eapply 等价共线BCA.
          eapply (共线的传递性2 _ Z').
            intro.
            subst Z'.
            apply 中间性的同一律 in H6.
            subst Z.
            apply H4.
            apply AAB型共线.
            apply 等价共线BAC.
            assumption.
          apply 中间性蕴含共线1 in H6.
          apply 等价共线ACB.
          assumption.
        apply l6_6.
        apply bet_out.
          intro.
          subst T.
          apply H11.
          apply 中间性蕴含共线1.
          assumption.
        apply 中间性的对称性.
        assumption.
      assert(OS A Z Y T).
        apply invert_one_side.
        eapply (col_one_side _ Z').
          apply 中间性蕴含共线1 in H6.
          apply 等价共线ACB.
          assumption.
          auto.
        apply invert_one_side.
        assumption.
      assert(TS A Z X T).
        repeat split.
          intro.
          apply H11.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ Z).
            assumption.
            apply 等价共线BCA.
            assumption.
          apply 中间性蕴含共线1 in H6.
          apply 等价共线BAC.
          assumption.
          unfold OS in H17.
          ex_and H17 C.
          unfold TS in H18.
          分离合取式.
          assumption.
        exists A.
        split.
          apply AAB型共线.
        apply 中间性的对称性.
        assumption.
      assert(TS A Z Y X).
        eapply l9_8_2.
          eapply l9_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      apply l9_9 in H19.
      contradiction.
    assert(OS A Z T X).
      apply out_one_side.
        right.
        intro.
        apply H4.
        apply 等价共线BAC.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply 中间性的对称性.
      assumption.
    assert(TS A Y Z' Z).
      repeat split.
        unfold OS in H5.
        ex_and H15 C.
        unfold TS in H15.
        分离合取式.
        intro.
        apply H15.
        apply 等价共线ACB.
        assumption.
        intro.
        apply H5.
        apply 等价共线CBA.
        assumption.
      exists A.
      split.
        apply AAB型共线.
      apply 中间性的对称性.
      assumption.
    assert(OS A Y T X).
      apply out_one_side.
        left.
        unfold OS in H15.
        ex_and H15 C.
        unfold TS in H18.
        分离合取式.
        intro.
        apply H18.
        apply 等价共线CBA.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply 中间性的对称性.
      assumption.
    apply invert_one_side in H15.
    assert (OS A Y Z' X).
      eapply one_side_transitivity.
        apply H15.
      assumption.
    eapply l9_8_2.
      apply H17.
    assumption.
Qed.

Lemma col123__nos : forall A B P Q, Col P Q A -> ~ OS P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (~ Col P Q A) by (apply (one_side_not_col123 P Q A B); auto).
  auto.
Qed.

Lemma col124__nos : forall A B P Q, Col P Q B -> ~ OS P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (HN : ~ OS P Q B A) by (apply col123__nos; auto).
  apply HN; apply one_side_symmetry; auto.
Qed.

Lemma col2_os__os : forall A B C D X Y, C <> D -> Col A B C ->
   Col A B D -> OS A B X Y -> OS C D X Y.
Proof.
  intros A B C D X Y HCD HColC HColD Hos.
  destruct Hos as [Z [Hts1 Hts2]].
  exists Z.
  split; apply (col_preserves_two_sides A B); auto.
Qed.

Lemma os_out_os : forall A B C D C' P , Col A B P -> OS A B C D -> Out P C C' -> OS A B C' D.
Proof.
    intros.
    assert(A <> B /\ ~ Col C A B).
      unfold OS in H0.
      ex_and H0 T.
      unfold TS in H0.
      分离合取式.
      split.
        intro.
        subst B.
        Col.
      assumption.
    分离合取式.
    prolong C P T C P.
    assert(P <> T).
      intro.
      subst T.
      treat_equalities.
      Col.
    assert(TS A B C T).
      unfold TS.
      repeat split; Col.
        intro.
        apply H3.
        assert_cols. ColR.
      exists P.
      split; Col.
    assert(TS A B T C').
      apply 中间性蕴含共线1 in H4.
      eapply (out_out_two_sides _ _ T C _ _ P); Col.
        apply l9_2.
        assumption.
      apply out_trivial.
      auto.
    assert(OS A B C C').
      eapply l9_8_1.
        apply H7.
      apply l9_2.
      assumption.
    eauto using one_side_transitivity, one_side_symmetry.
Qed.

Lemma ts_ts_os : forall A B C D, TS A B C D -> TS C D A B -> OS A C B D.
Proof.
    intros.
    unfold TS in *.
    分离合取式.
    ex_and H4 T1.
    ex_and H2 T.
    assert(T1 = T).
      assert_cols.
      apply (l6_21_两线交点的唯一性 C D A B); Col.
      intro.
      subst B.
      Col.
    subst T1.

assert(OS A C T B).
apply(out_one_side A C T B).
right.
intro.
Col.
unfold Out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst B.
Col.
left.
assumption.

assert(OS C A T D).
apply(out_one_side C A T D).
right.
intro.
apply H0.
Col.
unfold Out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst D.
Col.
left.
assumption.
apply invert_one_side in H8.
apply (one_side_transitivity A C B T).
apply one_side_symmetry.
assumption.
assumption.
Qed.

Lemma two_sides_not_col :
 forall A B X Y,
  TS A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold TS in H.
    分离合取式.
    intro.
    apply H.
    apply 等价共线CAB.
    assumption.
Qed.

Lemma col_one_side_out : forall A B X Y,
 Col A X Y ->
 OS A B X Y ->
 Out A X Y.
Proof.
    intros.
    assert(X <> A /\ Y <> A).
      unfold OS in H0.
      ex_and H0 Z.
      unfold TS in *.
      分离合取式.
      ex_and H5 T0.
      ex_and H3 T1.
      split.
        intro.
        subst X.
        Col.
      intro.
      subst Y.
      Col.
    分离合取式.
    unfold Col in H.
    induction H.
      unfold Out.
      repeat split; try assumption.
      left.
      assumption.
    induction H.
      unfold Out.
      repeat split; try assumption.
      right.
      apply 中间性的对称性.
      assumption.
    assert(TS A B X Y).
      unfold TS.
      assert(HH0 := H0).
      unfold OS in H0.
      ex_and H0 Z.
      unfold TS in *.
      分离合取式.
      repeat split.
        assumption.
        assumption.
      exists A.
      split.
        apply AAB型共线.
      apply 中间性的对称性.
      assumption.
    eapply l9_9 in H3.
    contradiction.
Qed.

Lemma col_two_sides_bet :
 forall A B X Y,
 Col A X Y ->
 TS A B X Y ->
 Bet X A Y.
Proof.
    intros.
    unfold Col in H.
    induction H.
      unfold TS in H0.
      分离合取式.
      ex_and H2 T.
      apply False_ind.
      apply H1.
      apply 等价共线CAB.
      eapply (共线的传递性2 _ T).
        intro.
        subst T.
        assert(A = X).
          eapply 双中间性推出点重合.
            apply H.
          assumption.
        subst X.
        apply H0.
        apply AAB型共线.
        apply 等价共线BAC.
        assumption.
      apply 等价共线BCA.
      eapply (共线的传递性2 _ X).
        intro.
        subst Y.
        apply 中间性的同一律 in H3.
        subst X.
        contradiction.
        apply 中间性蕴含共线1 in H.
        apply 等价共线CBA.
        assumption.
      apply 等价共线CAB.
      apply 中间性蕴含共线1.
      assumption.
    induction H.
      unfold TS in H0.
      分离合取式.
      ex_and H2 T.
      assert(Col Y A T).
        eapply (共线的传递性2 _ X).
          intro.
          subst Y.
          apply 中间性的同一律 in H3.
          subst X.
          contradiction.
          apply 等价共线BAC.
          apply 中间性蕴含共线1.
          assumption.
        apply 等价共线CAB.
        apply 中间性蕴含共线1.
        assumption.
      apply False_ind.
      apply H1.
      apply 等价共线CAB.
      eapply (共线的传递性2 _ T).
        intro.
        subst T.
        assert(A = Y).
          eapply 双中间性推出点重合.
            apply 中间性的对称性.
            apply H.
          apply 中间性的对称性.
          assumption.
        subst Y.
        apply H1.
        apply AAB型共线.
        apply 等价共线BAC.
        assumption.
      apply 等价共线BCA.
      assumption.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma os_ts1324__os : forall A X Y Z,
  OS A X Y Z ->
  TS A Y X Z ->
  OS A Z X Y.
Proof.
  intros A X Y Z Hos Hts.
  destruct Hts as [HNColXY [HNColYZ [P [HColP HPBet]]]].
  apply (one_side_transitivity _ _ _ P).
  - apply invert_one_side.
    apply one_side_symmetry.
    apply one_side_symmetry in Hos.
    apply one_side_not_col123 in Hos.
    apply out_one_side; Col.
    apply bet_out; Between; intro; subst Z; Col.

  - apply out_one_side.
    right; Col.
    apply (col_one_side_out _ X); Col.
    apply one_side_symmetry in Hos.
    apply (one_side_transitivity _ _ _ Z); auto.
    apply invert_one_side.
    apply one_side_not_col123 in Hos.
    apply out_one_side; Col.
    apply bet_out; auto; intro; subst X; Col.
Qed.

Lemma ts2__ex_bet2 : forall A B C D, TS A C B D -> TS B D A C ->
  exists X, Bet A X C /\ Bet B X D.
Proof.
  intros A B C D HTS HTS'.
  destruct HTS as [HNCol [HNCol1 [X [HCol HBet]]]].
  exists X; split; trivial.
  apply col_two_sides_bet with B; trivial.
  统计不重合点.
  apply invert_two_sides, col_two_sides with D; Col.
  intro; subst X; auto.
Qed.

Lemma out_one_side_1 :
 forall A B C D X,
 ~ Col A B C -> Col A B X -> Out X C D ->
 OS A B C D.
Proof.
    intros.
    induction (两点重合的决定性 C D).
      subst D.
      apply one_side_reflexivity.
      intro.
      apply H.
      Col.
    prolong C X C' C X.
    exists C'.
    assert(TS A B C C').
      unfold TS.
      repeat split.
        intro.
        apply H.
        Col.
        intro.
        assert(C'=X).
          eapply (l6_21_两线交点的唯一性 A B C D).
            assumption.
            assumption.
            Col.
            assumption.
            apply out_col in H1.
            eapply (共线的传递性2 _ X).
              intro.
              treat_equalities.
              Col5.
              Col.
            Col.
            Col.
        treat_equalities.
        unfold Out in H1.
        tauto.
      exists X.
      split; Col.
    assert(TS A B D C').
      eapply (l9_5 _ _ _ _ X).
        apply H5.
        Col.
      assumption.
    split; assumption.
Qed.

Lemma out_two_sides_two_sides :
 forall A B X Y P PX,
  A <> PX ->
  Col A B PX ->
  Out PX X P ->
  TS A B P Y ->
  TS A B X Y.
Proof.
    intros.
    assert(OS A B P X).
      eapply (col_one_side _ PX).
        Col.
        unfold TS in H2.
        分离合取式.
        auto.
        intro.
        subst B.
        Col.
      apply invert_one_side.
      apply out_one_side.
        left.
        intro.
        unfold TS in H2.
        分离合取式.
        apply H2.
        ColR.
      apply l6_6.
      assumption.
    eapply l9_8_2.
      apply H2.
    assumption.
Qed.

Lemma 十字上的中间性_bis : forall A B C X Y, X <> Y -> ~ Col C A B -> exists P : Tpoint,
  Cong A P X Y /\ Perp A B P A /\ TS A B C P.
Proof.
intros.
assert (A <> B) by (intro; subst; Col).
assert(HH:= 十字上的中间性 A B C H1).
ex_and HH P.
ex_and H2 T.

assert(TS A B C P).
unfold TS.
repeat split; auto.
intro.
apply L形垂直推出不共线 in H2.
apply H2.
Col.
exists T.
split; Col.
assert(P <> A).
apply 垂直推出不重合 in H2.
tauto.

assert(HH:= 由一点往一方向构造等长线段_2 P A X Y H6).
ex_and HH P'.
exists P'.

assert(Perp A B P' A).
apply 垂直的对称性.
apply 垂直的左交换性.
apply (垂线共线点也构成垂直1 _ P).
intro.
subst P'.
apply 等长的对称性 in H8.
apply 等长的同一性 in H8.
contradiction.
Perp.
induction H7.

apply 中间性蕴含共线1 in H7.
Col.
apply 中间性蕴含共线1 in H7.
Col.

repeat split;auto.
apply L形垂直推出不共线 in H9.
intro.
apply H9.
Col.

assert(OS A B P P').
apply out_one_side.
left.
apply L形垂直推出不共线 in H2.
assumption.
repeat split; auto.
apply 垂直推出不重合 in H9.
tauto.
assert(TS A B C P').
apply l9_2.
apply(l9_8_2 A B P P' C); auto.
apply l9_2.
assumption.
unfold TS in H11.
分离合取式.
ex_and H13 T'.
exists T'.
split; auto.
Qed.

Lemma ts__ncol : forall A B X Y, TS A B X Y -> ~Col A X Y \/ ~Col B X Y.
Proof.
intros.
unfold TS in H.
分离合取式.
ex_and H1 T.

assert(X <> Y).
intro.
treat_equalities.
contradiction.
induction(两点重合的决定性 A T).
treat_equalities.
right.
intro.
apply H.
ColR.
left.
intro.
apply H.
ColR.
Qed.

Lemma one_or_two_sides_aux : forall A B C D X,
 ~ Col C A B -> ~ Col D A B -> Col A C X -> Col B D X ->
 TS A B C D \/ OS A B C D.
Proof.
    intros.
    统计不重合点.
    assert (A <> X) by (intro; subst; Col).
    assert (B <> X) by (intro; subst; Col).
    assert (~ Col X A B) by (intro; apply H; ColR).
    destruct H1 as [|[|]]; destruct H2 as [|[|]].
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply bet_out; auto.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply bet_out; auto.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_8_2 with X.
        repeat split; Col.
        exists B; split; Col.
      apply out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply l6_6, bet_out; Between.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply l6_6, bet_out; Between.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_8_2 with X.
        repeat split; Col.
        exists B; split; Col.
      apply out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_2, l9_8_2 with X.
        repeat split; Col.
        exists A; split; Col.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - left.
      apply l9_2, l9_8_2 with X.
        repeat split; Col.
        exists A; split; Col.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - right.
      exists X; repeat split; Col.
        exists A; split; [Col|Between].
      exists B; split; [Col|Between].
Qed.

Lemma cop__one_or_two_sides :
 forall A B C D, 共面 A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  TS A B C D \/ OS A B C D.
Proof.
    intros.
    ex_and H X.
    induction H2; 分离合取式.
      destruct (or_bet_out C X D) as [|[|]].
        left; repeat split; auto; exists X; split; Col.
        right; apply out_one_side_1 with X; Col.
      exfalso; Col.
    induction H; 分离合取式.
      apply one_or_two_sides_aux with X; assumption.
    induction (one_or_two_sides_aux A B D C X H1 H0 H H2).
      left; apply l9_2; assumption.
    right; apply one_side_symmetry; assumption.
Qed.

Lemma os__coplanar : forall A B C D, OS A B C D -> 共面 A B C D.
Proof.
  intros A B C D HOS.
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D, HOS).
  destruct (由一点往一方向构造等长线段 C B B C) as [C'[]].
  assert (HT : TS A B D C').
  { apply l9_8_2 with C; [|assumption].
    split; [|split].
      Col.
      intro; apply HNCol; ColR.
      exists B; split; Col.
  }
  destruct HT as [HNCol1 [HNCol2 [T []]]].
  assert (C' <> T) by (intro; treat_equalities; auto).
  destruct (共线的决定性 T B C) as [|HNCol3].
    exists B; left; split; ColR.
  destruct (中间性的决定性 T B A) as [|HOut].
  - apply 等价共面DABC, 异侧蕴含共面.
    apply l9_8_2 with T.
      repeat split; Col; exists B; split; Col.
    apply out_one_side_1 with C'; Col.
    apply bet_out; Between.
  - apply 等价共面DACB, 异侧蕴含共面, l9_31; [|apply one_side_symmetry, invert_one_side, HOS].
    apply one_side_transitivity with T.
      apply out_one_side_1 with C'; [intro; apply HNCol3; ColR|Col|apply l6_6, bet_out; Between].
      apply out_one_side; Col; apply not_bet_out; Col.
Qed.

Lemma coplanar_trans_1 : forall P Q R A B,
  ~ Col P Q R -> 共面 P Q R A -> 共面 P Q R B -> 共面 Q R A B.
Proof.
  intros P Q R A B HNCol HCop1 HCop2.
  destruct (共线的决定性 Q R A).
    exists A; left; split; Col.
  destruct (共线的决定性 Q R B).
    exists B; left; split; Col.
  destruct (共线的决定性 Q A B).
    exists Q; left; split; Col.
  assert (HDij : TS Q R A B \/ OS Q R A B).
  { assert (HA : TS Q R P A \/ OS Q R P A) by (apply cop__one_or_two_sides; Col; Cop).
    assert (HB : TS Q R P B \/ OS Q R P B) by (apply cop__one_or_two_sides; Col; Cop).
    destruct HA; destruct HB.
    - right; apply l9_8_1 with P; apply l9_2; assumption.
    - left; apply l9_2, l9_8_2 with P; assumption.
    - left; apply l9_8_2 with P; assumption.
    - right; apply one_side_transitivity with P; [apply one_side_symmetry|]; assumption.
  }
  destruct HDij; [apply 异侧蕴含共面|apply os__coplanar]; assumption.
Qed.

Lemma col_cop__cop : forall A B C D E, 共面 A B C D -> C <> D -> Col C D E -> 共面 A B C E.
Proof.
  intros A B C D E HCop HCD HCol.
  destruct (共线的决定性 D A C).
    assert (Col A C E) by (apply 共线的传递性1 with D; Col); Cop.
  apply 等价共面ACBD, (coplanar_trans_1 D); Cop.
Qed.

Lemma bet_cop__cop : forall A B C D E, 共面 A B C E -> Bet C D E -> 共面 A B C D.
Proof.
  intros A B C D E HCop HBet.
  destruct (两点重合的决定性 C E).
    treat_equalities; apply HCop.
  apply col_cop__cop with E; Col.
Qed.

Lemma col2_cop__cop : forall A B C D E F, 共面 A B C D -> C <> D -> Col C D E -> Col C D F ->
  共面 A B E F.
Proof.
  intros A B C D E F HCop HCD HE HF.
  destruct (两点重合的决定性 E C).
    subst; apply col_cop__cop with D; Col; Cop.
  apply col_cop__cop with C; [apply 等价共面ABDC, col_cop__cop with D| |apply 共线的传递性1 with D]; Col.
Qed.

Lemma col_cop2__cop : forall A B C U V P, U <> V ->
  共面 A B C U -> 共面 A B C V -> Col U V P ->
  共面 A B C P.
Proof.
  intros A B C U V P HUV HU HV HCol.
  destruct (共线的决定性 A B C) as [HCol1|HNCol].
    apply 共线三点和任一点共面, HCol1.
  revert dependent C.
  revert A B.
  assert (Haux : forall A B C, ~ Col A B C -> ~ Col U A B ->
  共面 A B C U -> 共面 A B C V -> 共面 A B C P).
  { intros A B C HNCol HNCol' HU HV.
    apply (coplanar_trans_1 U); [Cop..|].
    apply 等价共面CABD, col_cop__cop with V; auto.
    apply (coplanar_trans_1 C); Col; Cop.
  }
  intros A B C HU HV HNCol.
  destruct (共线的决定性 U A B); [destruct (共线的决定性 U A C)|].
  - apply 等价共面CABD, Haux; Col; Cop.
    intro; apply HNCol; destruct (两点重合的决定性 U A); ColR.
  - apply 等价共面ACBD, Haux; Col; Cop.
  - apply Haux; assumption.
Qed.

Lemma bet_cop2__cop : forall A B C U V W,
  共面 A B C U -> 共面 A B C W -> Bet U V W -> 共面 A B C V.
Proof.
  intros A B C U V W HU HW HBet.
  destruct (两点重合的决定性 U W).
    treat_equalities; assumption.
    apply col_cop2__cop with U W; Col.
Qed.

Lemma coplanar_pseudo_trans : forall A B C D P Q R,
  ~ Col P Q R ->
  共面 P Q R A ->
  共面 P Q R B ->
  共面 P Q R C ->
  共面 P Q R D ->
  共面 A B C D.
Proof.
assert (Haux : forall P Q R A B C,
  ~ Col P Q R -> 共面 P Q R A -> 共面 P Q R B -> 共面 P Q R C ->
  共面 A B C R).
  {
  intros P Q R A B C HNC HCop1 HCop2 HCop3.
  统计不重合点.
  elim (共线的决定性 R Q A); intro HQRA.
    apply 等价共面DABC, col_cop__cop with Q; auto.
    apply 等价共面CDBA, (coplanar_trans_1 P); assumption.
  apply 等价共面BCDA, (coplanar_trans_1 Q); [Col|apply (coplanar_trans_1 P); assumption..].
  }
intros A B C D P Q R HNC HCop1 HCop2 HCop3 HCop4.
elim (共线的决定性 P Q D); intro HPQD.
  apply col_cop2__cop with P Q; [统计不重合点|apply (Haux Q R)|apply (Haux P R)|]; Col; Cop.
apply (Haux P Q); [assumption|apply (coplanar_trans_1 R); Col; Cop..].
Qed.

Lemma l9_30 : forall A B C D E F P X Y Z,
  ~ 共面 A B C P -> ~ Col D E F -> 共面 D E F P ->
  共面 A B C X -> 共面 A B C Y -> 共面 A B C Z ->
  共面 D E F X -> 共面 D E F Y -> 共面 D E F Z ->
  Col X Y Z.
Proof.
  intros A B C D E F P X Y Z HNCop HNCol HP HX1 HY1 HZ1 HX2 HY2 HZ2.
  destruct (共线的决定性 X Y Z); [assumption|].
  assert (~ Col A B C) by (apply 四点不共面则前三点不共线 with P, HNCop).
  exfalso.
  apply HNCop.
  apply coplanar_pseudo_trans with X Y Z; [assumption|apply coplanar_pseudo_trans with A B C; Cop..|];
  apply coplanar_pseudo_trans with D E F; assumption.
Qed.

Lemma cop_per2__col : forall A X Y Z,
  共面 A X Y Z ->  A <> Z -> Per X Z A -> Per Y Z A -> Col X Y Z.
Proof.
intros A X Y Z HC HAZ HPer1 HPer2.
destruct HPer1 as [B' [HMid1 HCong1]]; destruct HPer2 as [B [HMid2 HCong2]]; treat_equalities.
elim (两点重合的决定性 X Y); intro HXY; treat_equalities; Col.
elim (两点重合的决定性 X Z); intro HXZ; treat_equalities; Col.
elim (两点重合的决定性 Y Z); intro HYZ; treat_equalities; Col.
destruct HC as [I HC].
elim HC; clear HC; intro HC; try (elim HC; clear HC);
try (intros HCol1 HCol2); try (intro H; destruct H as [HCol1 HCol2]).

  {
  elim (两点重合的决定性 X I); intro HXI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with Y Z; unfold 中点 in *; 分离合取式; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A X B I).
      {
      apply l5_6_等长保持小于等于关系 with A X A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A X HLe); destruct H as [X' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A X' B X).
      {
      apply 五线段公理_等价SAS with I I X X'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply 等长的传递性 with B X; Cong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply 点的唯一构造 with I X X A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := 由一点往一方向构造等长线段 B I I X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong A X' B X).
      {
      apply 五线段公理_等价SAS with X X' I I; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; Cong.
      apply 等长的传递性 with B X; Cong.
      }
    assert (H : A = B) by (apply 点的唯一构造 with X I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := 由一点往一方向构造等长线段 I B A X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong X B X' A).
      {
      apply 五线段公理_等价SAS with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply 等长的传递性 with B X; Cong.
      apply 两组连续三点分段等则全体等 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I X; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (两点重合的决定性 Y I); intro HYI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Z; unfold 中点 in *; 分离合取式; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A Y B I).
      {
      apply l5_6_等长保持小于等于关系 with A Y A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A Y HLe); destruct H as [Y' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A Y' B Y).
      {
      apply 五线段公理_等价SAS with I I Y Y'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply 等长的传递性 with B Y; Cong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply 点的唯一构造 with I Y Y A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := 由一点往一方向构造等长线段 B I I Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong A Y' B Y).
      {
      apply 五线段公理_等价SAS with Y Y' I I; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; Cong.
      apply 等长的传递性 with B Y; Cong.
      }
    assert (H : A = B) by (apply 点的唯一构造 with Y I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := 由一点往一方向构造等长线段 I B A Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong Y B Y' A).
      {
      apply 五线段公理_等价SAS with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply 等长的传递性 with B Y; Cong.
      apply 两组连续三点分段等则全体等 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I Y; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (两点重合的决定性 Z I); intro HZI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Y; unfold 中点 in *; 分离合取式; Cong).
  assert (H := 共线点间距相同要么重合要么中点 I A B).
  elim H; try ColR; intro.
    treat_equalities; exfalso; auto.
  ColR.
  }
Qed.

Lemma cop_perp2__col : forall X Y Z A B,
 共面 A B Y Z -> Perp X Y A B -> Perp X Z A B -> Col X Y Z.
Proof.
    intros.
    induction(共线的决定性 A B X).
      induction(两点重合的决定性 X A).
        subst A.
        assert(X <> B).
          apply 垂直推出不重合 in H0.
          分离合取式.
          assumption.
        apply 垂直的右交换性 in H0.
        apply L形垂直转垂直于 in H0.
        apply 垂直于的交换性 in H0.
        apply L形垂直于转直角 in H0.
        apply 垂直的右交换性 in H1.
        apply L形垂直转垂直于 in H1.
        apply 垂直于的交换性 in H1.
        apply L形垂直于转直角 in H1.
        apply 等价共线CAB.
        apply cop_per2__col with B.
          Cop.
          auto.
          assumption.
          assumption.
      assert(Perp A X X Y ).
        eapply 垂线共线点也构成垂直1.
          auto.
          apply 垂直的对称性.
          apply H0.
        assumption.
      assert(Perp A X X Z).
        eapply 垂线共线点也构成垂直1.
          auto.
          apply 垂直的对称性.
          apply H1.
        assumption.
      apply 等价共线CAB.
      apply cop_per2__col with A.
        统计不重合点; apply 等价共面CABD, col_cop__cop with B; Cop.
        auto.
        apply L形垂直于转直角.
        apply 垂直于的交换性.
        apply L形垂直转垂直于.
        apply 垂直的对称性.
        assumption.
      apply L形垂直于转直角.
      apply 垂直于的交换性.
      apply L形垂直转垂直于.
      apply 垂直的对称性.
      assumption.
    assert(HH0:=H0).
    assert(HH1:=H1).
    unfold Perp in H0.
    unfold Perp in H1.
    ex_and H0 Y0.
    ex_and H1 Z0.
    assert(HH2:=H0).
    assert(HH3:=H3).
    apply 垂点是交点 in H0.
    apply 垂点是交点 in H3.
    分离合取式.
    assert(Perp X Y0 A B).
      eapply 垂线共线点也构成垂直1.
        intro.
        subst Y0.
        contradiction.
        apply HH0.
      assumption.
    assert(Perp X Z0 A B).
      eapply 垂线共线点也构成垂直1.
        intro.
        subst Z0.
        contradiction.
        apply HH1.
      assumption.
    assert(Y0 = Z0).
      eapply l8_18_过一点垂线之垂点的唯一性.
        apply H2.
        assumption.
        apply 垂直的对称性.
        assumption.
        assumption.
      apply 垂直的对称性.
      assumption.
    subst Z0.
    apply (共线的传递性2 _ Y0).
      intro.
      subst Y0.
      contradiction.
      Col.
    Col.
Qed.

Lemma two_sides_dec : forall A B C D, TS A B C D \/ ~ TS A B C D.
Proof.
    intros.
    destruct (共线的决定性 C A B).
      right; intros []; contradiction.
    destruct (共线的决定性 D A B) as [|HNCol].
      right; intros [HN []]; contradiction.
    destruct (l8_18_过一点垂线之垂点的存在性 A B C) as [C0 [HCol1 HPerp1]]; Col.
    destruct (l8_18_过一点垂线之垂点的存在性 A B D) as [D0 [HCol2 HPerp2]]; Col.
    统计不重合点.
    destruct (中点的存在性 C0 D0) as [M].
    assert (Col M A B).
      destruct (两点重合的决定性 C0 D0); [treat_equalities; Col|ColR].
    destruct (l6_11_existence D0 C0 C D) as [D' []]; auto.
    destruct (中间性的决定性 C M D') as [|HNBet].
    { left; apply l9_2, l9_5 with D' D0; Col.
      repeat split; auto.
        intro; apply HNCol; ColR.
      exists M; split; Between.
    }
    right; intro HTS.
    apply HNBet.
    assert (HTS1 : TS A B D' C).
      apply l9_5 with D D0; [apply l9_2|Col|apply l6_6]; assumption.
    destruct (两点重合的决定性 C0 D0).
    { treat_equalities.
      assert (Col M C D) by (apply cop_perp2__col with A B; Perp; Cop).
      destruct (distinct A B M); auto.
      - apply col_two_sides_bet with A.
          ColR.
        apply invert_two_sides, col_two_sides with B; Col; apply l9_2, HTS1.
      - apply col_two_sides_bet with B.
          ColR.
        apply invert_two_sides, col_two_sides with A; Col.
        apply l9_2, invert_two_sides, HTS1.
    }
    destruct HTS1 as [HNCol' [_ [M' []]]].
    destruct (四点成首末边等长双直角S形则对边等长且对角线交点平分对角线 C0 D0 C D' M') as [_ []]; Between; Cong; Col.
      apply L形垂直转直角1, 与垂线共线之线也为垂线2 with A B; auto.
      统计不重合点; apply 直角边共线点也构成直角2 with D; Col; apply L形垂直转直角1, 与垂线共线之线也为垂线2 with A B; auto.
      ColR.
    replace M with M'; Between.
    apply (中点的唯一性1 C0 D0); assumption.
Qed.

Lemma cop_nts__os :
 forall A B C D,
  共面 A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  ~ TS A B C D ->
  OS A B C D.
Proof.
    intros.
    induction (cop__one_or_two_sides A B C D); auto.
    contradiction.
Qed.

Lemma cop_nos__ts :
 forall A B C D,
  共面 A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  ~ OS A B C D ->
  TS A B C D.
Proof.
    intros.
    induction (cop__one_or_two_sides A B C D); auto.
    contradiction.
Qed.

Lemma one_side_dec : forall A B C D,
 OS A B C D \/ ~ OS A B C D.
Proof.
  intros A B C D.
  destruct (共线的决定性 A B D).
    right; intro Habs; apply (one_side_not_col124 A B C D); assumption.
  destruct (l9_10 A B D) as [D']; Col.
  destruct (two_sides_dec A B C D') as [|HNTS].
    left; apply l9_8_1 with D'; assumption.
  right; intro.
  apply HNTS, l9_8_2 with D.
    assumption.
  apply one_side_symmetry; assumption.
Qed.

Lemma cop_dec : forall A B C D,
 共面 A B C D \/ ~ 共面 A B C D.
Proof.
  intros A B C D.
  destruct (共线的决定性 C A B).
    left; exists C; left; split; Col.
  destruct (共线的决定性 D A B).
    left; exists D; left; split; Col.
  destruct (two_sides_dec A B C D).
    left; apply 异侧蕴含共面; assumption.
  destruct (one_side_dec A B C D).
    left; apply os__coplanar; assumption.
  right; intro; destruct (cop__one_or_two_sides A B C D); auto.
Qed.

Lemma ex_diff_cop : forall A B C D, exists E,
  共面 A B C E /\ D <> E.
Proof.
  intros A B C D.
  destruct (两点重合的决定性 A D); [destruct (两点重合的决定性 B D); subst|].
  - destruct (每个点均有不同点 D) as [E]; exists E; split; Cop.
  - exists B; split; Cop.
  - exists A; split; Cop.
Qed.

Lemma ex_ncol_cop : forall A B C D E, D <> E ->
  exists F, 共面 A B C F /\ ~ Col D E F.
Proof.
  intros A B C D E HDE.
  destruct (共线的决定性 A B C) as [|HNCol].
    destruct (两点不重合则存在不共线的点 D E HDE) as [F]; exists F; split; Cop.
  destruct (共线的决定性 D E A); [destruct (共线的决定性 D E B)|].
  - exists C; split; Cop.
    intro; apply HNCol; ColR.
  - exists B; split; Cop.
  - exists A; split; Cop.
Qed.

Lemma ex_ncol_cop2 : forall A B C D, exists E F,
  共面 A B C E /\ 共面 A B C F /\ ~ Col D E F.
Proof.
  intros A B C D.
  destruct (ex_diff_cop A B C D) as [E [HE HDE]].
  destruct (ex_ncol_cop A B C D E HDE) as [F []].
  exists E, F; repeat split; assumption.
Qed.

Lemma col2_cop2__eq : forall A B C U V P Q, ~ 共面 A B C U -> U <> V ->
  共面 A B C P -> 共面 A B C Q -> Col U V P -> Col U V Q ->
  P = Q.
Proof.
  intros A B C U V P Q HNCop; intros.
  destruct (两点重合的决定性 P Q); [assumption|].
  exfalso.
  apply HNCop, col_cop2__cop with P Q; ColR.
Qed.

Lemma cong3_cop2__col : forall A B C P Q,
  共面 A B C P -> 共面 A B C Q ->
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  Col A B C.
Proof.
  intros A B C P Q HP HQ HPQ HA HB HC.
  destruct (共线的决定性 A B C); [assumption|].
  destruct (中点的存在性 P Q) as [M HMid].
  assert (Per A M P) by (exists Q; Cong).
  assert (Per B M P) by (exists Q; Cong).
  assert (Per C M P) by (exists Q; Cong).
  elim (两点重合的决定性 A M); intro HAM.
    treat_equalities.
    统计不重合点; apply 等价共线CAB, cop_per2__col with P; Cop.
  assert (Col A B M).
    apply cop_per2__col with P; try apply HUD; 统计不重合点; auto.
    apply 等价共面CABD, col_cop__cop with Q; Col.
    apply coplanar_trans_1 with C; Cop; Col.
  assert (Col A C M).
    apply cop_per2__col with P; try apply HUD; 统计不重合点; auto.
    apply 等价共面CABD, col_cop__cop with Q; Col.
    apply coplanar_trans_1 with B; Cop; Col.
  apply 共线的传递性2 with M; Col.
Qed.

Lemma l9_38 : forall A B C P Q, 在平面异侧 A B C P Q -> 在平面异侧 A B C Q P.
Proof.
  intros A B C P Q [HP [HQ [T [HT HBet]]]].
  repeat split; trivial.
  exists T; split; Between.
Qed.

Lemma l9_39 : forall A B C D P Q R, 在平面异侧 A B C P R -> 共面 A B C D -> Out D P Q ->
  在平面异侧 A B C Q R.
Proof.
  intros A B C D P Q R [HP [HR [T [HT HBet]]]] HCop HOut.
  assert (HNCol : ~ Col A B C) by (apply 四点不共面则前三点不共线 with P, HP).
  split.
    intro; 统计不重合点; apply HP, col_cop2__cop with D Q; Col.
  split; [assumption|].
  destruct (两点重合的决定性 D T).
    subst T; exists D; split; [|apply (bet_out__bet P)]; assumption.
  assert (HTS : TS D T Q R).
  { assert (~ Col P D T) by (intro; apply HP, col_cop2__cop with D T; Col).
    apply l9_8_2 with P.
    - repeat split; auto.
        intro; apply HR, col_cop2__cop with D T; Col.
        exists T; split; Col.
    - apply out_one_side; Col.
  }
  destruct HTS as [HNCol1 [HNCol2 [T' []]]].
  exists T'; split; [|assumption].
  apply col_cop2__cop with D T; Col.
Qed.

Lemma l9_41_1 : forall A B C P Q R, 在平面异侧 A B C P R -> 在平面异侧 A B C Q R -> 在平面同侧 A B C P Q.
Proof.
  intros A B C P Q R H1 H2.
  exists R; split; assumption.
Qed.

Lemma l9_41_2 : forall A B C P Q R, 在平面异侧 A B C P R -> 在平面同侧 A B C P Q -> 在平面异侧 A B C Q R.
Proof.
  intros A B C P Q R HPR [S [[HP [_ [X []]]] [HQ [HS [Y []]]]]].
  assert (P <> X /\ S <> X /\ Q <> Y /\ S <> Y) by (repeat split; intro; subst; auto); 分离合取式.
  destruct (共线的决定性 P Q S) as [|HNCol].
  { assert (X = Y) by (统计不重合点; apply (col2_cop2__eq A B C Q S); ColR).
    subst Y.
    apply l9_39 with X P; trivial.
    apply l6_2 with S; auto.
  }
  destruct (帕施公理 P Q S X Y) as [Z []]; trivial.
  assert (X <> Z) by (intro; subst; apply HNCol; ColR).
  apply l9_39 with X Z; [|assumption|apply bet_out; auto].
  assert (Y <> Z) by (intro; subst; apply HNCol; ColR).
  apply l9_39 with Y P; [assumption..|apply l6_6, bet_out; auto].
Qed.

Lemma tsp_exists : forall A B C P, ~ 共面 A B C P -> exists Q, 在平面异侧 A B C P Q.
Proof.
  intros A B C P HP.
  destruct (由一点往一方向构造等长线段 P A A P) as [Q []].
  assert (HA : 共面 A B C A) by Cop.
  exists Q; repeat split.
  - assumption.
  - assert (A <> P) by (intro; subst; apply HP, HA); 统计不重合点.
    intro; apply HP, col_cop2__cop with A Q; Col.
  - exists A; split; assumption.
Qed.

Lemma osp_reflexivity : forall A B C P, ~ 共面 A B C P -> 在平面同侧 A B C P P.
Proof.
  intros A B C P HP.
  destruct (tsp_exists A B C P HP) as [Q].
  exists Q; split; assumption.
Qed.

Lemma osp_symmetry : forall A B C P Q, 在平面同侧 A B C P Q -> 在平面同侧 A B C Q P.
Proof.
  intros A B C P Q [R []].
  exists R; split; assumption.
Qed.

Lemma osp_transitivity : forall A B C P Q R, 在平面同侧 A B C P Q -> 在平面同侧 A B C Q R -> 在平面同侧 A B C P R.
Proof.
  intros A B C P Q R [S [HPS HQS]] HQR.
  exists S; split; [|apply l9_41_2 with Q]; assumption.
Qed.

Lemma cop3_tsp__tsp : forall A B C D E F P Q, ~ Col D E F ->
  共面 A B C D -> 共面 A B C E -> 共面 A B C F ->
  在平面异侧 A B C P Q -> 在平面异侧 D E F P Q.
Proof.
  intros A B C D E F P Q HNCol HD HE HF [HP [HQ [T [HT HBet]]]].
  assert (~ Col A B C) by (apply 四点不共面则前三点不共线 with P, HP).
  assert (共面 D E F A /\ 共面 D E F B /\ 共面 D E F C /\ 共面 D E F T).
    repeat split; apply coplanar_pseudo_trans with A B C; Cop.
  分离合取式.
  repeat split.
    intro; apply HP; apply coplanar_pseudo_trans with D E F; Cop.
    intro; apply HQ; apply coplanar_pseudo_trans with D E F; Cop.
    exists T; split; assumption.
Qed.

Lemma cop3_osp__osp : forall A B C D E F P Q, ~ Col D E F ->
  共面 A B C D -> 共面 A B C E -> 共面 A B C F ->
  在平面同侧 A B C P Q -> 在平面同侧 D E F P Q.
Proof.
  intros A B C D E F P Q HNCol HD HE HF [R []].
  exists R; split; apply (cop3_tsp__tsp A B C); assumption.
Qed.

Lemma ncop_distincts : forall A B C D, ~ 共面 A B C D ->
  A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.
Proof.
  intros A B C D H; repeat split; intro; subst; apply H; Cop.
Qed.

Lemma tsp_distincts : forall A B C P Q, 在平面异侧 A B C P Q ->
  A <> B /\ A <> C /\ B <> C /\ A <> P /\ B <> P /\ C <> P /\ A <> Q /\ B <> Q /\ C <> Q /\ P <> Q.
Proof.
  intros A B C P Q [HP [HQ HT]].
  assert (HP' := ncop_distincts A B C P HP).
  assert (HQ' := ncop_distincts A B C Q HQ).
  分离合取式; clean.
  repeat split; auto.
  destruct HT; 分离合取式.
  intro; apply HP; treat_equalities; assumption.
Qed.

Lemma osp_distincts : forall A B C P Q, 在平面同侧 A B C P Q ->
  A <> B /\ A <> C /\ B <> C /\ A <> P /\ B <> P /\ C <> P /\ A <> Q /\ B <> Q /\ C <> Q.
Proof.
  intros A B C P Q [R [HPR HQR]].
  apply tsp_distincts in HPR.
  apply tsp_distincts in HQR.
  分离合取式; clean; repeat split; auto.
Qed.

Lemma tsp__ncop1 : forall A B C P Q, 在平面异侧 A B C P Q -> ~ 共面 A B C P.
Proof.
  unfold 在平面异侧; intros; 分离合取式; assumption.
Qed.

Lemma tsp__ncop2 : forall A B C P Q, 在平面异侧 A B C P Q -> ~ 共面 A B C Q.
Proof.
  unfold 在平面异侧; intros; 分离合取式; assumption.
Qed.

Lemma osp__ncop1 : forall A B C P Q, 在平面同侧 A B C P Q -> ~ 共面 A B C P.
Proof.
  intros A B C P Q [R [H1 H2]].
  apply tsp__ncop1 with R, H1.
Qed.

Lemma osp__ncop2 : forall A B C P Q, 在平面同侧 A B C P Q -> ~ 共面 A B C Q.
Proof.
  intros A B C P Q [R [H1 H2]].
  apply tsp__ncop1 with R, H2.
Qed.

Lemma tsp__nosp : forall A B C P Q, 在平面异侧 A B C P Q -> ~ 在平面同侧 A B C P Q.
Proof.
  intros A B C P Q HTS HOS.
  absurd (在平面异侧 A B C P P).
    intro Habs; apply tsp_distincts in Habs; 分离合取式; auto.
    apply l9_41_2 with Q; [apply l9_38 | apply osp_symmetry]; assumption.
Qed.

Lemma osp__ntsp : forall A B C P Q, 在平面同侧 A B C P Q -> ~ 在平面异侧 A B C P Q.
Proof.
  intros A B C P Q HOS HTS.
  apply (tsp__nosp A B C P Q); assumption.
Qed.

Lemma osp_bet__osp : forall A B C P Q R, 在平面同侧 A B C P R -> Bet P Q R -> 在平面同侧 A B C P Q.
Proof.
  intros A B C P Q R [S [HPS [HR [_ [Y []]]]]] HBet.
  destruct (共线的决定性 P R S) as [|HNCol].
  { exists S.
    split; [assumption|].
    apply l9_39 with Y P; trivial.
    destruct HPS as [HP [HS [X []]]].
    assert (P <> X /\ S <> X /\ R <> Y) by (repeat split; intro; subst; auto); 分离合取式.
    assert (X = Y) by (统计不重合点; apply (col2_cop2__eq A B C R S); ColR).
    subst Y.
    apply out_bet_out_1 with R; [|assumption].
    apply l6_2 with S; auto.
  }
  destruct HPS as [HP [HS [X []]]].
  assert (HOS : OS X Y P Q).
  { apply l9_17 with R; [|assumption].
    assert (P <> X /\ S <> X /\ R <> Y /\ S <> Y) by (repeat split; intro; subst; auto); 分离合取式.
    assert (~ Col S X Y) by (intro; apply HNCol; ColR).
    exists S; repeat split; trivial; try (intro; apply HNCol; ColR).
      exists X; split; Col.
      exists Y; split; Col.
  }
  destruct HOS as [S' [[HNCol1 [HNCol2 [X' []]]] [HNCol3 [_ [Y' []]]]]].
  assert (共面 A B C X') by (统计不重合点; apply col_cop2__cop with X Y; Col).
  assert (共面 A B C Y') by (统计不重合点; apply col_cop2__cop with X Y; Col).
  assert (HS' : ~ 共面 A B C S').
    intro; apply HP, col_cop2__cop with X' S'; Col; intro; subst; Col.
  exists S'; repeat split; trivial.
    exists X'; split; assumption.
    intro; apply HS', col_cop2__cop with Q Y'; Col; intro; subst; Col.
    exists Y'; split; assumption.
Qed.

Lemma l9_18_3 : forall A B C X Y P, 共面 A B C P -> Col X Y P ->
  在平面异侧 A B C X Y <-> Bet X P Y /\ ~ 共面 A B C X /\ ~ 共面 A B C Y.
Proof.
  intros A B C X Y P HP HCol.
  split; [|intros [HBet [HX HY]]; repeat split; trivial; exists P; split; assumption].
  intros [HX [HY [T [HT HBet]]]].
  repeat split; trivial.
  replace P with T; trivial.
  apply (col2_cop2__eq A B C X Y); Col.
  intro; treat_equalities; auto.
Qed.

Lemma bet_cop__tsp : forall A B C X Y P,
  ~ 共面 A B C X -> P <> Y -> 共面 A B C P -> Bet X P Y ->
  在平面异侧 A B C X Y.
Proof.
  intros A B C X Y P HX HPY HP HBet.
  apply (l9_18_3 A B C X Y P); Col.
  repeat split; [assumption..|].
  intro; apply HX, col_cop2__cop with P Y; Col.
Qed.

Lemma cop_out__osp : forall A B C X Y P,
  ~ 共面 A B C X -> 共面 A B C P -> Out P X Y -> 在平面同侧 A B C X Y.
Proof.
  intros A B C X Y P HX HP HOut.
  assert (~ 共面 A B C Y).
    统计不重合点; intro; apply HX, col_cop2__cop with P Y; Col.
  destruct (由一点往一方向构造等长线段 X P P X) as [X' []].
  assert (~ 共面 A B C X').
    统计不重合点; intro; apply HX, col_cop2__cop with P X'; Col.
  exists X'; repeat split; trivial; exists P; split; trivial.
  apply bet_out__bet with X; assumption.
Qed.

Lemma l9_19_3 : forall A B C X Y P, 共面 A B C P -> Col X Y P ->
  在平面同侧 A B C X Y <-> Out P X Y /\ ~ 共面 A B C X.
Proof.
  intros A B C X Y P HP HCol.
  split; [|intros []; apply cop_out__osp with P; assumption].
  intro HOS.
  assert (~ 共面 A B C X /\ ~ 共面 A B C Y).
    unfold 在平面同侧, 在平面异侧 in HOS; destruct HOS as [Z []]; 分离合取式; split; assumption.
  分离合取式.
  split; [|assumption].
  apply not_bet_out; [Col|].
  intro HBet.
  apply osp__ntsp in HOS.
  apply HOS.
  repeat split; trivial; exists P; split; assumption.
Qed.

Lemma cop2_ts__tsp : forall A B C D E X Y, ~ 共面 A B C X ->
  共面 A B C D -> 共面 A B C E -> TS D E X Y ->
  在平面异侧 A B C X Y.
Proof.
  intros A B C D E X Y HX HD HE [HNCol [HNCol' [T []]]].
  assert (共面 A B C T) by (统计不重合点; apply col_cop2__cop with D E; Col).
  repeat split.
    assumption.
    intro; apply HX, col_cop2__cop with T Y; Col; intro; subst; apply HNCol'; Col.
  exists T; split; assumption.
Qed.

Lemma cop2_os__osp : forall A B C D E X Y, ~ 共面 A B C X ->
  共面 A B C D -> 共面 A B C E -> OS D E X Y ->
  在平面同侧 A B C X Y.
Proof.
  intros A B C D E X Y HX HD HE [Z [HXZ HYZ]].
  assert (HTS : 在平面异侧 A B C X Z) by (apply cop2_ts__tsp with D E; assumption).
  exists Z; split; [assumption|].
  destruct HTS as [_ []].
  apply l9_2 in HYZ.
  apply l9_38, cop2_ts__tsp with D E; assumption.
Qed.

Lemma cop3_tsp__ts : forall A B C D E X Y, D <> E ->
  共面 A B C D -> 共面 A B C E -> 共面 D E X Y ->
  在平面异侧 A B C X Y -> TS D E X Y.
Proof.
  intros A B C D E X Y HDE HD HE HCop H在平面异侧.
  assert (HX : ~ 共面 A B C X) by (apply tsp__ncop1 with Y, H在平面异侧).
  assert (HY : ~ 共面 A B C Y) by (apply tsp__ncop2 with X, H在平面异侧).
  apply cop_nos__ts.
    assumption.
    intro; apply HX, col_cop2__cop with D E; Col.
    intro; apply HY, col_cop2__cop with D E; Col.
  intro.
  apply tsp__nosp in H在平面异侧.
  apply H在平面异侧, cop2_os__osp with D E; assumption.
Qed.

Lemma cop3_osp__os : forall A B C D E X Y, D <> E ->
  共面 A B C D -> 共面 A B C E -> 共面 D E X Y ->
  在平面同侧 A B C X Y -> OS D E X Y.
Proof.
  intros A B C D E X Y HDE HD HE HCop H在平面同侧.
  assert (HX : ~ 共面 A B C X) by (apply osp__ncop1 with Y, H在平面同侧).
  assert (HY : ~ 共面 A B C Y) by (apply osp__ncop2 with X, H在平面同侧).
  apply cop_nts__os.
    assumption.
    intro; apply HX, col_cop2__cop with D E; Col.
    intro; apply HY, col_cop2__cop with D E; Col.
  intro.
  apply osp__ntsp in H在平面同侧.
  apply H在平面同侧, cop2_ts__tsp with D E; assumption.
Qed.

Lemma cop_tsp__ex_cop2 : forall A B C D E P,
  共面 A B C P -> 在平面异侧 A B C D E ->
  exists Q, 共面 A B C Q /\ 共面 D E P Q /\ P <> Q.
Proof.
  intros A B C D E P HCop H在平面异侧.
  destruct (共线的决定性 D E P) as [|HNCol].
  { apply tsp_distincts in H在平面异侧; 分离合取式.
    destruct (两点重合的决定性 P A).
      subst; exists B; repeat split; Cop.
      exists A; repeat split; Cop.
  }
  destruct H在平面异侧 as [_ [_ [Q []]]].
  exists Q; repeat split; Cop.
  intro; subst; apply HNCol; Col.
Qed.

Lemma cop_osp__ex_cop2 : forall A B C D E P,
  共面 A B C P -> 在平面同侧 A B C D E ->
  exists Q, 共面 A B C Q /\ 共面 D E P Q /\ P <> Q.
Proof.
  intros A B C D E P HCop H在平面同侧.
  destruct (共线的决定性 D E P) as [|HNCol].
  { apply osp_distincts in H在平面同侧; 分离合取式.
    destruct (两点重合的决定性 P A).
      subst; exists B; repeat split; Cop.
      exists A; repeat split; Cop.
  }
  destruct (由一点往一方向构造等长线段 E P P E) as [E' []].
  assert (~ Col D E' P) by (intro; apply HNCol; ColR).
  destruct (cop_tsp__ex_cop2 A B C D E' P) as [Q [HQ1 [HQ2 HPQ]]]; [assumption|..].
  { apply l9_41_2 with E.
      统计不重合点; destruct H在平面同侧 as [F [_ [HE]]]; apply bet_cop__tsp with P; Cop.
      apply osp_symmetry, H在平面同侧.
  }
  exists Q; repeat split; auto.
  apply 等价共面ACBD, coplanar_trans_1 with E'; Col; Cop.
Qed.

Lemma sac__coplanar : forall A B C D, 萨凯里四边形 A B C D -> 共面 A B C D.
Proof.
  intros A B C D [_ [_ [_ HOS]]].
  apply os__coplanar in HOS; Cop.
Qed.

End T9.

Hint Resolve l9_2 invert_two_sides invert_one_side one_side_symmetry l9_9 l9_9_bis
             l9_31 l9_38 osp_symmetry osp__ntsp tsp__nosp : side.
Hint Resolve os__coplanar sac__coplanar : cop.

Ltac Side := auto 4 with side.

Ltac not_exist_hyp_perm_ncol4 A B C D := first
  [not_exist_hyp_perm_ncol A B C|not_exist_hyp_perm_ncol A B D|
   not_exist_hyp_perm_ncol A C D|not_exist_hyp_perm_ncol B C D].

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y H))

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);Side)

      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := 四点不共面则任三点不共线 A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.
