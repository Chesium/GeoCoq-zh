Require Export GeoCoq.Tarski_dev.Ch09_plane.
Require Export GeoCoq.Tarski_dev.Tactics.CoincR_for_cop.

Ltac assert_cops :=
 repeat match goal with
      | H:Perp ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply perp__coplanar, H)
      | H:TS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply ts__coplanar, H)
      | H:OS ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply os__coplanar, H)
      | H:严格对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply reflectl__coplanar, H)
      | H:对称 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply reflect__coplanar, H)
      | H:在角内 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply inangle__coplanar, H)
      | H:严格平行 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply pars__coplanar, H)
      | H:Par ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply par__coplanar, H)
      | H:Plg ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plg__coplanar, H)
      | H:严格平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plgs__coplanar, H)
      | H:退化平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply plgf__coplanar, H)
      | H:平行四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply parallelogram__coplanar, H)
      | H:菱形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply rhombus__coplanar, H)
      | H:长方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply rectangle__coplanar, H)
      | H:正方形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply square__coplanar, H)
      | H:萨凯里四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply sac__coplanar, H)
      | H:Lambert四边形 ?X1 ?X2 ?X3 ?X4 |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4; assert (共面 X1 X2 X3 X4) by (apply lambert__coplanar, H)
 end.

Ltac Cop := auto; try (intros; solve [apply col__coplanar; Col
     |apply coplanar_perm_1, col__coplanar; Col|apply coplanar_perm_4, col__coplanar; Col
     |apply coplanar_perm_18, col__coplanar; Col
     |assert_cops; auto 2 with cop_perm]).

Ltac exist_hyp_perm_col A B C := first [exist_hyp (Col A B C)|exist_hyp (Col A C B)
                                       |exist_hyp (Col B A C)|exist_hyp (Col B C A)
                                       |exist_hyp (Col C A B)|exist_hyp (Col C B A)].

Ltac copr_aux :=
 repeat match goal with
      | H: ~ Col ?X1 ?X2 ?X3, X4 : Tpoint |- _ =>
     not_exist_hyp_perm_cop X1 X2 X3 X4;
     first[exist_hyp_perm_col X1 X2 X4; assert (共面 X1 X2 X4 X3) by (apply col__coplanar; Col)
          |exist_hyp_perm_col X2 X3 X4; assert (共面 X2 X3 X4 X1) by (apply col__coplanar; Col)
          |exist_hyp_perm_col X1 X3 X4; assert (共面 X1 X3 X4 X2) by (apply col__coplanar; Col)]
 end.

Ltac CopR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
 let cop := constr:(共面) in
   treat_equalities; assert_cols; clean; assert_ncols; assert_cops; auto 2 with cop_perm;
   solve[apply col__coplanar; Col|apply coplanar_perm_1, col__coplanar; Col
        |apply coplanar_perm_4, col__coplanar; Col|apply coplanar_perm_18, col__coplanar; Col
        |copr_aux; Cop_refl tpoint col cop] || fail "Can not be deduced".

Section T10.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.
Goal forall A B C D, ~ 共面 D C B A -> ~ 共面 A B C D.
Proof.
intros.
match goal with
       | |- 共面 ?A ?B ?C ?D => exist_hyp_perm_cop A B C D; auto with cop_perm
       | |- ~ 共面 ?A ?B ?C ?D => exist_hyp_perm_ncop A B C D; auto with cop_perm
      end.
Qed.
Lemma ex_sym : forall A B X, exists Y, (Perp A B X Y \/ X = Y) /\
   (exists M, Col A B M /\ 中点 M X Y).
Proof.
    intros.
    induction (共线的决定性 A B X).
      exists X.
      split.
        right.
        reflexivity.
      exists X.
      split.
        assumption.
      apply A是AA中点.
    assert (exists M, Col A B M /\ Perp A B X M).
      apply l8_18_过一点垂线之垂点的存在性.
      assumption.
    ex_and H0 M0.
    double X M0 Z.
    exists Z.
    split.
      left.
      apply 垂直的对称性.
      eapply 垂线共线点也构成垂直1.
        intro.
        subst Z.
        apply M是AA中点则M与A重合 in H2.
        subst X.
        apply 垂直推出不重合 in H1.
        spliter.
        absurde.
        apply 垂直的对称性.
        apply H1.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    exists M0.
    split.
      assumption.
    assumption.
Qed.

Lemma is_image_is_image_spec : forall P P' A B, A<>B -> (对称 P' P A B <-> 严格对称 P' P A B).
Proof.
    intros.
    unfold 对称.
    tauto.
Qed.

Lemma ex_sym1 : forall A B X, A<>B -> exists Y, (Perp A B X Y \/ X = Y) /\
 (exists M, Col A B M /\ 中点 M X Y /\ 对称 X Y A B).
Proof.
    intros.
    induction (共线的决定性 A B X).
      exists X.
      split.
        right.
        reflexivity.
      exists X.
      rewrite -> (is_image_is_image_spec) by apply H.
      split.
        assumption.
      split.
        apply A是AA中点.
      unfold 严格对称.
      split.
        exists X.
        split.
          apply A是AA中点.
        assumption.
      right.
      reflexivity.
    assert (exists M, Col A B M /\ Perp A B X M).
      apply l8_18_过一点垂线之垂点的存在性.
      assumption.
    ex_and H1 M0.
    double X M0 Z.
    exists Z.
    split.
      left.
      apply 垂直的对称性.
      eapply 垂线共线点也构成垂直1.
        intro.
        subst Z.
        apply M是AA中点则M与A重合 in H3.
        subst X.
        apply 垂直推出不重合 in H2.
        spliter.
        absurde.
        apply 垂直的对称性.
        apply H2.
      unfold Col.
      left.
      apply midpoint_bet.
      assumption.
    exists M0.
    split.
      assumption.
    split.
      assumption.
    rewrite -> (is_image_is_image_spec) by apply H.
    unfold 严格对称.
    split.
      exists M0.
      split.
        apply M是AB中点则M是BA中点.
        assumption.
      assumption.
    left.
    apply 垂直的对称性.
    apply 垂直的左交换性.
    eapply 垂线共线点也构成垂直1.
      intro.
      subst X.
      apply M是AA中点则M与A重合 in H3.
      subst Z.
      apply 垂直推出不重合 in H2.
      spliter.
      absurde.
      apply 垂直的对称性.
      apply H2.
    unfold Col.
    left.
    apply midpoint_bet.
    assumption.
Qed.

Lemma l10_2_uniqueness : forall A B P P1 P2,
 对称 P1 P A B -> 对称 P2 P A B -> P1=P2.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst.
      unfold 对称 in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      eapply 中点组的唯一性1 with P B;auto.
    rewrite -> (is_image_is_image_spec) in * by apply H1.
    unfold 严格对称 in *.
    spliter.
    ex_and H X.
    ex_and H0 Y.
    induction H2; induction H3.
      assert (P <> X).
        intro.
        subst X.
        apply A是AB中点则A与B重合 in H.
        subst P1.
        apply 垂直推出不重合 in H3.
        spliter.
        absurde.
      assert (P <> Y).
        intro.
        subst Y.
        apply A是AB中点则A与B重合 in H0.
        subst P2.
        apply 垂直推出不重合 in H2.
        spliter.
        absurde.
      assert (Perp P X A B).
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply 垂直的对称性.
          apply H3.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      assert (Perp P Y A B).
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply 垂直的对称性.
          apply H2.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      induction (两点重合的决定性 X A).
        subst X.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1_共线四点和一垂直推另一直角.
            apply ABA型共线.
            apply ABB型共线.
            auto.
          apply 垂直的对称性.
          assumption.
        spliter.
        assert (Y = A).
          eapply l8_18_过一点垂线之垂点的唯一性.
            apply H10.
            assumption.
            apply 垂直的对称性.
            assumption.
            apply ABA型共线.
          apply 垂直的对称性.
          assumption.
        subst Y.
        eapply 中点组的唯一性1.
          apply H.
        apply H0.
      assert (~ Col A B P /\ Per P X A).
        eapply l8_16_1_共线四点和一垂直推另一直角.
          assumption.
          apply ABA型共线.
          auto.
        apply 垂直的对称性.
        assumption.
      spliter.
      assert (Y = X).
        eapply l8_18_过一点垂线之垂点的唯一性.
          apply H11.
          assumption.
          apply 垂直的对称性.
          assumption.
          assumption.
        apply 垂直的对称性.
        assumption.
      subst Y.
      eapply 中点组的唯一性1.
        apply H.
      apply H0.
      subst P1.
      assert (P <> Y).
        intro.
        subst Y.
        apply M是AA中点则M与A重合 in H.
        subst X.
        apply A是AB中点则A与B重合 in H0.
        subst P2.
        eapply 垂直推出不重合 in H2.
        spliter.
        absurde.
      assert (Perp P Y A B).
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply 垂直的对称性.
          apply H2.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      apply M是AA中点则M与A重合 in H.
      subst X.
      induction (两点重合的决定性 Y A).
        subst Y.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1_共线四点和一垂直推另一直角.
            assumption.
            apply ABB型共线.
            auto; auto.
          apply 垂直的对称性.
          assumption.
        spliter.
        contradiction.
      assert (~ Col A B P /\ Per P Y A).
        eapply l8_16_1_共线四点和一垂直推另一直角.
          assumption.
          apply ABA型共线.
          auto.
        apply 垂直的对称性.
        assumption.
      spliter.
      contradiction.
      subst P2.
      assert (P <> X).
        intro.
        subst X.
        apply M是AA中点则M与A重合 in H0.
        subst Y.
        apply A是AB中点则A与B重合 in H.
        subst P1.
        eapply 垂直推出不重合 in H3.
        spliter.
        absurde.
      assert (Perp P X A B).
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply 垂直的对称性.
          apply H3.
        unfold Col.
        right; left.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      apply M是AA中点则M与A重合 in H0.
      subst Y.
      induction (两点重合的决定性 X A).
        subst X.
        assert (~ Col A B P /\ Per P A B).
          eapply l8_16_1_共线四点和一垂直推另一直角.
            assumption.
            apply ABB型共线.
            auto.
          apply 垂直的对称性.
          assumption.
        spliter.
        contradiction.
      assert (~ Col A B P /\ Per P X A).
        eapply l8_16_1_共线四点和一垂直推另一直角.
          assumption.
          apply ABA型共线.
          auto.
        apply 垂直的对称性.
        assumption.
      spliter.
      contradiction.
    subst P1.
    subst P2.
    reflexivity.
Qed.

Lemma l10_2_uniqueness_spec : forall A B P P1 P2,
 严格对称 P1 P A B -> 严格对称 P2 P A B -> P1=P2.
Proof.
    intros A B P P1 P2 HP1 HP2.
    assert (HR1 := HP1).
    assert (HR2 := HP2).
    destruct HR1 as [HX1 [HPerp|Heq1]].
      assert_diffs; apply (l10_2_uniqueness A B P); apply is_image_is_image_spec; assumption.
    destruct HR2 as [HX2 [HPerp|Heq2]].
      assert_diffs; apply (l10_2_uniqueness A B P); apply is_image_is_image_spec; assumption.
   congruence.
Qed.

Lemma l10_2_existence_spec : forall A B P,
 exists P', 严格对称 P' P A B.
Proof.
    intros.
    induction (共线的决定性 A B P).
      unfold 严格对称.
      exists P.
      split.
        exists P.
        split.
          apply A是AA中点.
        assumption.
      right.
      reflexivity.
    assert (exists X, Col A B X /\ Perp A B P X).
      eapply l8_18_过一点垂线之垂点的存在性.
      assumption.
    ex_and H0 X.
    double P X P'.
    exists P'.
    unfold 严格对称.
    split.
      exists X.
      split; assumption.
    left.
    apply 垂直的对称性.
    eapply 垂线共线点也构成垂直1.
      intro.
      subst P'.
      apply M是AA中点则M与A重合 in H2.
      subst X.
      apply 垂直推出不重合 in H1.
      spliter.
      absurde.
      apply 垂直的对称性.
      apply H1.
    unfold Col.
    left.
    apply midpoint_bet.
    assumption.
Qed.

Lemma l10_2_existence : forall A B P,
 exists P', 对称 P' P A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst B.
      unfold 对称.
      elim (构造对称点 P A).
      intros P'.
      exists P'.
      tauto.
    elim (l10_2_existence_spec A B P).
    intros P'; intros.
    exists P'.
    unfold 对称.
    tauto.
Qed.

Lemma l10_4_spec : forall A B P P',
 严格对称 P P' A B ->
 严格对称 P' P A B.
Proof.
    intros.
    unfold 严格对称 in *.
    spliter.
    ex_and H X.
    split.
      exists X.
      split.
        apply M是AB中点则M是BA中点.
        assumption.
      assumption.
    induction H0.
      left.
      apply 垂直的右交换性.
      assumption.
    auto.
Qed.

Lemma l10_4 : forall A B P P', 对称 P P' A B -> 对称 P' P A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst B.
      unfold 对称 in *.
      elim H;intros.
        intuition.
      right.
      spliter.
      split.
        assumption.
      apply M是AB中点则M是BA中点.
      assumption.
    rewrite -> (is_image_is_image_spec) in * by apply H0.
    apply l10_4_spec;auto.
Qed.

Lemma l10_5 : forall A B P P' P'',
 对称 P' P A B ->
 对称 P'' P' A B -> P=P''.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      unfold 对称 in *.
      subst.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply 中点组的唯一性1 with P' B.
        apply M是AB中点则M是BA中点.
        assumption.
      assumption.
    rewrite -> (is_image_is_image_spec) in * by apply H1.
    eapply l10_2_uniqueness.
      eapply l10_4.
      apply is_image_is_image_spec.
        apply H1.
      apply H.
    apply is_image_is_image_spec.
      assumption.
    assumption.
Qed.

Lemma l10_6_uniqueness : forall A B P P1 P2, 对称 P P1 A B -> 对称 P P2 A B -> P1 = P2.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst.
      unfold 对称 in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply 中点组的唯一性1 with P B.
        apply M是AB中点则M是BA中点.
        assumption.
      apply M是AB中点则M是BA中点.
      assumption.
    eapply l10_2_uniqueness.
      apply l10_4.
      apply H.
    apply l10_4.
    assumption.
Qed.

Lemma l10_6_uniqueness_spec : forall A B P P1 P2, 严格对称 P P1 A B -> 严格对称 P P2 A B -> P1 = P2.
Proof.
    intros A B P P1 P2 HP1 HP2.
    assert (HR1 := HP1).
    assert (HR2 := HP2).
    destruct HR1 as [HX1 [HPerp|Heq1]].
      assert_diffs; apply (l10_6_uniqueness A B P); apply is_image_is_image_spec; assumption.
    destruct HR2 as [HX2 [HPerp|Heq2]].
      assert_diffs; apply (l10_6_uniqueness A B P); apply is_image_is_image_spec; assumption.
    subst; reflexivity.
Qed.

Lemma l10_6_existence_spec : forall A B P', A<>B -> exists P, 严格对称 P' P A B.
Proof.
    intros.
    assert (exists P, 严格对称 P P' A B).
      eapply l10_2_existence_spec.
    ex_and H0 P.
    exists P.
    apply l10_4_spec.
    assumption.
Qed.

Lemma l10_6_existence : forall A B P', exists P, 对称 P' P A B.
Proof.
    intros.
    assert (exists P, 对称 P P' A B).
      eapply l10_2_existence.
    ex_and H P.
    exists P.
    apply l10_4.
    assumption.
Qed.

Lemma l10_7 : forall A B P P' Q Q',
 对称 P' P A B -> 对称 Q' Q A B ->
  P'=Q' -> P = Q.
Proof.
    intros.
    subst Q'.
    eapply l10_2_uniqueness.
      apply l10_4.
      apply H.
    apply l10_4.
    assumption.
Qed.

Lemma l10_8 : forall A B P, 对称 P P A B -> Col P A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst;Col.
    unfold 对称 in H.
    unfold 严格对称 in H.
    induction H.
      spliter.
      ex_and H1 X.
      apply M是AA中点则M与A重合 in H1.
      subst X.
      Col.
    spliter. subst. Col.
Qed.

Lemma col__refl : forall A B P, Col P A B -> 严格对称 P P A B.
Proof.
    intros A B P HCol.
    split.
      exists P; split; [中点|Col].
    right; reflexivity.
Qed.


(** Here we need the assumption that A<>B *)
Lemma is_image_col_cong : forall A B P P' X, A<>B ->
 对称 P P' A B -> Col A B X -> Cong P X P' X.
Proof.
    intros.
    rewrite is_image_is_image_spec in H0 by apply H.
    unfold 严格对称 in *.
    spliter.
    ex_and H0 M0.
    induction H2.
      assert (HH:= H2).
      apply 垂直推出不重合 in HH.
      spliter.
      induction (两点重合的决定性 M0 X).
        subst X.
        unfold 中点 in *.
        spliter.
        Cong.
      assert (Perp M0 X P' P).
        eapply 与垂线共线之线也为垂线2;eauto.
      assert(~ Col A B P /\ Per P M0 X).
        eapply l8_16_1_共线四点和一垂直推另一直角.
          assumption.
          assumption.
          auto.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          intro.
          subst P.
          apply M是AB中点则M是BA中点 in H0.
          apply A是AB中点则A与B重合 in H0.
          subst P'.
          absurde.
          apply 垂直的左交换性.
          apply 垂直的对称性.
          apply H2; eapply 垂直的左交换性.
        unfold Col.
        right; left.
        apply midpoint_bet.
        assumption.
      spliter.
      eapply 直角的对称性 in H9.
      unfold Per in H9.
      ex_and H9 P0.
      assert (P0 = P').
        eapply 中点组的唯一性1.
          apply H9.
        apply M是AB中点则M是BA中点.
        assumption.
      subst P0.
      apply 等长的交换性.
      assumption.
    subst P'.
    apply 等长的自反性.
Qed.

Lemma is_image_spec_col_cong : forall A B P P' X,
 严格对称 P P' A B -> Col A B X -> Cong P X P' X.
Proof.
    intros.
    unfold 严格对称 in *.
    spliter.
    ex_and H M0.
    induction H1.
      assert (HH:= H1).
      apply 垂直推出不重合 in HH.
      spliter.
      induction (两点重合的决定性 M0 X).
        subst X.
        unfold 中点 in *.
        spliter.
        Cong.
      assert (Perp M0 X P' P) by (eauto using 与垂线共线之线也为垂线2).
      assert(~ Col A B P /\ Per P M0 X).
        eapply l8_16_1_共线四点和一垂直推另一直角.
          assumption.
          assumption.
          auto.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          intro.
          subst P.
          apply M是AB中点则M是BA中点 in H.
          apply A是AB中点则A与B重合 in H.
          subst P'.
          absurde.
          apply 垂直的左交换性.
          apply 垂直的对称性.
          apply H1; eapply 垂直的左交换性.
        unfold Col.
        right; left.
        apply midpoint_bet.
        assumption.
      spliter.
      eapply 直角的对称性 in H8.
      unfold Per in H8.
      ex_and H8 P0.
      assert (P0 = P').
        eapply 中点组的唯一性1.
          apply H8.
        apply M是AB中点则M是BA中点.
        assumption.
      subst P0.
      Cong.
    subst.
    Cong.
Qed.

Lemma image_id : forall A B T T',
  A<>B ->
  Col A B T ->
  对称 T T' A B ->
  T = T'.
Proof.
    intros.
    rewrite is_image_is_image_spec in H1 by apply H.
    unfold 严格对称 in H1.
    spliter.
    ex_and H1 X.
    induction H2.
      assert (A <> B /\ T' <> T).
        apply 垂直推出不重合 in H2.
        spliter.
        split; assumption.
      spliter.
      induction (两点重合的决定性 A X).
        subst X.
        assert (Perp A B T' A).
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            intro.
            subst T'.
            apply A是AB中点则A与B重合 in H1.
            subst A.
            absurde.
            apply 垂直的对称性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          assumption.
        assert (~ Col  A T' B).
          apply L形垂直推出不共线.
          apply 垂直的交换性.
          apply 垂直的对称性.
          assumption.
        assert (A = T).
          apply l6_21_两线交点的唯一性 with A T' B T; Col.
          intro; treat_equalities; Col.
        subst A.
        apply M是AB中点则M是BA中点 in H1.
        apply A是AB中点则A与B重合 in H1.
        subst T'.
        absurde.
      induction (两点重合的决定性 B X).
        subst X.
        assert (Perp A B T' B).
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            intro.
            subst T'.
            apply A是AB中点则A与B重合 in H1.
            subst B.
            absurde.
            apply 垂直的对称性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          assumption.
        assert (~ Col  B T' A).
          apply L形垂直推出不共线.
          apply 垂直的左交换性.
          apply 垂直的对称性.
          assumption.
        assert (B = T).
          eapply l6_21_两线交点的唯一性.
            apply H8.
            apply H4.
            apply ABA型共线.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply M是AB中点则M是BA中点.
            apply H1.
            apply ABB型共线.
            assumption.
        subst B.
        apply M是AB中点则M是BA中点 in H1.
        apply A是AB中点则A与B重合 in H1.
        subst T'.
        absurde.
      assert (Col A X T) by ColR.
      assert (Perp A B T' X).
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          intro.
          subst T'.
          apply A是AB中点则A与B重合 in H1.
          subst X.
          absurde.
          apply 垂直的对称性.
          apply H2.
        assert_cols.
        Col.
      assert (~ Col  X T' A).
        apply L形垂直推出不共线.
        apply 垂直的左交换性.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply H9.
        assumption.
      assert (X = T).
        eapply l6_21_两线交点的唯一性.
          apply H10.
          apply H6.
          apply ABA型共线.
          unfold Col.
          right; right.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          apply H1.
          apply ABB型共线.
          assumption.
      subst X.
      apply M是AB中点则M是BA中点 in H1.
      apply A是AB中点则A与B重合 in H1.
      subst T'.
      absurde.
    subst T'.
    reflexivity.
Qed.

Lemma osym_not_col : forall A B P P',
 对称 P P' A B ->
 ~ Col A B P -> ~ Col A B P'.
Proof.
    intros.
    unfold 对称 in *.
    induction H.
      spliter.
      assert ( HH:= H1).
      unfold 严格对称 in HH.
      spliter.
      ex_and H2 T.
      intro.
      induction H3.
        assert (P'=P).
          eapply image_id.
            apply H.
            assumption.
          apply l10_4.
          apply is_image_is_image_spec.
            assumption.
          assumption.
        subst P'.
        apply 垂直推出不重合 in H3.
        spliter.
        absurde.
      apply H0.
      subst P'.
      assumption.
    spliter. subst. Col5.
Qed.

Lemma midpoint_preserves_image : forall A B P P' Q Q' M,
 A <> B -> Col A B M -> 对称 P P' A B ->
 中点 M P Q -> 中点 M P' Q' -> 对称 Q Q' A B.
Proof.
    intros.
    rewrite is_image_is_image_spec in * by apply H.
    assert (HH1:=H1).
    unfold 严格对称 in H1.
    spliter.
    ex_and H1 X.
    induction H4.
      double X M Y.
      assert (中点 Y Q Q').
        eapply 对称保持中点.
          apply H2.
          apply H6.
          apply H3.
        apply M是AB中点则M是BA中点.
        apply H1.
      assert (P <> P').
        intro.
        subst P'.
        apply 垂直推出不重合 in H4.
        spliter.
        absurde.
      assert (Q <> Q').
        intro.
        subst Q'.
        apply M是AA中点则M与A重合 in H7.
        subst Q.
        assert (P=P').
          eapply 中点组的唯一性2.
            apply H2.
          apply H3.
        subst P'.
        apply 垂直推出不重合 in H4.
        spliter.
        absurde.
      split.
        exists Y.
        split.
          apply M是AB中点则M是BA中点.
          apply H7.
        induction (两点重合的决定性 X Y).
          subst Y.
          assumption.
        assert_diffs.
        ColR.
      left.
      assert(Per M Y Q).
        unfold Per.
        exists Q'.
        split.
          assumption.
        unfold 中点 in *.
        spliter.
        eapply 等长的传递性.
          apply 等长的对称性.
          apply H14.
        apply 等长的对称性.
        eapply 等长的传递性.
          apply 等长的对称性.
          apply H13.
        eapply is_image_col_cong.
          apply H.
          apply l10_4.
          apply is_image_is_image_spec.
            assumption.
          apply HH1.
        assumption.
      induction (两点重合的决定性 X Y).
        subst Y.
        apply M是AA中点则M与A重合 in H6.
        subst X.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1 with P'.
          auto.
          apply 垂直的左交换性.
          apply 垂线共线点也构成垂直1 with P.
            intro.
            subst Q'.
            apply M是AA中点则M与A重合 in H3.
            subst P'.
            apply A是AB中点则A与B重合 in H1.
            subst P.
            absurde.
            apply 垂直的对称性.
            apply H4.
          eapply (共线的传递性3 M).
            intro.
            subst P'.
            apply A是AB中点则A与B重合 in H1.
            subst P.
            absurde.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply M是AB中点则M是BA中点.
            assumption.
          unfold Col.
          right; right.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          assumption.
        eapply (共线的传递性3 M).
          intro.
          subst Q'.
          apply M是AB中点则M是BA中点 in H7.
          apply A是AB中点则A与B重合 in H7.
          subst Q.
          absurde.
          unfold Col.
          right; right.
          apply midpoint_bet.
          assumption.
        unfold Col.
        right; right.
        apply midpoint_bet.
        assumption.
      apply 直角转L形垂直于 in H10.
        apply 垂直于转T形垂直 in H10.
        induction H10.
          apply 垂直推出不重合 in H10.
          spliter.
          absurde.
        apply 垂直的交换性.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          assumption.
          apply 垂直的交换性.
          eapply (垂线共线点也构成垂直1  Y Q).
            intro.
            subst Q.
            apply 垂直推出不重合 in H10.
            spliter.
            absurde.
            apply 垂直的对称性.
            induction (两点重合的决定性 A M).
              subst A.
              apply 垂直的左交换性.
              eapply (垂线共线点也构成垂直1 _ M).
                auto.
                apply 垂直的左交换性.
                eapply (垂线共线点也构成垂直1 _ Y).
                  assumption.
                  assumption.
                induction (两点重合的决定性 M X).
                  subst X.
                  apply A是AB中点则A与B重合 in H6.
                  subst M.
                  apply AAB型共线.
                eapply (共线的传递性2 _ X).
                  assumption.
                  unfold Col.
                  right; right.
                  apply midpoint_bet.
                  apply M是AB中点则M是BA中点.
                  assumption.
                apply 等价共线ACB.
                assumption.
              apply ABB型共线.
            induction (两点重合的决定性 B M).
              subst M.
              apply 垂直的左交换性.
              apply (垂线共线点也构成垂直1 _ Y).
                auto.
                assumption.
              induction (两点重合的决定性 B X).
                subst X.
                apply A是AB中点则A与B重合 in H6.
                subst Y.
                absurde.
              eapply 共线的传递性2.
                apply H13.
                unfold Col.
                right; right.
                apply midpoint_bet.
                apply M是AB中点则M是BA中点.
                assumption.
              apply 等价共线BCA.
              assumption.
            eapply 垂线共线点也构成垂直1.
              assumption.
              apply 垂直的左交换性.
              eapply (垂线共线点也构成垂直1 M Y).
                auto.
                assumption.
              assert(Col B X M).
                eapply 共线的传递性3.
                  apply H.
                  assumption.
                assumption.
              induction (两点重合的决定性 M X).
                subst X.
                apply A是AB中点则A与B重合 in H6.
                contradiction.
              assert(Col B Y M).
                apply 等价共线BCA.
                eapply (共线的传递性3  X).
                  auto.
                  apply 等价共线BCA.
                  assumption.
                unfold Col.
                left.
                apply midpoint_bet.
                assumption.
              eapply (共线的传递性2 _ B).
                auto.
                apply 等价共线CAB.
                assumption.
              apply 等价共线CBA.
              apply H0.
            apply 等价共线ACB.
            apply H0.
          apply ABB型共线.
        unfold Col.
        left.
        apply midpoint_bet.
        apply H7.
        intro.
        subst Y.
        apply M是AB中点则M是BA中点 in H6.
        apply A是AB中点则A与B重合 in H6.
        subst X.
        absurde.
      intro.
      subst Q.
      apply A是AB中点则A与B重合 in H7.
      subst Q'.
      absurde.
    subst P'.
    apply M是AA中点则M与A重合 in H1.
    subst P.
    assert(Q = Q').
      eapply 中点组的唯一性2.
        apply M是AB中点则M是BA中点.
        apply H2.
      apply M是AB中点则M是BA中点.
      apply H3.
    subst Q'.
    split.
      exists Q.
      split.
        apply A是AA中点.
      induction (两点重合的决定性 M X).
        subst X.
        assert(M=Q).
          apply A是AB中点则A与B重合.
          assumption.
        subst Q.
        assumption.
      ColR.
    right.
    reflexivity.
Qed.

Lemma image_in_is_image_spec :
 forall M A B P P',
  严格对称于 M P P' A B -> 严格对称 P P' A B.
Proof.
    intros.
    unfold 严格对称于 in H.
    spliter.
    unfold 严格对称.
    split.
      exists M.
      split; assumption.
    assumption.
Qed.

Lemma image_in_gen_is_image : forall M A B P P',
 对称于 M P P' A B  -> 对称 P P' A B.
Proof.
    intros.
    unfold 对称于 in H.
    induction H.
      spliter.
      apply image_in_is_image_spec in H0.
      unfold 对称.
      tauto.
    spliter.
    subst.
    subst.
    unfold 对称.
    right.
    auto.
Qed.

Lemma image_image_in : forall A B P P' M,
 P <> P'-> 严格对称 P P' A B -> Col A B M -> Col P M P' ->
 严格对称于 M P P' A B.
Proof.
    intros.
    unfold 严格对称于.
    split.
      split.
        assert(HH:=H0).
        unfold 严格对称 in H0.
        spliter.
        ex_and H0 M'.
        induction H3.
          assert (Perp P M' A B).
            eapply 垂线共线点也构成垂直1.
              intro.
              subst P.
              apply M是AB中点则M是BA中点 in H0.
              apply A是AB中点则A与B重合 in H0.
              subst P'.
              apply 垂直推出不重合 in H3.
              spliter.
              absurde.
              apply 垂直的对称性.
              apply 垂直的右交换性.
              apply H3.
            unfold Col.
            right; left.
            apply midpoint_bet.
            assumption.
          assert (M'=M).
            apply (l6_21_两线交点的唯一性 A B P P'); Col.
              induction (两点重合的决定性 A M').
                subst M'.
                assert (~ Col A B P /\ Per P A B).
                  eapply l8_16_1_共线四点和一垂直推另一直角.
                    apply ABA型共线.
                    apply ABB型共线.
                    apply 垂直推出不重合 in H3.
                    spliter.
                    auto.
                  apply 垂直的对称性.
                  assumption.
                spliter.
                intro.
                apply H6.
                assumption.
              assert (~ Col A B P /\ Per P M' A).
                eapply l8_16_1_共线四点和一垂直推另一直角.
                  assumption.
                  apply ABA型共线.
                apply 垂直的对称性.
                assumption.
              spliter.
              intro.
              apply H7.
              assumption.
            apply 垂直推出不重合 in H3.
            spliter.
            auto.
          subst M'.
          assumption.
        subst P'.
        absurde.
      assumption.
    assert (HH:=H0).
    unfold 严格对称 in H0.
    spliter.
    induction H3.
      left.
      assumption.
    right.
    assumption.
Qed.

Lemma image_in_col : forall A B P P' Y : Tpoint,
 严格对称于 Y P P' A B -> Col P P' Y.
Proof.
    intros.
    unfold 严格对称于 in *.
    spliter.
    assert_cols.
    Col.
Qed.

Lemma is_image_spec_rev : forall P P' A B, 严格对称 P P' A B -> 严格对称 P P' B A.
Proof.
    unfold 严格对称.
    intros.
    spliter.
    split.
      ex_and H M0.
      exists M0.
      split.
        assumption.
      apply 等价共线BAC.
      assumption.
    induction H0.
      left.
      apply 垂直的左交换性.
      assumption.
    right.
    assumption.
Qed.

Lemma is_image_rev : forall P P' A B,
 对称 P P' A B -> 对称 P P' B A.
Proof.
    intros.
    unfold 对称 in *.
    induction H.
      spliter.
      left.
      split.
        auto.
      apply is_image_spec_rev.
      assumption.
    right.
    spliter. subst. tauto.
Qed.

Lemma midpoint_preserves_per : forall A B C A1 B1 C1 M,
 Per A B C ->
 中点 M A A1 ->
 中点 M B B1 ->
 中点 M C C1 ->
 Per A1 B1 C1.
Proof.
    intros.
    unfold Per in *.
    ex_and H C'.
    double C' M C1'.
    exists C1'.
    split.
      eapply 对称保持中点.
        apply H2.
        apply H1.
        apply H4.
      assumption.
    eapply l7_16.
      apply H0.
      apply H2.
      apply H0.
      apply H4.
    assumption.
Qed.

Lemma col__image_spec : forall A B X, Col A B X -> 严格对称 X X A B.
Proof.
    intros.
    unfold 严格对称.
    split.
      exists X.
      split.
        apply A是AA中点.
      assumption.
    right.
    reflexivity.
Qed.

Lemma image_triv : forall A B, 对称 A A A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      right; split; 中点.
    left; split.
      auto.
    apply col__image_spec; Col.
Qed.

Lemma cong_midpoint__image : forall A B X Y, Cong A X A Y -> 中点 B X Y -> 对称 Y X A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      right; subst; split; auto.
    left; repeat split; auto.
      exists B; split; Col.
    induction(两点重合的决定性 X Y).
      right.
      assumption.
    left.
    apply 垂直的对称性.
    assert(B <> X /\ B <> Y).
      apply 严格中点组推论1.
        assumption.
      assumption.
    spliter.
      apply 直角加共线转L形垂直; Col.
    exists Y.
    split.
      assumption.
    assumption.
Qed.

Lemma col_image_spec__eq : forall A B P P', Col A B P -> 严格对称 P P' A B -> P = P'.
Proof.
    intros.
    apply (l10_6_uniqueness_spec A B P).
      apply col__image_spec; assumption.
      assumption.
Qed.

Lemma image_spec_triv : forall A B, 严格对称 A A B B.
Proof.
    intros.
    apply col__image_spec.
    Col.
Qed.

Lemma image_spec__eq : forall A P P', 严格对称 P P' A A -> P = P'.
Proof.
    intros A P P'; apply col_image_spec__eq; Col.
Qed.

Lemma image__midpoint : forall A P P', 对称 P P' A A -> 中点 A P' P.
Proof.
    induction 1; spliter.
      contradiction.
      assumption.
Qed.

Lemma is_image_spec_dec :
  forall A B C D, 严格对称 A B C D \/ ~ 严格对称 A B C D.
Proof.
    intros.
    elim (两点重合的决定性 C D); intro HCD.
      subst.
      elim (两点重合的决定性 A B); intro HAB.
        subst.
        left.
        apply image_spec_triv.
      right.
      intro H.
      unfold 严格对称 in *.
      destruct H as [H HFalse].
      elim HFalse; clear HFalse; intro HFalse.
        apply 垂直推出不重合 in HFalse.
        intuition.
      intuition.
    elim (l10_6_existence_spec C D A HCD); intros B' HB'.
    elim (两点重合的决定性 B B'); intro HBB'.
      subst.
      tauto.
    right.
    intro H.
    apply HBB'.
    apply l10_6_uniqueness with C D A.
      unfold 对称.
      tauto.
    unfold 对称.
    tauto.
Qed.

Lemma l10_14 : forall P P' A B, P <> P' -> A <> B ->
 对称 P P' A B -> TS A B P P'.
Proof.
    intros.
    rewrite is_image_is_image_spec in H1 by apply H0.
    unfold 严格对称 in H1.
    spliter.
    ex_and H1 M0.
    induction H2.
      assert (P <> M0).
        intro.
        subst P.
        apply M是AB中点则M是BA中点 in H1.
        apply A是AB中点则A与B重合 in H1.
        subst P'.
        absurde.
      induction (两点重合的决定性 A M0).
        subst A.
        assert (Perp M0 B P M0).
          apply 垂直的对称性.
          eapply (垂线共线点也构成垂直1 _ P').
            assumption.
            apply 垂直的对称性.
            apply 垂直的右交换性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (垂直于 M0 M0 B P M0).
          eapply L形垂直转垂直于.
          assumption.
        assert(Per B M0 P).
          eapply L形垂直于转直角.
          apply 垂直于的交换性.
          assumption.
        assert (B <> M0).
          intro.
          repeat split.
          subst B.
          apply 垂直推出不重合 in H2.
          spliter.
          absurde.
        assert (~Col B M0 P).
          eapply 成直角三点不共线.
            assumption.
            auto.
          assumption.
        repeat split.
          auto.
          intro.
          apply H9.
          Col.
          intro.
          apply H9.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ P').
            intro.
            subst P'.
            apply A是AB中点则A与B重合 in H1.
            subst P.
            absurde.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply M是AB中点则M是BA中点.
            assumption.
          apply 等价共线BAC.
          assumption.
        exists M0.
        split.
          apply AAB型共线.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      induction (两点重合的决定性 B M0).
        subst B.
        assert (Perp M0 A P M0).
          apply 垂直的对称性.
          eapply (垂线共线点也构成垂直1 _ P').
            assumption.
            apply 垂直的对称性.
            apply 垂直的交换性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (垂直于 M0 M0 A P M0).
          eapply L形垂直转垂直于.
          assumption.
        assert(Per A M0 P).
          eapply L形垂直于转直角.
          apply 垂直于的交换性.
          assumption.
        repeat split.
          assert (~Col A M0 P).
            eapply 成直角三点不共线.
              assumption.
              auto.
            assumption.
          intro.
          apply H9.
          apply 等价共线BCA.
          assumption.
          intro.
          assert (Col M0 A P).
            eapply (共线的传递性2 _ P').
              intro.
              subst P'.
              apply A是AB中点则A与B重合 in H1.
              subst P.
              absurde.
              apply 等价共线CAB.
              assumption.
            unfold Col.
            right; right.
            apply midpoint_bet.
            apply M是AB中点则M是BA中点.
            assumption.
          apply (成直角三点不共线 A M0 P); auto.
          apply 等价共线BAC.
          assumption.
        exists M0.
        split.
          apply ABA型共线.
        apply midpoint_bet.
        apply M是AB中点则M是BA中点.
        assumption.
      repeat split.
        assert(Perp  P M0 A B).
          eapply 垂线共线点也构成垂直1.
            assumption.
            apply 垂直的对称性.
            apply 垂直的右交换性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        assert (~ Col M0 P A).
          apply L形垂直推出不共线.
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            assumption.
            apply 垂直的对称性.
            apply 垂直的左交换性.
            apply H7.
          assumption.
        intro.
        apply H8.
        apply 等价共线BCA.
        eapply 共线的传递性2.
          apply 垂直推出不重合 in H2.
          spliter.
          apply H2.
          assumption.
        apply 等价共线BCA.
        assumption.
        assert(Perp  P' M0 A B).
          eapply 垂线共线点也构成垂直1.
            intro.
            subst P'.
            apply A是AB中点则A与B重合 in H1.
            subst P.
            absurde.
            apply 垂直的对称性.
            apply H2.
          unfold Col.
          right; left.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          assumption.
        assert (~ Col M0 P' A).
          apply L形垂直推出不共线.
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            assumption.
            apply 垂直的对称性.
            apply 垂直的左交换性.
            apply H7.
          assumption.
        intro.
        apply H8.
        apply 等价共线BCA.
        eapply 共线的传递性2.
          apply 垂直推出不重合 in H2.
          spliter.
          apply H2.
          assumption.
        apply 等价共线BCA.
        assumption.
      exists M0.
      split.
        apply 等价共线CAB.
        assumption.
      apply midpoint_bet.
      apply M是AB中点则M是BA中点.
      assumption.
    subst P'.
    absurde.
Qed.

Lemma l10_15 : forall A B C P,
 Col A B C -> ~ Col A B P ->
 exists Q, Perp A B Q C /\ OS A B P Q.
Proof.
    intros.
    assert (A<>B).
      intro;subst.
      Col.
    assert (exists X , TS A B P X).
      apply l9_10.
      intro.
      apply H0.
      apply 等价共线BCA.
      assumption.
    ex_elim H2 X.
    induction (两点重合的决定性 A C).
      subst C.
      assert (exists Q, exists T, Perp A B Q A /\ Col A B T /\ Bet X T Q).
        apply 十字上的中间性.
        assumption.
      ex_elim H2 Q.
      ex_and H4 T.
      exists Q.
      split.
        assumption.
      eapply l9_8_1.
        apply H3.
      unfold TS.
      repeat split.
        apply L形垂直推出不共线 in H2.
        intro.
        apply H2.
        apply 等价共线BCA.
        assumption.
        unfold TS in H3.
        spliter.
        assumption.
      exists T.
      split.
        apply 等价共线CAB.
        assumption.
      apply 中间性的对称性.
      assumption.
    assert (exists Q, exists T, Perp C A Q C /\ Col C A T /\ Bet X T Q).
      apply 十字上的中间性.
      auto.
    ex_elim H4 Q.
    ex_and H5 T.
    exists Q.
    split.
      eapply 垂线共线点也构成垂直1.
        assumption.
        apply 垂直的左交换性.
        apply H4.
      apply 等价共线ACB.
      assumption.
    eapply l9_8_1.
      apply H3.
    unfold TS.
    repeat split.
      eapply L形垂直推出不共线 in H4.
      intro.
      apply H4.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H1.
        apply 等价共线BCA.
        assumption.
      assumption.
      unfold TS in H3.
      spliter.
      assumption.
    exists T.
    split.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H2.
        apply 等价共线ACB.
        assumption.
      apply 等价共线BAC.
      assumption.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma ex_四点成首末边等长双直角S形则对边等长 : forall A B C D X Y,
 A <> B -> X <> Y -> Col A B C -> ~Col A B D ->
 exists P, Per P C A /\ Cong P C X Y /\ OS A B P D.
Proof.
    intros A B C D X Y HAB HXY HCol HNCol.
    destruct (l10_15 A B C D) as [Q [HQ1 HQ2]]; trivial.
    assert_diffs.
    destruct (由一点往一方向构造等长线段_3 C Q X Y) as [P [HP1 HP2]]; auto.
    exists P; repeat split; Cong.
    - destruct (两点重合的决定性 A C).
        subst; Perp.
      apply L形垂直转直角1.
      apply 垂线共线点也构成垂直2 with B; auto.
      assert_diffs; apply 垂直的对称性, 垂线共线点也构成垂直2 with Q; Col; Perp.
    - apply os_out_os with Q C; Side.
Qed.

Lemma exists_cong_per : forall A B X Y, exists C, Per A B C /\ Cong B C X Y.
Proof.
intros.
destruct (两点重合的决定性 A B).
subst.
destruct (由一点往一方向构造等长线段 X B X Y).
exists x;split;spliter;Perp.
destruct (两点不重合则存在不共线的点 A B H) as [P HP].
destruct (两点重合的决定性 X Y).
subst;exists B;split;[Perp|Cong].
destruct (ex_四点成首末边等长双直角S形则对边等长 A B B P X Y); Col.
spliter.
exists x;split;[Perp|Cong].
Qed.

End T10.
