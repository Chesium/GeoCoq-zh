Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_2.
Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity.

Section T10_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma cop__cong_on_bissect : forall A B M P X,
 共面 A B X P -> 中点 M A B -> 垂直于 M A B P M -> Cong X A X B ->
 Col M P X.
Proof.
intros.
assert(X = M \/ ~ Col A B X /\ 垂直于 M X M A B).
assert_diffs; apply(cong_perp_or_mid A B M X); Cong.
induction H3.
treat_equalities; Col.
spliter.
apply perp_in_perp in H1.
apply perp_in_perp in H4.
assert_cols.
apply(cop_perp2__col _ _ _ A B); Perp; Cop.
Qed.

Lemma cong_cop_mid_perp__col : forall A B M P X,
 共面 A B X P -> Cong A X B X -> 中点 M A B -> Perp A B P M -> Col M P X.
Proof.
intros.
apply (cop__cong_on_bissect A B); Cong.
apply l8_15_1; Col.
Qed.

Lemma cop_image_in2__col : forall A B P P' Q Q' M,
 共面 A B P Q -> 严格对称于 M P P' A B -> 严格对称于 M Q Q' A B ->
 Col M P Q.
Proof.
    intros.
    assert(严格对称 P P' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    assert(严格对称 Q Q' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    unfold 严格对称于 in *.
    spliter.
    induction H4.
      induction H6.
        induction (两点重合的决定性 A M).
          subst M.
          assert (Per B A P).
            unfold Per.
            exists P'.
            split.
              apply M是AB中点则M是BA中点.
              assumption.
            apply 等长的交换性.
            eapply is_image_spec_col_cong with A B;Col.
          assert (Per B A Q).
            unfold Per.
            exists Q'.
            split.
              apply M是AB中点则M是BA中点.
              assumption.
            apply 等长的交换性.
            eapply is_image_spec_col_cong with A B;Col.
          apply 等价共线CAB.

          apply cop_per2__col with B.
            Cop.
            apply perp_distinct in H4.
            spliter.
            auto.
            apply l8_2.
            apply H8.
          apply l8_2.
          assumption.
        assert (Per A M P).
          unfold Per.
          exists P'.
          split.
            apply M是AB中点则M是BA中点.
            assumption.
          apply 等长的交换性.
          eapply is_image_spec_col_cong.
            apply H2.
          Col.
        assert (Per A M Q).
          unfold Per.
          exists Q'.
          split.
            apply M是AB中点则M是BA中点.
            assumption.
          apply 等长的交换性.
          eapply is_image_spec_col_cong.
            apply H3.
          apply ABA型共线.
        apply 等价共线CAB.
        apply cop_per2__col with A.
          assert_diffs; apply coplanar_perm_12, col_cop__cop with B; Cop.
          auto.
          apply l8_2.
          apply H9.
          auto.
        apply l8_2.
        assumption.
      subst P'.
      apply M是AA中点则M与A重合 in H0.
      subst P.
      Col.
    subst Q'.
    apply M是AA中点则M与A重合 in H1.
    subst Q.
    Col.
Qed.

Lemma l10_10_spec : forall A B P Q P' Q',
 严格对称 P' P A B -> 严格对称 Q' Q A B ->
 Cong P Q P' Q'.
Proof.
    intros.
    destruct (两点重合的决定性 A B).
      subst B.
      assert (P' = P) by (apply (image_spec__eq A); assumption).
      assert (Q' = Q) by (apply (image_spec__eq A); assumption).
      subst; Cong.
    assert(HH0 := H).
    assert(HH1 := H0).
    unfold 严格对称 in H.
    unfold 严格对称 in H0.
    spliter.
    ex_and H X.
    ex_and H0 Y.
    assert (exists M, 中点 M X Y).
      apply midpoint_existence.
    ex_elim H6 Z.
    assert (Col A B Z).
      induction (两点重合的决定性 X Y).
        subst Y.
        apply M是AA中点则M与A重合 in H7.
        subst X.
        assumption.
      ColR.
    double P Z R.
    double P' Z R'.
    apply 等长的交换性.
    induction H3.
      induction H2.
        assert (严格对称 R R' A B).
          apply is_image_is_image_spec .
            assumption.
          eapply (midpoint_preserves_image ) with P P' Z.
            assumption.
            assumption.
            apply l10_4.
            apply is_image_is_image_spec;auto.
            assumption.
          assumption.
        assert(R <> R').
          intro.
          subst R'.
          assert( P' = P).
            eapply 中点组的唯一性2.
              apply H9.
            assumption.
          subst P'.
          apply perp_distinct in H3.
          spliter.
          absurde.
        assert (中点 Y R R') by (eauto using 对称保持中点).
        assert (Cong Q' R' Q R) by (apply (l7_13_同中点组两侧等长 Y); assumption).
        assert (Cong P' Z P Z) by (apply (is_image_spec_col_cong A B); assumption).
        assert (Cong Q' Z Q Z) by (apply (is_image_spec_col_cong A B); assumption).
        apply 等长的交换性, (五线段公理_等价SAS R R' Z Z); Cong; Between.
          apply 等长的传递性 with P Z; [|apply 等长的传递性 with P' Z]; Cong.
          intro; treat_equalities; contradiction.
      subst Q'.
      apply M是AA中点则M与A重合 in H0.
      subst Q.
      apply 等长的交换性.
      eapply is_image_spec_col_cong.
        apply l10_4_spec.
        apply HH0.
      assumption.
    subst P'.
    apply M是AA中点则M与A重合 in H.
    subst P.
    eapply is_image_spec_col_cong.
      apply l10_4_spec.
      apply HH1.
    assumption.
Qed.

Lemma l10_10 : forall A B P Q P' Q',
 对称 P' P A B -> 对称 Q' Q A B ->
 Cong P Q P' Q'.
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
      apply l7_13_同中点组两侧等长 with B; apply M是AB中点则M是BA中点;auto.
    apply l10_10_spec with A B;try apply is_image_is_image_spec;assumption.
Qed.

Lemma image_preserves_bet : forall A B C A' B' C' X Y,
  严格对称 A A' X Y -> 严格对称 B B' X Y -> 严格对称 C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    destruct (两点重合的决定性 X Y).
      subst Y.
      apply image_spec__eq in H.
      apply image_spec__eq in H0.
      apply image_spec__eq in H1.
      subst; assumption.
    eapply l4_6.
      apply H2.
    unfold 三角形全等.
    repeat split; apply l10_10_spec with X Y.
      apply l10_4_spec.
      apply H.
      apply l10_4_spec; assumption.
      apply l10_4_spec.
      apply H.
      apply l10_4_spec.
      assumption.
      apply l10_4_spec.
      apply H0.
    apply l10_4_spec.
    assumption.
Qed.

Lemma image_gen_preserves_bet : forall A B C A' B' C' X Y,
  对称 A A' X Y ->
  对称 B B' X Y ->
  对称 C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    destruct (两点重合的决定性 X Y).
      subst Y.
      apply image__midpoint in H.
      apply image__midpoint in H0.
      apply image__midpoint in H1.
      subst.
      apply l7_15 with A B C X; 中点.
    eapply image_preserves_bet;try apply is_image_is_image_spec; eauto.
Qed.

Lemma image_preserves_col : forall A B C A' B' C' X Y,
  严格对称 A A' X Y -> 严格对称 B B' X Y -> 严格对称 C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    destruct H2 as [HBet|[HBet|HBet]]; [|apply 等价共线CAB|apply 等价共线BCA];
    apply 中间性蕴含共线1; eapply image_preserves_bet; eauto.
Qed.

Lemma image_gen_preserves_col : forall A B C A' B' C' X Y,
  对称 A A' X Y -> 对称 B B' X Y -> 对称 C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    destruct H2 as [HBet|[HBet|HBet]]; [|apply 等价共线CAB|apply 等价共线BCA];
    apply 中间性蕴含共线1; eapply image_gen_preserves_bet; eauto.
Qed.

Lemma image_gen_preserves_ncol : forall A B C A' B' C' X Y,
  对称 A A' X Y -> 对称 B B' X Y -> 对称 C C' X Y ->
  ~ Col A B C ->
  ~ Col A' B' C'.
Proof.
    intros.
    intro.
    apply H2, image_gen_preserves_col with A' B' C' X Y; try (apply l10_4); assumption.
Qed.

Lemma image_gen_preserves_inter : forall A B C D I A' B' C' D' I' X Y,
  对称 A A' X Y -> 对称 B B' X Y -> 对称 C C' X Y -> 对称 D D' X Y ->
  ~ Col A B C -> C <> D ->
  Col A B I -> Col C D I -> Col A' B' I' -> Col C' D' I' ->
  对称 I I' X Y.
Proof.
    intros.
    destruct (l10_6_existence X Y I) as [I0 HI0]; trivial.
    assert (I' = I0); [|subst; assumption].
    apply (l6_21_两线交点的唯一性 A' B' C' D'); trivial.
      apply image_gen_preserves_ncol with A B C X Y; assumption.
      intro; subst D'; apply H4, l10_2_uniqueness with X Y C'; assumption.
      apply image_gen_preserves_col with A B I X Y; assumption.
      apply image_gen_preserves_col with C D I X Y; assumption.
Qed.

Lemma intersection_with_image_gen : forall A B C A' B' X Y,
  对称 A A' X Y -> 对称 B B' X Y ->
  ~ Col A B A' -> Col A B C -> Col A' B' C ->
  Col C X Y.
Proof.
    intros.
    apply l10_8.
    assert (对称 A' A X Y) by (apply l10_4; assumption).
    assert (~ Col A' B' A) by (apply image_gen_preserves_ncol with A B A' X Y; trivial).
    assert_diffs.
    apply image_gen_preserves_inter with A B A' B' A' B' A B; trivial.
    apply l10_4; assumption.
Qed.

Lemma image_preserves_midpoint :
 forall A B C A' B' C' X Y,
 严格对称 A A' X Y -> 严格对称 B B' X Y -> 严格对称 C C' X Y ->
 中点 A B C ->
 中点 A' B' C'.
Proof.
    intros.
    unfold 中点 in *.
    spliter.
    repeat split.
      eapply image_preserves_bet.
        apply H0.
        apply H.
        apply H1.
        apply H2.
    eapply 等长的传递性.
      eapply l10_10_spec.
        apply H0.
      apply H.
    eapply 等长的传递性.
      apply H3.
    eapply l10_10_spec.
      apply l10_4_spec.
      apply H.
    apply l10_4_spec.
    apply H1.
Qed.


Lemma image_spec_preserves_per : forall A B C A' B' C' X Y,
 严格对称 A A' X Y -> 严格对称 B B' X Y -> 严格对称 C C' X Y ->
 Per A B C ->
 Per A' B' C'.
Proof.
    intros.
    induction (两点重合的决定性 X Y).
      subst Y.
      apply image_spec__eq in H.
      apply image_spec__eq in H0.
      apply image_spec__eq in H1.
      subst; assumption.
    double C B C1.
    assert (exists C1', 严格对称 C1 C1' X Y).
      apply l10_6_existence_spec.
      assumption.
    ex_and H5 C1'.
    unfold Per.
    exists C1'.
    split.
      eapply image_preserves_midpoint.
        apply H0.
        apply H1.
        apply H6.
      assumption.
    eapply 等长的传递性.
      eapply l10_10_spec.
        apply H.
      apply H1.
    eapply 等长的传递性.
      unfold Per in H2.
      ex_and H2 C2.
      assert (C2=C1).
        eapply 中点组的唯一性1.
          apply H2.
        assumption.
      subst C2.
      apply H5.
    eapply l10_10_spec.
      apply l10_4_spec.
      apply H.
    apply l10_4_spec.
    assumption.
Qed.

Lemma image_preserves_per : forall A B C A' B' C' X Y,
 对称 A A' X Y -> 对称 B B' X Y -> 对称 C C' X Y ->
 Per A B C ->
 Per A' B' C'.
Proof.
    intros.
    induction (两点重合的决定性 X Y).
    - induction H; induction H0; induction H1; spliter; [contradiction..|].
      treat_equalities.
      apply midpoint_preserves_per with A B C X; [|apply M是AB中点则M是BA中点..]; assumption.
    - induction H; induction H0; induction H1; spliter; [|contradiction..].
      apply image_spec_preserves_per with A B C X Y; assumption.
Qed.

Lemma l10_12 : forall A B C A' B' C',
 Per A B C -> Per A' B' C' ->
 Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    induction (两点重合的决定性 B C).
      treat_equalities;auto.
    induction (两点重合的决定性 A B).
      treat_equalities;auto.
    assert (exists X, 中点 X B B').
      apply midpoint_existence.
    ex_and H5 X.
    double A' X A1.
    double C' X C1.
    assert(三角形全等 A' B' C' A1 B C1)
    by (repeat split;eauto using l7_13_同中点组两侧等长, M是AB中点则M是BA中点).
    assert (Per A1 B C1)
      by (eauto using l8_10).
    unfold 三角形全等 in H8.
    spliter.
    assert(Cong A B A1 B) by (apply 等长的传递性 with A' B'; trivial).
    assert(Cong B C B C1) by (apply 等长的传递性 with B' C'; trivial).
    apply 等长的传递性 with A1 C1; Cong.
    clear dependent A'; clear dependent B'; clear dependent C'; clear X.

    assert(exists Y, 中点 Y C C1)
      by (apply midpoint_existence).
    ex_and H0 Y.
    assert(对称 C1 C B Y) by (apply cong_midpoint__image; assumption).
    assert(exists A2, 对称 A1 A2 B Y).
      apply l10_6_existence.
    ex_elim H2 A2.
    assert (Cong C A2 C1 A1).
      eapply l10_10.
        apply H0.
      assumption.
    apply 等长的传递性 with A2 C; Cong.
    assert (对称 B B B Y) by apply image_triv.
    assert (Per A2 B C).
      eapply (image_preserves_per A1 B C1 A2 B C).
        apply H5.
        assumption.
        assumption.
      assumption.
    assert (Cong A B A2 B).
      apply 等长的传递性 with A1 B; trivial.
      apply 等长的对称性, l10_10 with B Y; assumption.
    clear dependent A1; clear dependent C1; clear dependent Y.

    assert (exists Z, 中点 Z A A2).
      apply midpoint_existence.
    ex_and H0 Z.
    assert (对称 A2 A B Z) by (apply cong_midpoint__image; Cong).
    destruct (构造对称点 C B) as [C0].
    assert (Cong A C A C0) by (apply per_double_cong with B; assumption).
    assert (Cong A2 C A2 C0) by (apply per_double_cong with B; assumption).
    assert (对称 C0 C B Z).
      apply is_image_rev, cong_midpoint__image; trivial.
      induction (两点重合的决定性 A A2).
        treat_equalities; assumption.
      apply (l4_17 A A2); Col.
    assert (Cong A C A2 C0).
      apply l10_10 with B Z; assumption.
    apply 等长的传递性 with A2 C0; Cong.
Qed.

Lemma l10_16 : forall A B C A' B' P,
 ~ Col A B C -> ~ Col A' B' P -> Cong A B A' B' ->
 exists C', 三角形全等 A B C A' B' C' /\ OS  A' B' P C' .
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst B.
      apply 等长的对称性 in H1.
      apply False_ind.
      apply H.
      apply AAB型共线.
    assert(exists X, Col A B X /\ Perp A B C X).
      apply l8_18_existence.
      assumption.
    ex_and H3 X.
    assert (exists X', 三角形全等 A B X A' B' X').
      eapply l4_14_退化三角形有其全等形.
        assumption.
      assumption.
    ex_elim H5 X'.
    assert (exists Q, Perp A' B' Q X' /\ OS A' B' P Q).
      apply l10_15.
        eapply 全等于退化的三角形.
          apply H3.
        assumption.
      assumption.
    ex_and H5 Q.
    assert (exists C', Out X' C' Q /\ Cong  X' C' X C).
      eapply l6_11_existence.
        apply perp_distinct in H5.
        spliter.
        assumption.
      intro.
      subst C.
      apply perp_distinct in H4.
      spliter.
      absurde.
    ex_and H8 C'.
    exists C'.
    unfold 三角形全等 in *.
    spliter.
    assert (Cong A C A' C').
      induction(两点重合的决定性 A X).
        subst X.
        apply 等长的对称性 in H10.
        apply 等长的同一性 in H10.
        subst X'.
        apply 等长的对称性.
        assumption.
      apply l10_12 with X X'.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_right_comm.
            apply H4.
          assumption.
          apply ABA型共线.
        apply AAB型共线.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply 等长的同一性 in H10.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply 等长的对称性 in H9.
              apply 等长的同一性 in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H5.
            apply 等价共线ACB.
            eapply out_col.
            assumption.
          eapply 全等于退化的三角形.
            apply H3.
          unfold 三角形全等.
          repeat split;assumption.
          apply ABA型共线.
        apply AAB型共线.
        assumption.
      apply 等长的对称性.
      assumption.
    assert (Cong B C B' C').
      induction(两点重合的决定性 B X).
        subst X.
        apply 等长的对称性 in H11.
        apply 等长的同一性 in H11.
        subst X'.
        apply 等长的对称性.
        assumption.
      apply l10_12 with X X'.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_comm.
            apply H4.
          apply 等价共线BAC.
          assumption.
          apply ABA型共线.
        apply AAB型共线.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply 等长的同一性 in H11.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply 等长的对称性 in H9.
              apply 等长的同一性 in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_comm.
              apply H5.
            apply 等价共线ACB.
            eapply out_col.
            assumption.
          apply 等价共线BAC.
          eapply 全等于退化的三角形.
            apply H3.
          unfold 三角形全等.
          repeat split; assumption.
          apply ABA型共线.
        apply AAB型共线.
        assumption.
      apply 等长的对称性.
      assumption.
    repeat split.
      assumption.
      assumption.
      assumption.
    assert (T19 := (l9_19 A' B' C' Q X')).
    assert (OS A' B' C' Q <-> Out X' C' Q /\ ~ Col A' B' C').
      apply T19.
        eapply 全等于退化的三角形.
          apply H3.
        unfold 三角形全等.
        repeat split; assumption.
      apply 等价共线BCA.
      apply out_col.
      assumption.
    apply 等长的对称性 in H1.
    destruct H14.
    spliter.
    assert (OS A' B' C' Q).
      apply H15.
      split.
        assumption.
      intro.
      apply H.
      eapply 全等于退化的三角形.
        apply H16.
      unfold 三角形全等.
      repeat split.
        assumption.
        apply 等长的对称性.
        assumption.
      apply 等长的对称性.
      assumption.
    eapply one_side_transitivity.
      apply H7.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma cong_cop_image__col : forall A B P P' X,
 P <> P' -> 对称 P P' A B -> Cong P X P' X -> 共面 A B P X ->
 Col A B X.
Proof.
    intros.
    unfold 对称 in *.
    induction H0.
      spliter.
      unfold 严格对称 in H3.
      spliter.
      ex_and H3 M.
      induction H4.
        induction(两点重合的决定性 A M).
          subst M.
          assert (Perp P A A B).
            eapply perp_col.
              apply perp_distinct in H4.
              spliter.
              intro.
              subst P.
              apply M是AB中点则M是BA中点 in H3.
              apply A是AB中点则A与B重合 in H3.
              subst P'.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H4.
            unfold Col.
            right; left.
            apply midpoint_bet.
            assumption.
          apply perp_comm in H6.
          apply perp_perp_in in H6.
          apply perp_in_comm in H6.
          apply perp_in_per in H6.
          assert (Per X A P).
            unfold Per.
            exists P'.
            split.
              apply M是AB中点则M是BA中点.
              assumption.
            Cong.
          apply l8_2 in H6.
          apply 等价共线CAB.
          apply (cop_per2__col P).
            Cop.
            intro.
            subst P.
            apply M是AB中点则M是BA中点 in H3.
            apply A是AB中点则A与B重合 in H3.
            subst P'.
            absurde.
            assumption.
          assumption.
        assert (Perp P M M A).
          eapply perp_col.
            intro.
            subst P.
            apply M是AB中点则M是BA中点 in H3.
            apply A是AB中点则A与B重合 in H3.
            subst P'.
            absurde.
            apply perp_sym.
            apply perp_comm.
            eapply perp_col.
              assumption.
              apply H4.
            assumption.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        apply perp_comm in H7.
        apply perp_perp_in in H7.
        apply perp_in_comm in H7.
        apply perp_in_per in H7.
        assert (Per X M P).
          unfold Per.
          exists P'.
          split.
            apply M是AB中点则M是BA中点.
            assumption.
          apply 等长的交换性.
          assumption.
        apply l8_2 in H7.
        assert (Col A X M).
          assert (P <> M).
            intro.
            subst P.
            apply M是AB中点则M是BA中点 in H3.
            apply A是AB中点则A与B重合 in H3.
            subst P'.
            absurde.
          apply (cop_per2__col P).
            apply coplanar_perm_2, col_cop__cop with B; Cop.
            assumption.
            assumption.
          assumption.
        eapply 共线的传递性2.
          apply H6.
          apply 等价共线ACB.
          assumption.
        apply 等价共线ACB.
        assumption.
      subst P'.
      absurde.
    spliter;subst;Col.
Qed.

Lemma cong_cop_per2_1 :
 forall A B X Y, A <> B -> Per A B X -> Per A B Y ->
 Cong B X B Y -> 共面 A B X Y -> X = Y \/ 中点 B X Y.
Proof.
    intros.
    eapply 共线点间距相同要么重合要么中点.
      apply 等价共线ACB.
      apply (cop_per2__col A).
        Cop.
        assumption.
        apply l8_2.
        assumption.
      apply l8_2.
      assumption.
    assumption.
Qed.

Lemma cong_cop_per2 : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y -> 共面 A B X Y ->
 X = Y \/ 严格对称 X Y A B.
Proof.
    intros.
    induction (cong_cop_per2_1 A B X Y H H0 H1 H2 H3).
      left; assumption.
    right.
    apply is_image_is_image_spec; auto.
    apply l10_4, cong_midpoint__image; trivial.
    apply per_double_cong with B; assumption.
Qed.

Lemma cong_cop_per2_gen : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y -> 共面 A B X Y ->
 X = Y \/ 对称 X Y A B.
Proof.
    intros.
    induction (cong_cop_per2 A B X Y H H0 H1 H2 H3).
      left; assumption.
    right.
    apply is_image_is_image_spec; assumption.
Qed.

Lemma ex_perp_cop : forall A B C P,
 A <> B -> exists Q, Perp A B Q C /\ 共面 A B P Q.
Proof.
  intros A B C P HAB.
  destruct (共线的决定性 A B C) as [HCol|HNCol]; [destruct (共线的决定性 A B P) as [|HNCol]|].
  - destruct (两点不重合则存在不共线的点 A B HAB) as [P' HNCol].
    destruct (l10_15 A B C P' HCol HNCol) as [Q []].
    exists Q.
    split; trivial.
    exists P; left; Col.
  - destruct (l10_15 A B C P HCol HNCol) as [Q []].
    exists Q.
    split; [|apply os__coplanar]; assumption.
  - destruct (l8_18_existence A B C HNCol) as [Q []].
    exists Q.
    split.
      Perp.
    exists Q; left; split; Col.
Qed.

Lemma hilbert_s_version_of_pasch_aux : forall A B C I P, 共面 A B C P ->
  ~ Col A I P -> ~ Col B C P -> Bet B I C -> B <> I -> I <> C -> B <> C ->
  exists X, Col I P X /\
            ((Bet A X B /\ A <> X /\ X <> B /\ A <> B) \/
             (Bet A X C /\ A <> X /\ X <> C /\ A <> C)).
Proof.
intros A B C I P HCop HNC HNC' HBet HBI HIC HBC.
assert (HTS : TS I P B C).
  {
  assert_cols; split; try (intro; apply HNC'; ColR).
  split; try (intro; apply HNC'; ColR).
  exists I; Col.
  }
assert (HCop1 : 共面 A P B I) by (assert_diffs; apply col_cop__cop with C; Cop; Col).
elim (two_sides_dec I P A B); intro HTS'.

  {
  destruct HTS' as [Hc1 [Hc2 [T [HCol HBet']]]].
  exists T; split; Col.
  left; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }

  {
  rename HTS' into HOS.
  assert (HTS' : TS I P A C).
    {
    apply l9_8_2 with B; Col.
    unfold TS in HTS; spliter.
    apply cop_nts__os; Cop.
    intro; apply HOS; apply l9_2; Col.
    }
  destruct HTS' as [Hc1 [Hc2 [T [HCol HBet']]]].
  exists T; split; Col.
  right; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }
Qed.

Lemma hilbert_s_version_of_pasch : forall A B C P Q, 共面 A B C P ->
  ~ Col C Q P -> ~ Col A B P -> BetS A Q B ->
  exists X, Col P Q X /\ (BetS A X C \/ BetS B X C).
Proof.
intros A B C P Q HCop HNC1 HNC2 HAQB.
rewrite 严格中间性的等价 in HAQB; spliter.
destruct (hilbert_s_version_of_pasch_aux C A B Q P) as [X [HPQX HBetS]]; Cop.
exists X; split; Col; unfold BetS.
induction HBetS; spliter; repeat split; Between.
Qed.

Lemma two_sides_cases : forall O P A B,
 ~ Col O A B -> OS O P A B -> TS O A P B \/ TS O B P A.
Proof.
intros.
assert(TS O A P B \/ OS O A P B).
{
  apply(cop__one_or_two_sides O A P B); Col.
    Cop.
  unfold OS in H0.
  ex_and H0 R.
  unfold TS in H0.
  spliter.
  Col.
}
induction H1.
left; auto.
right.
apply l9_31; Side.
Qed.

Lemma not_par_two_sides :
  forall A B C D I, C <> D -> Col A B I -> Col C D I -> ~ Col A B C ->
  exists X, exists Y, Col C D X /\ Col C D Y /\ TS A B X Y.
Proof.
intros A B C D I HCD HCol1 HCol2 HNC.
assert (HX : exists X, Col C D X /\ I <> X) by (exists C; split; try intro; treat_equalities; Col).
destruct HX as [X [HCol3 HIX]].
destruct (构造对称点 X I) as [Y HMid].
exists X; exists Y; assert_diffs; assert_cols; repeat split; try ColR.
  intro; apply HIX, l6_21_两线交点的唯一性 with A B C D; Col.
  intro; absurd (I = Y); [auto|apply l6_21_两线交点的唯一性 with A B C D; ColR].
exists I; unfold 中点 in HMid; spliter; split; Col; Between.
Qed.

Lemma cop_not_par_other_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  共面 A B C P ->
  exists Q, Col C D Q /\ TS A B P Q.
Proof.
intros A B C D I P HCD HCol1 HCol2 HNC1 HNC2 HCop.
destruct (not_par_two_sides A B C D I HCD HCol1 HCol2 HNC1) as [X [Y [HCol3 [HCol4 HTS]]]].
assert (共面 A B P X).
  apply coplanar_trans_1 with C; [Col|Cop|].
  exists I; right; right; split; ColR.
elim (two_sides_dec A B P X); intro HOS; [exists X; Col|].
assert_diffs; apply cop_nts__os in HOS; Col; [|intro; unfold TS in HTS; intuition].
exists Y; split; Col.
apply l9_8_2 with X; [|apply one_side_symmetry]; Col.
Qed.

Lemma cop_not_par_same_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  共面 A B C P ->
  exists Q, Col C D Q /\ OS A B P Q.
Proof.
intros A B C D I P HCD HCol1 HCol2 HNC1 HNC2 HCop.
destruct (not_par_two_sides A B C D I HCD HCol1 HCol2 HNC1) as [X [Y [HCol3 [HCol4 HTS]]]].
assert (共面 A B P X).
  apply coplanar_trans_1 with C; [Col|Cop|].
  exists I; right; right; split; ColR.
elim (one_side_dec A B P X); intro HTS2; [exists X; Col|].
assert_diffs; apply cop_nos__ts in HTS2; Col; [|intro; unfold TS in HTS; intuition].
exists Y; split; Col.
exists X; split; Side.
Qed.

End T10_1.

Section T10_2D.

Context `{T2D:Tarski_2D}.

Lemma all_coplanar : forall A B C D, 共面 A B C D.
Proof.
apply 防升维公理_implies_all_coplanar;
unfold 防升维公理_axiom; apply 防升维公理.
Qed.

Lemma per2__col : forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X.
Proof.
apply 防升维公理_implies_per2__col;
unfold 防升维公理_axiom; apply 防升维公理.
Qed.

Lemma perp2__col : forall X Y Z A B,
 Perp X Y A B -> Perp X Z A B -> Col X Y Z.
Proof.
    intros X Y Z A B.
    apply cop_perp2__col, all_coplanar.
Qed.

End T10_2D.

Hint Resolve all_coplanar : cop.
(* the hint: eapply @all_coplanar will only be used by eauto *)

Ltac Cop := auto; try (intros; solve [apply all_coplanar|apply col__coplanar; Col
     |apply coplanar_perm_1, col__coplanar; Col|apply coplanar_perm_4, col__coplanar; Col
     |apply coplanar_perm_18, col__coplanar; Col
     |assert_cops; auto 2 with cop_perm]).