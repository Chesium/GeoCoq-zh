Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.
Import Ch10_line_reflexivity.

Section T11_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l11_3 : forall A B C D E F,
 等角 A B C D E F ->
 exists A', exists C', exists D', exists F',
 Out B A' A /\ Out B C C' /\ Out E D' D /\ Out E F F' /\
 三角形全等 A' B C' D' E F'.
Proof.
    intros.
    unfold 等角 in H.
    分离合取式.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    统计不重合点.
    repeat split; auto; apply 等长的左交换性.
      apply 两组连续三点分段等则全体等 with A D; Cong; Between.
      apply 两组连续三点分段等则全体等 with C F; Cong; Between.
Qed.

Lemma l11_aux : forall B A A' A0 E D D' D0,
      Out B A A' -> Out E D D' -> Cong B A' E D' ->
      Bet B A A0 -> Bet E D D0 -> Cong A A0 E D ->
      Cong D D0 B A ->
      Cong B A0 E D0 /\ Cong A' A0 D' D0.
Proof.
    intros.
    assert (A <> B).
      unfold Out in H.
      分离合取式.
      assumption.
    assert(Cong B A0 E D0).
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with A D; Cong; Between.
    split.
      apply H7.
    unfold Out in *.
    分离合取式.
    induction H9; induction H11.
      assert(Bet B A' A0 \/ Bet B A0 A').
        eauto using l5_1.

      induction H12.
        assert(Bet E D' D0).
          apply (cong_preserves_bet B A' A0); trivial.
          unfold Out.
          repeat split.
            assumption.
            统计不重合点.
            auto.
          apply l5_1 with D; auto.
        apply 等长的交换性.
        apply l4_3  with B E; Cong; Between.
      assert(Bet E D0 D').
        apply (cong_preserves_bet B A0 A'); trivial.
        unfold Out.
        repeat split.
          统计不重合点;auto.
          统计不重合点;auto.
        apply l5_1 with D; auto.
      apply l4_3 with B E; Between; Cong.
      apply 等长的交换性.
      apply l4_3 with B E; Cong.
        apply 中间性的对称性.
        eapply 中间性的交换传递性2.
          apply H11.
        assumption.
        apply 中间性的对称性.
        apply (cong_preserves_bet B A' A0); Cong.
          eapply 中间性的交换传递性2.
            apply H11.
          assumption.
        unfold Out.
        repeat split.
          assumption.
          统计不重合点;auto.
        apply l5_1 with D; auto.
      apply 等长的交换性.
      apply l4_3 with B E; Cong.
        apply 中间性的对称性.
        apply (cong_preserves_bet E D' D0); Cong.
          eapply 中间性的交换传递性2.
            apply H9.
          assumption.
        unfold Out.
        repeat split.
          assumption.
          统计不重合点;auto.
        eauto using l5_1.
        apply 中间性的对称性.
        eapply 中间性的交换传递性2.
          apply H9.
        assumption.
    apply 等长的交换性.
    apply l4_3 with B E; Cong.
      apply 中间性的对称性.
      eapply 中间性的交换传递性2.
        apply H11.
      assumption.
      apply 中间性的对称性.
      eapply 中间性的交换传递性2.
        apply H9.
      assumption.
Qed.

Lemma l11_3_bis : forall A B C D E F,
 (exists A', exists C', exists D', exists F',
 Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
 三角形全等 A' B C' D' E F') -> 等角 A B C D E F.
Proof.
    intros.
    unfold 等角.
    ex_and H A'.
    ex_and H0 C'.
    ex_and H D'.
    ex_and H0 F'.
    prolong B A A0 E D.
    prolong B C C0 E F.
    prolong E D D0 B A.
    prolong E F F0 B C.
    assert(HH0:=H0).
    assert(HH1:=H1).
    assert(HH2:=H2).
    assert(HH:=H).
    unfold Out in HH.
    unfold Out in HH0.
    unfold Out in HH1.
    unfold Out in HH2.
    分离合取式.
    repeat split;try assumption.
    repeat split;try assumption.
    exists A0.
    exists C0.
    exists D0.
    exists F0.
    repeat split; try (assumption).
    unfold 三角形全等 in H3.
    分离合取式.
    assert(Cong B A0 E D0 /\ Cong A' A0 D' D0).
      apply l11_aux with A D; Out; Cong.
    assert(Cong B C0 E F0 /\ Cong C' C0 F' F0).
      apply l11_aux with C F; Out.
    分离合取式.
    assert (三角形全等 B A' A0 E D' D0)
      by (repeat split;Cong).
    assert (三角形全等 B C' C0 E F' F0)
      by (repeat split;Cong).
    assert (Cong C0 A' F0 D').
      apply l4_16_五线段形式推论 with B C' E F';
        unfold 五线段形式; repeat split; Cong; ColR.
    apply l4_16_五线段形式推论 with B A' E D';
    unfold 五线段形式; repeat split; Cong; ColR.
Qed.

Lemma l11_4_1 : forall A B C D E F,
  等角 A B C D E F -> A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F').
Proof.
    intros.
    assert (HH:=H).
    apply l11_3 in HH.
    unfold 等角 in H.
    分离合取式.
    repeat split; try assumption.
    clear H3.
    intros.
    ex_and HH A0.
    ex_and H4 C0.
    ex_and H10 D0.
    ex_and H4 F0.
    unfold 三角形全等 in H13.
    分离合取式.
    assert (Out B A' A0).
      eapply l6_7.
        apply H3.
      apply l6_6.
      assumption.
    assert (Out E D' D0).
      eapply l6_7.
        apply H6.
      apply l6_6.
      assumption.
    assert(Cong A' A0 D' D0).
      eapply out_cong_cong.
        apply H16.
        apply H17.
        assumption.
      Cong.
    assert (Cong A' C0 D' F0).
      eapply (l4_16_五线段形式推论 B A0 A' C0 E D0 D' F0).
        unfold 五线段形式.
        repeat split.
          Col.
          Cong.
          assumption.
          Cong.
          assumption.
        assumption.
      intro.
      subst A0.
      unfold Out in H4.
      分离合取式.
      absurde.
    assert (Out B C' C0).
      eapply l6_7.
        apply H5.
      assumption.
    assert (Out E F' F0).
      eapply l6_7.
        apply H7.
      assumption.
    assert(Cong C' C0 F' F0).
      apply out_cong_cong with B E; auto.
    apply 等长的交换性.
    apply (l4_16_五线段形式推论 B C0 C' A' E F0 F' D').
      repeat split; Col; Cong.
    统计不重合点.
    auto.
Qed.



Lemma l11_4_2 : forall A B C D E F,
  (A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F')) ->  等角 A B C D E F.
Proof.
    intros.
    分离合取式.
    apply l11_3_bis.
    prolong B A A' E D.
    prolong B C C' E F.
    prolong E D D' B A.
    prolong E F F' B C.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    assert(Cong A' B D' E).
     {
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with A D; Cong; Between.
     }
    assert (Cong B C' E F').
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with C F; Cong; Between.
    统计不重合点; repeat split; auto.
    apply H3; repeat split; Cong.
Qed.

Lemma 同角相等 : forall A B C, A <> B -> C <> B -> 等角 A B C A B C.
Proof.
    intros.
    apply l11_3_bis.
    exists A.
    exists C.
    exists A.
    exists C.
    repeat split; Between; Cong.
Qed.

Lemma 等角的对称性 : forall A B C A' B' C', 等角 A B C A' B' C' -> 等角 A' B' C' A B C.
Proof.
    unfold 等角.
    intros.
    分离合取式.
    ex_and H3 A0.
    ex_and H4 C0.
    ex_and H3 D0.
    ex_and H4 F0.
    repeat split; try assumption.
    exists D0.
    exists F0.
    exists A0.
    exists C0.
    repeat split; Cong.
Qed.

Lemma l11_10 : forall A B C D E F A' C' D' F',
  等角 A B C D E F -> Out B A' A -> Out B C' C -> Out E D' D -> Out E F' F ->
  等角 A' B C' D' E F'.
Proof.
    intros.
    apply l11_4_1 in H.
    分离合取式.
    apply l11_4_2.
    统计不重合点.
    repeat split; auto.
    intros.
    分离合取式.
    apply H7.
    统计不重合点.
    repeat split;Cong.
      apply l6_7 with A'; Out.
      apply l6_7 with C'; Out.
      apply l6_7 with D'; Out.
      apply l6_7 with F'; Out.
Qed.

Lemma out2__conga : forall A B C A' C', Out B A' A -> Out B C' C -> 等角 A B C A' B C'.
Proof.
  intros A B C A' C' HAOut HCOut.
  统计不重合点.
  apply l11_10 with A C A C; Out.
  apply 同角相等;auto.
Qed.

Lemma 三角形全等推点不重合_AB : forall A B C A' B' C',
 A<>B -> 三角形全等 A B C A' B' C' -> A' <> B'.
Proof.
unfold 三角形全等 in *.
intros.
分离合取式.
统计不重合点.
auto.
Qed.

Lemma 三角形全等推点不重合_BC: forall A B C A' B' C',
 B<>C -> 三角形全等 A B C A' B' C' -> B' <> C'.
Proof.
unfold 三角形全等 in *.
intros.
分离合取式.
统计不重合点.
auto.
Qed.

Lemma 三角形全等推角等1 : forall A B C A' B' C',
 A <> B -> C <> B ->
 三角形全等 A B C A' B' C' ->
 等角 A B C A' B' C'.
Proof.
    intros.
    assert (A' <> B') by (eauto using 三角形全等推点不重合_AB).
    assert (B' <> C') by (eauto using 三角形全等推点不重合_BC).
    apply (l11_3_bis A B C A' B' C').
    exists A, C, A', C'.
    intuition Out.
Qed.

Lemma 三角形全等推角等2 : forall A B C A' B' C' A'' B'' C'',
  三角形全等 A B C A' B' C' ->
  等角 A B C A'' B'' C'' ->
  等角 A' B' C' A'' B'' C''.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A2.
    ex_and H5 C2.
    unfold 三角形全等 in H.
    分离合取式.
    unfold 等角.
    统计不重合点.
    repeat split; auto.
    prolong B' A' A1 B'' A''.
    prolong B' C' C1 B'' C''.
    exists A1, C1, A2, C2.
    repeat split;try assumption.
      apply 等长的传递性 with B A; Cong.
      apply 等长的传递性 with B C; auto.
    assert (Cong A A0 A' A1).
      apply 等长的传递性 with B'' A''; Cong.
    assert(Cong B A0 B' A1).
      apply 两组连续三点分段等则全体等 with A A'; Cong.
    assert (Cong C C0 C' C1).
      apply 等长的传递性 with B'' C''; Cong.
    assert(Cong B C0 B' C1).
      eapply 两组连续三点分段等则全体等 with C C'; auto.
    assert(五线段形式 B A A0 C B' A' A1 C').
      unfold 五线段形式; assert_cols; repeat split; Cong.
    assert(Cong A0 C A1 C').
      eauto using l4_16_五线段形式推论.
    apply 等长的交换性.
    assert(Cong C0 A0 C1 A1).
      apply (l4_16_五线段形式推论 B C C0 A0 B' C' C1 A1).
        unfold 五线段形式;assert_cols;repeat split; Cong.
      auto.
    apply 等长的传递性 with A0 C0; Cong.
Qed.

Lemma 角等推AB不重合 : forall A B C A' B' C', 等角 A B C A' B' C' -> A <> B.
Proof.
    intros.
    unfold 等角 in H.
    分离合取式.
    assumption.
Qed.

Lemma 角等推CB不重合 : forall A B C A' B' C', 等角 A B C A' B' C' -> C <> B.
Proof.
    intros.
    unfold 等角 in H.
    分离合取式.
    assumption.
Qed.

Lemma 角等推DE不重合 : forall A B C A' B' C', 等角 A B C A' B' C' -> A' <> B'.
Proof.
  intros A B C A' B' C' H.
  apply (角等推AB不重合 A' B' C' A B C); apply 等角的对称性; auto.
Qed.

Lemma 角等推FE不重合 : forall A B C A' B' C', 等角 A B C A' B' C' -> C' <> B'.
Proof.
  intros A B C A' B' C' H.
  apply (角等推CB不重合 A' B' C' A B C); apply 等角的对称性; auto.
Qed.

Lemma 角等的传递性 : forall A B C A' B' C' A'' B'' C'',
  等角 A B C A' B' C' -> 等角 A' B' C' A'' B'' C'' ->
  等角 A B C A'' B'' C''.
Proof.
    intros.
    assert (HH:=H).
    unfold 等角 in H.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    统计不重合点.
    assert(A'' <> B'' /\ C'' <> B'').
      unfold 等角 in H0.
      分离合取式.
      split; assumption.
    分离合取式.
    assert(等角 A1 B' C1 A'' B'' C'')
      by (apply l11_10 with A' C' A'' C'';Out).
    assert (等角 A0 B C0 A' B' C')
      by (apply l11_10 with A C A' C';Out).
    assert (Cong B A0 B' A1).
      {
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with A A'; Between; Cong.
      }
    assert (Cong B C0 B' C1).
      {
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with C C'; Between; Cong.
      }
    assert (Cong A0 C0 A1 C1).
    {
      apply (l11_4_1) in H24.
      分离合取式.
      apply H30.
      repeat split;Between.
    }
    assert (三角形全等 A0 B C0 A1 B' C1)
      by (repeat split; Cong).
    apply 三角形全等的对称性 in H28.
    assert (等角 A0 B C0 A'' B'' C'')
      by (eauto using 三角形全等推角等2).
    apply l11_10 with A0 C0 A'' C''; Out.
Qed.

Lemma 角ABC等于角CBA : forall A B C,
 A <> B -> C <> B -> 等角 A B C C B A.
Proof.
    intros.
    unfold 等角.
    repeat split; try assumption.
    prolong B A A' B C.
    prolong B C C' B A.
    prolong B A A'' B C.
    prolong B C C'' B A.
    exists A', C', C'', A''.
    repeat split; try assumption.
    assert (A' = A'') by (pose (点的唯一构造 B A); eauto).
    subst A''.
    assert (C' = C'') by (pose (点的唯一构造 B C); eauto).
    subst C''.
    Cong.
Qed.

Lemma 角ABA等于角CDC : forall A B C D,
  A<>B -> C<>D -> 等角 A B A C D C.
Proof.
    intros.
    unfold 等角.
    repeat split; try assumption.
    prolong B A A' D C.
    prolong D C C' B A.
    exists A', A', C', C'.
    repeat split;Cong.
Qed.

Lemma l11_13 : forall A B C D E F A' D',
 等角 A B C D E F -> Bet A B A' -> A'<> B -> Bet D E D' -> D'<> E -> 等角 A' B C D' E F.
Proof.
    intros.
    unfold 等角 in H.
    分离合取式.
    ex_and H7 A''.
    ex_and H8 C''.
    ex_and H7 D''.
    ex_and H8 F''.
    prolong B A' A0 E D'.
    prolong E D' D0 B A'.
    unfold 等角.
    repeat split; try assumption.
    exists A0.
    exists C''.
    exists D0.
    exists F''.
    repeat split; try assumption.
    apply (五线段公理_等价SAS_with_def A'' B A0 C'' D'' E D0 F'').
      unfold 外五线段形式.
      repeat split.
        eapply 中间性的外传递性1.
          apply 中间性的对称性.
          apply H7.
          eapply 中间性的外传递性2.
            apply H0.
            assumption.
          auto.
        assumption.
        eapply 中间性的外传递性1.
          apply 中间性的对称性.
          apply H11.
          eapply 中间性的外传递性2.
            apply H2.
            assumption.
          auto.
        assumption.
        apply 等长的左交换性.
        eapply 两组连续三点分段等则全体等.
          apply H7.
          apply 中间性的对称性.
          apply H11.
          Cong.
        Cong.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply H16.
          apply 中间性的对称性.
          apply H18.
          apply 等长的对称性.
          Cong.
        Cong.
        assumption.
      apply 等长的右交换性.
      apply 两组连续三点分段等则全体等 with C F; Cong; Between.
    统计不重合点;auto.
Qed.

Lemma 等角的右交换性 : forall A B C D E F, 等角 A B C D E F -> 等角 A B C F E D.
Proof.
    intros.
    apply 角等的传递性 with D E F.
    apply H.
    unfold 等角 in H.
    分离合取式.
    apply 角ABC等于角CBA;auto.
Qed.

Lemma 等角的左交换性 : forall A B C D E F, 等角 A B C D E F -> 等角 C B A D E F.
Proof.
    intros.
    apply 等角的对称性, 等角的右交换性, 等角的对称性.
    assumption.
Qed.

Lemma 等角的交换性 : forall A B C D E F, 等角 A B C D E F -> 等角 C B A F E D.
Proof.
    intros.
    apply 等角的左交换性.
    apply 等角的右交换性.
    assumption.
Qed.

Lemma 成中间性三点组的角相等 : forall A B C A' B' C',
 A <> B -> B <> C -> A' <> B' -> B' <> C' -> Bet A B C -> Bet A' B' C' ->
 等角 A B C A' B' C'.
Proof.
    intros.
    统计不重合点.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold 等角.
    repeat split; try assumption.
      auto.
      auto.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    apply (两组连续三点分段等则全体等 A0 B C0 A1 B' C1).
      eapply 中间性的外传递性1.
        apply 中间性的对称性.
        apply H11.
        eapply 中间性的外传递性2.
          apply H3.
          assumption.
        assumption.
      assumption.
      eapply 中间性的外传递性1.
        apply 中间性的对称性.
        apply H13.
        eapply 中间性的外传递性2.
          apply H4.
          assumption.
        assumption.
      assumption.
      apply 等长的右交换性.
      eapply 两组连续三点分段等则全体等.
        apply 中间性的对称性.
        apply H11.
        apply H13.
        apply 等长的左交换性.
        assumption.
      apply 等长的对称性.
      apply 等长的右交换性.
      assumption.
    apply 等长的右交换性.
    eapply 两组连续三点分段等则全体等.
      apply H7.
      apply 中间性的对称性.
      apply H9.
      apply 等长的对称性.
      apply 等长的左交换性.
      assumption.
    apply 等长的右交换性.
    assumption.
Qed.


Lemma l11_14 : forall A B C A' C',
 Bet A B A' -> A <> B -> A' <> B -> Bet C B C' -> B <> C -> B <> C' ->
 等角 A B C A' B C'.
Proof.
    intros.
    统计不重合点.
    assert (等角 A' B C  C' B A).
    {
      apply l11_13 with A C; Between.
      apply 角ABC等于角CBA; auto.
    }
      apply l11_13 with A' A; Between.
      apply 等角的右交换性; assumption.
Qed.

End T11_1.

Section T11_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l11_16_直角相等 : forall A B C A' B' C',
 Per A B C    -> A <> B  -> C <> B ->
 Per A' B' C' -> A'<> B' -> C'<> B'->
 等角 A B C A' B' C'.
Proof.
    intros.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold 等角.
    repeat split; try assumption.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    apply (l10_12 A0 B C0 A1 B' C1).
      apply (直角边共线点也构成直角2 _ _ C).
        intro;subst.
        auto.
        apply 直角的对称性.
        apply (直角边共线点也构成直角2 _ _ A).
          auto.
          apply 直角的对称性.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      apply (直角边共线点也构成直角2 _ _ C').
        auto.
        apply 直角的对称性.
        apply (直角边共线点也构成直角2 _ _ A').
          auto.
          apply 直角的对称性.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      apply 等长的右交换性.
      eapply 两组连续三点分段等则全体等.
        apply 中间性的对称性.
        apply H9.
        apply H11.
        apply 等长的左交换性.
        assumption.
      apply 等长的对称性.
      apply 等长的右交换性.
      assumption.
    apply 等长的右交换性.
    eapply 两组连续三点分段等则全体等.
      apply H5.
      apply 中间性的对称性.
      apply H7.
      apply 等长的对称性.
      apply 等长的左交换性.
      assumption.
    apply 等长的右交换性.
    assumption.
Qed.


Lemma l11_17_等于直角的角是直角 : forall A B C A' B' C',
  Per A B C -> 等角 A B C A' B' C' -> Per A' B' C'.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (Per A0 B C0).
      apply (直角边共线点也构成直角2 _ _ C).
        auto.
        apply 直角的对称性.
        apply (直角边共线点也构成直角2 _ _ A).
          auto.
          apply 直角的对称性.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
    assert(Per A1 B' C1).
      eapply l8_10_直角与全等推出直角.
        apply H13.
      repeat split.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply 中间性的对称性.
          apply H4.
          apply H8.
          apply 等长的左交换性.
          assumption.
        apply 等长的对称性.
        apply 等长的右交换性.
        assumption.
        assumption.
      apply 等长的右交换性.
      eapply 两组连续三点分段等则全体等.
        apply H6.
        apply 中间性的对称性.
        apply H10.
        apply 等长的左交换性.
        apply 等长的对称性.
        apply 等长的交换性.
        assumption.
      apply 等长的右交换性.
      assumption.
    apply (直角边共线点也构成直角2 _ _ C1).
      intro.
      subst C1.
      apply 中间性的同一律 in H10.
      subst C'.
      absurde.
      apply 直角的对称性.
      apply (直角边共线点也构成直角2 _ _ A1).
        intro.
        subst A1.
        apply 中间性的同一律 in H8.
        subst A'.
        absurde.
        apply 直角的对称性.
        assumption.
      unfold Col.
      right; left.
      apply 中间性的对称性.
      assumption.
    unfold Col.
    right; left.
    apply 中间性的对称性.
    assumption.
Qed.
(* 
     A
     |
     |
C————B————D
*)
Lemma l11_18_1 : forall A B C D,
  Bet C B D -> B <> C -> B <> D -> A <> B -> Per A B C -> 等角 A B C A B D.
Proof.
    intros.
    分离合取式.
    assert (Per A B D).
      eapply 直角边共线点也构成直角2.
        apply H0.
        assumption.
      unfold Col.
      right; right.
      apply 中间性的对称性.
      assumption.
    apply l11_16_直角相等; auto.
Qed.
(* 
     A
     |
     |
C————B————D
*)
Lemma l11_18_2 : forall A B C D,
  Bet C B D -> 等角 A B C A B D -> Per A B C.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 D0.
    assert (A0 = A1).
      apply (点的唯一构造 B A B A); auto.
    subst A1.
    assert(Per A0 B C0).
      unfold Per.
      exists D0.
      repeat split.
        eapply 中间性的外传递性1.
          apply 中间性的对称性.
          apply H6.
          eapply 中间性的外传递性2.
            apply H.
            assumption.
          auto.
        assumption.
        eapply 两组连续三点分段等则全体等.
          apply 中间性的对称性.
          apply H6.
          apply H10.
          apply 等长的左交换性.
          assumption.
        apply 等长的对称性.
        apply 等长的右交换性.
        assumption.
      assumption.
    apply (直角边共线点也构成直角2 _ _ C0).
      intro.
      subst C0.
      apply 中间性的同一律 in H6.
      subst C.
      absurde.
      apply 直角的对称性.
      apply (直角边共线点也构成直角2 _ _ A0).
        intro.
        subst A0.
        apply 中间性的同一律 in H8.
        subst A.
        absurde.
        apply 直角的对称性.
        assumption.
      unfold Col.
      right; left.
      apply 中间性的对称性.
      assumption.
    unfold Col.
    right; left.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma cong3_preserves_out : forall A B C A' B' C',
  Out A B C -> 三角形全等 A B C A' B' C' -> Out A' B' C'.
Proof.
    intros.
    unfold Out in *.
    分离合取式.
    assert(HH:=H0).
    unfold 三角形全等 in H0.
    分离合取式.
    repeat split.
      intro.
      subst A'.
      apply 等长的同一性 in H0.
      subst A.
      absurde.
      intro.
      subst A'.
      apply 等长的同一性 in H3.
      subst A.
      absurde.
    induction H2.
      left.
      apply (l4_6 A B C); assumption.
    right.
    apply (l4_6 A C B).
      apply H2.
    unfold 三角形全等.
    repeat split; Cong.
Qed.

Lemma l11_21_a : forall A B C A' B' C', Out B A C -> 等角 A B C A' B' C' -> Out B' A' C'.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (Out B A0 C0).
      unfold Out.
      repeat split.
        intro.
        subst A0.
        apply 中间性的同一律 in H4.
        subst A.
        absurde.
        intro.
        subst C0.
        apply 中间性的同一律 in H6.
        subst C.
        absurde.
      unfold Out in H.
      分离合取式.
      induction H14.
        apply l5_1 with A; auto.
        eapply 中间性的交换传递性2.
          apply H14.
        assumption.
      apply l5_1 with C; auto.
      eapply 中间性的交换传递性2.
        apply H14.
      assumption.
    assert (Out B' A1 C1).
      eapply cong3_preserves_out.
        apply H13.
      unfold 三角形全等.
      repeat split.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply H4.
          apply 中间性的对称性.
          apply H8.
          apply 等长的对称性.
          apply 等长的左交换性.
          assumption.
        apply 等长的右交换性.
        assumption; apply H8.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply H6.
          apply 中间性的对称性.
          apply H10.
          apply 等长的对称性.
          apply 等长的左交换性.
          assumption.
        apply 等长的右交换性.
        assumption.
      assumption.
    eapply l6_7.
      apply l6_6.
      eapply l6_7.
        apply H14.
      eapply l6_7.
        apply l6_6.
        apply H14.
      unfold Out.
      repeat split.
        intro.
        subst A1.
        unfold Out in H14.
        分离合取式.
        absurde.
        assumption.
      right.
      assumption.
    eapply l6_7.
      apply H14.
    unfold Out.
    repeat split.
      intro.
      subst C1.
      unfold Out in H14.
      分离合取式.
      absurde.
      assumption.
    right.
    assumption.
Qed.

Lemma l11_21_b : forall A B C A' B' C',
 Out B A C -> Out B' A' C' -> 等角 A B C A' B' C'.
Proof.
    intros.
    prolong A B A0 A B.
    prolong C B C0 B C.
    prolong A' B' A1 A' B'.
    prolong C' B' C1 B' C'.
    apply l11_13 with C0 C1.
      apply 成中间性三点组的角相等; Between.
        intro.
        treat_equalities.
        unfold Out in H.
        分离合取式.
        absurde.
        unfold Out in H.
        分离合取式.
        auto.
        intro.
        treat_equalities.
        unfold Out in H0.
        分离合取式.
        absurde.
        intro.
        unfold Out in H0.
        分离合取式.
        auto.
      unfold Out in H.
      分离合取式.
      induction H10.
        eapply 中间性的内传递性1.
          apply 中间性的对称性.
          apply H3.
        assumption.
      eapply 中间性的外传递性2.
        apply 中间性的对称性.
        apply H3.
        assumption.
      auto.
      unfold Out in H.
      分离合取式.
      auto.
      unfold Out in H0.
      分离合取式.
      induction H10.
        eapply 中间性的内传递性1.
          apply 中间性的对称性.
          apply H7.
        assumption.
      eapply 中间性的外传递性2.
        apply 中间性的对称性.
        apply H7.
        assumption.
      auto.
    unfold Out in H0.
    分离合取式.
    auto.
Qed.

Lemma conga_cop__or_out_ts : forall A B C C', 共面 A B C C' -> 等角 A B C A B C' ->
  Out B C C' \/ TS A B C C'.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (A0=A1).
      apply (点的唯一构造 B A B A); auto.
    subst A1.
    induction (两点重合的决定性 C0 C1).
      subst C1.
      left.
      unfold Out.
      repeat split; try assumption.
      eapply l5_3.
        apply H6.
      assumption.
    right.
    assert(exists M, 中点 M C0 C1).
      apply 中点的存在性.
    ex_and H14 M.
    assert(Cong B C0 B C1).
      apply 等长的右交换性.
      eapply 两组连续三点分段等则全体等.
        apply H6.
        apply 中间性的对称性.
        apply H10.
        apply 等长的对称性.
        apply 等长的左交换性.
        assumption.
      apply 等长的右交换性.
      assumption.
    assert(Per A0 M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per B M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per A0 M C1).
      unfold Per.
      exists C0.
      split.
        apply M是AB中点则M是BA中点.
        assumption.
      apply 等长的对称性.
      assumption.
    assert(Per B M C1).
      unfold Per.
      exists C0.
      split.
        apply M是AB中点则M是BA中点.
        assumption.
      apply 等长的对称性.
      assumption.
    assert (B <> A0).
      intro.
      subst A0.
      apply 中间性的同一律 in H8.
      subst A.
      absurde.
    assert (Cong A C0 A C1).
      eapply (l4_2 B A A0 C0 B A A0 C1).
      unfold 内五线段形式.
      repeat split; try assumption.
        apply 等长的自反性.
      apply 等长的自反性.
    assert (Per A M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert (Per A M C1).
      unfold Per.
      exists C0.
      split.
        apply M是AB中点则M是BA中点.
        assumption.
      apply 等长的对称性.
      assumption.
    assert(Col B A M).
      apply cop_per2__col with C0.
        apply 等价共面CABD, col_cop__cop with C1; Col.
        apply 等价共面CABD, col_cop__cop with C'; Col.
        apply 等价共面ADCB, col_cop__cop with C; Col; Cop.
        intro.
        subst M.
        apply A是AB中点则A与B重合 in H15.
        contradiction.
        assumption.
      assumption.
    (************)
    induction(两点重合的决定性 B M).
      subst M.
      assert(~Col A B C).
        apply 成直角三点不共线.
          assumption.
          auto.
        apply 直角边共线点也构成直角2 with C1.
          intro.
          subst C1.
          apply M是AB中点则M是BA中点 in H15.
          apply A是AB中点则A与B重合 in H15.
          subst C0.
          absurde.
          assumption.
        assert(Bet C B C1).
          eapply 中间性的交换传递性1.
            apply 中间性的对称性.
            apply H6.
          apply midpoint_bet.
          assumption.
        unfold Col.
        right; right.
        assumption.
      assert(~Col A B C').
        apply 成直角三点不共线.
          assumption.
          auto.
        apply 直角边共线点也构成直角2 with C1.
          intro.
          subst C1.
          apply M是AB中点则M是BA中点 in H15.
          apply A是AB中点则A与B重合 in H15.
          subst C0.
          absurde.
          assumption.
        assert(Bet C' B C0).
          eapply 中间性的交换传递性1.
            apply 中间性的对称性.
            apply H10.
          apply midpoint_bet.
          apply M是AB中点则M是BA中点.
          assumption.
        unfold Col.
        right; left.
        apply 中间性的对称性.
        assumption.
      unfold TS.
      repeat split.
        Col.
        Col.
      exists B.
      split.
        Col.
      apply 中间性的对称性.
      eapply 中间性的交换传递性1.
        apply 中间性的对称性.
        apply H10.
      apply 中间性的对称性.
      eapply 中间性的交换传递性1.
        apply 中间性的对称性.
        apply H6.
      apply midpoint_bet.
      assumption.
    (***********)
    assert(TS B M C0 C1).
      unfold TS.
      repeat split.
        intro.
        apply 成直角三点不共线 in H17.
          apply H17.
          apply 等价共线BCA.
          assumption.
          assumption.
        intro.
        subst C0.
        apply A是AB中点则A与B重合 in H15.
        subst C1.
        absurde.
        intro.
        apply 成直角三点不共线 in H19.
          apply H19.
          Col.
          assumption.
        intro.
        subst C1.
        apply M是AB中点则M是BA中点 in H15.
        apply A是AB中点则A与B重合 in H15.
        subst C0.
        absurde.
      exists M.
      split.
        apply ABA型共线.
      apply midpoint_bet.
      assumption.
    apply (col_two_sides _ _ A) in H26.
      apply invert_two_sides in H26.
      (*************************)
      assert(TS A B C C1).
        eapply l9_5.
          apply H26.
          apply ABA型共线.
        unfold Out.
        repeat split.
          intro.
          subst C0.
          apply 等长的对称性 in H14.
          apply 等长的同一性 in H14.
          subst C1.
          absurde.
          assumption.
        right.
        assumption.
      apply l9_2.
      eapply l9_5.
        apply l9_2.
        apply H27.
        apply ABA型共线.
      unfold Out.
      repeat split.
        intro.
        subst C1.
        apply 等长的同一性 in H14.
        subst C0.
        absurde.
        intro.
        subst C'.
        apply 等长的同一性 in H7.
        subst C0.
        absurde.
      right.
      assumption.
      Col.
    auto.
Qed.

Lemma conga_os__out : forall A B C C',
 等角 A B C A B C' -> OS A B C C' -> Out B C C'.
Proof.
    intros.
    destruct (conga_cop__or_out_ts A B C C'); trivial.
      Cop.
    exfalso; eapply l9_9; eassumption.
Qed.


Lemma 等角两边等长则端点间距相等 : forall A B C A' B' C',
 等角 A B C A' B' C' -> Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    unfold 等角 in H.
    分离合取式.
    ex_and H5 A0.
    ex_and H6 C0.
    ex_and H5 A1.
    ex_and H6 C1.
    assert(Cong A C0 A' C1).
      eapply (l4_2 B A A0 C0 B' A' A1 C1).
      repeat split; try assumption.
        eapply 两组连续三点分段等则全体等.
          apply H5.
          apply H9.
          apply 等长的交换性.
          assumption.
        eapply 等长的传递性.
          apply H6.
        apply 等长的交换性.
        apply 等长的对称性.
        apply 等长的传递性 with A B; Cong.
        eapply 等长的传递性.
          apply H6.
        apply 等长的交换性.
        apply 等长的对称性.
        apply 等长的传递性 with A B; Cong.
      eapply 等长的传递性.
        eapply 两组连续三点分段等则全体等.
          apply H7.
          apply H11.
          assumption.
        eapply 等长的传递性.
          apply H8.
        apply 等长的对称性.
        eapply 等长的传递性.
          apply H12.
        assumption.
      apply 等长的自反性.
    apply 等长的交换性.
    eapply (l4_2 B C C0 A B' C' C1 A').
    repeat split; try assumption.
      eapply 两组连续三点分段等则全体等.
        apply H7.
        apply H11.
        assumption.
      eapply 等长的传递性.
        apply H8.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H1.
      apply 等长的对称性.
      assumption.
      eapply 等长的传递性.
        apply H8.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H1.
      apply 等长的对称性.
      assumption.
      apply 等长的交换性.
      assumption.
    apply 等长的交换性.
    assumption.
Qed.


Lemma 给定角一边可作出与给定点同侧一点构成等角_非平角 : forall A B C A' B' P,
 ~ Col A B C -> ~ Col A' B' P ->
 exists C', 等角 A B C A' B' C' /\ OS A' B' C' P.
Proof.
    intros.
    assert (exists C0, Col B A C0 /\ Perp B A C C0).
      eapply l8_18_过一点垂线之垂点的存在性.
      intro.
      apply H.
      apply 等价共线BAC.
      assumption.
    ex_and H1 C0.
    induction(两点重合的决定性 B C0).
      subst C0.
      assert (exists  C', Per C' B' A' /\ Cong C' B' C B /\ OS A' B' C' P).
        apply ex_四点成首末边等长双直角S形则对边等长.
          intro.
          subst A'.
          apply H0.
          apply AAB型共线.
          intro.
          subst C.
          apply H.
          apply ABB型共线.
          apply ABB型共线.
        assumption.
      ex_and  H3 C'.
      exists C'.
      split.
        eapply l11_16_直角相等.
          apply L形垂直转垂直于 in H2.
          apply 垂直于的交换性 in H2.
          apply L形垂直于转直角 in H2.
          assumption.
          intro.
          subst A.
          apply H.
          apply AAB型共线.
          intro.
          subst C.
          apply H.
          apply ABB型共线.
          apply 直角的对称性.
          assumption.
          intro.
          subst A'.
          apply H0.
          apply AAB型共线.
        intro.
        subst C'.
        apply 等长的对称性 in H4.
        apply 等长的同一性 in H4.
        subst C.
        apply H.
        apply ABB型共线.
      assumption.
    (*********** B <> C0 ***********)
    induction (out_dec B A C0).
      assert (exists C0', Out B' A' C0' /\ Cong B' C0' B C0).
        eapply 由一点往一方向构造等长线段_3.
          intro.
          subst A'.
          apply H0.
          apply AAB型共线.
        assert (垂直于 C0 C0 C B C0).
          eapply L形垂直转垂直于.
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            assumption.
            apply 垂直的右交换性.
            apply H2.
          assumption.
        assumption.
      ex_and H5 C0'.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ OS B' C0' C' P).
        apply ex_四点成首末边等长双直角S形则对边等长.
          intro.
          subst C0'.
          unfold Out in H5.
          分离合取式.
          absurde.
          intro.
          subst C0.
          unfold Perp in H2.
          ex_and H2 X.
          unfold 垂直于 in H7.
          分离合取式.
          absurde.
          apply ABB型共线.
        intro.
        apply H0.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ C0').
          intro.
          subst C0'.
          unfold Out in H5.
          分离合取式.
          absurde.
          assumption.
        apply out_col.
        apply l6_6.
        assumption.
      ex_and H7 C'.
      assert (三角形全等 C0 B C C0' B' C').
        unfold 三角形全等.
        repeat split.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        eapply (l10_12 _ C0).
          assert(Perp  B C0 C C0 ).
            eapply 垂线共线点也构成垂直1.
              intro.
              subst C0.
              apply 垂直推出不重合 in H2.
              分离合取式.
              absurde.
              apply H2.
            assumption.
          apply 垂直的左交换性 in H10.
          apply L形垂直转垂直于 in H10.
          apply L形垂直于转直角.
          apply 垂直于的交换性.
          assumption.
          apply 直角的对称性.
          apply H7.
          apply 等长的对称性.
          assumption.
        apply 等长的对称性.
        apply 等长的交换性.
        assumption.
      exists C'.
      split.
        apply l11_10 with C0 C C0' C'.
          apply 三角形全等推角等1.
            intro.
            subst C0.
            absurde.
            intro.
            subst C.
            apply H.
            apply ABB型共线.
            assumption.
          assumption.
          apply out_trivial.
          intro.
          subst C.
          apply H.
          apply ABB型共线.
          assumption.
        apply out_trivial.
        intro.
        subst C'.
        apply ABA直角则A与B重合 in H7.
        subst C0'.
        unfold Out in H5.
        分离合取式.
        absurde.
      apply invert_one_side.
      apply col_one_side with C0'.
        apply out_col.
        apply l6_6.
        assumption.
        intro.
        subst A'.
        apply H0.
        apply AAB型共线.
        assumption.
    (*********************)
    apply not_out_bet in H4.
      prolong A' B' C0' B C0.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ OS B' C0' C' P).
        apply ex_四点成首末边等长双直角S形则对边等长.
          intro.
          subst C0'.
          apply 等长的对称性 in H6.
          apply 等长的同一性 in H6.
          subst C0.
          absurde.
          intro.
          subst C0.
          apply 垂直推出不重合 in H2.
          分离合取式.
          absurde.
          apply ABB型共线.
        intro.
        apply H0.
        apply 等价共线CAB.
        eapply 共线的传递性2 with C0'.
          intro.
          treat_equalities.
          absurde.
          assumption.
        unfold Col.
        right; right.
        assumption.
      ex_and H7 C'.
      exists C'.
      split.
        assert (三角形全等 C0 B C C0' B' C').
          repeat split.
            apply 等长的对称性.
            apply 等长的交换性.
            assumption.
            apply 等长的对称性.
            apply 等长的交换性.
            assumption.
          apply 等长的交换性.
          apply (l10_12 _ C0 _ _ C0').
            assert(Perp  B C0 C C0 ).
              eapply 垂线共线点也构成垂直1.
                intro.
                subst C0.
                apply 垂直推出不重合 in H2.
                分离合取式.
                absurde.
                apply H2.
              assumption.
            apply 垂直的左交换性 in H10.
            apply L形垂直转垂直于 in H10.
            apply L形垂直于转直角.
            apply 垂直于的对称性.
            assumption.
            assumption.
            apply 等长的对称性.
            assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply l11_13 with C0 C0'.
          apply 三角形全等推角等1; auto.
          intro.
          subst C.
          apply H.
          apply ABB型共线.
          apply 中间性的对称性.
          assumption.
          intro.
          subst A.
          apply H.
          apply AAB型共线.
          apply 中间性的对称性.
          assumption.
        intro.
        subst A'.
        apply H0.
        apply AAB型共线.
      apply invert_one_side.
      apply col_one_side with C0'.
        unfold Col.
        right; right.
        assumption.
        intro.
        subst A'.
        apply H0.
        apply AAB型共线.
        assumption.
    apply 等价共线BAC.
    assumption.
Qed.

Lemma 给定角一边可作出与给定点同侧一点构成等角_可平角 : forall A B C A' B' P,
 A <> B -> A <> C -> B <> C -> A' <> B' -> ~ Col A' B' P ->
 exists C', 等角 A B C A' B' C' /\ (OS A' B' C' P \/ Col A' B' C').
Proof.
    intros.
    分离合取式.
    induction (共线的决定性 A B C).
      induction (out_dec B A C).
        exists A'.
        split.
          assert(等角 A B A A B C).
            apply out2__conga.
            apply out_trivial.
            auto.
            apply l6_6.
            assumption.
          assert (等角 A B A A' B' A').
            apply 角ABA等于角CDC.
              auto.
            auto.
          apply 等角的对称性.
          eapply 角等的传递性.
            apply 等角的对称性.
            apply H7.
          assumption.
        right.
        apply ABA型共线.
      apply not_out_bet in H5.
        prolong A' B' C' A'  B'.
        exists C'.
        split.
          eapply 成中间性三点组的角相等; try assumption.
            intro.
            subst C'.
            apply 等长的对称性 in H7.
            apply 等长的同一性 in H7.
            subst A'.
            absurde.
        right.
        unfold Col.
        left.
        assumption.
      assumption.
    assert(exists C' , 等角 A B C A' B' C' /\ OS A' B' C' P).
      apply 给定角一边可作出与给定点同侧一点构成等角_非平角.
        assumption.
      assumption.
    ex_and H5 C'.
    exists C'.
    split.
      assumption.
    left.
    assumption.
Qed.

Lemma 给定角一边可作出与给定点异侧一点构成等角_非平角 : forall A B C A' B' P,
    ~ Col A B C -> ~ Col A' B' P ->
    exists C' : Tpoint, 等角 A B C A' B' C' /\ TS A' B' C' P.
Proof.
  intros A B C A' B' P HNCol HNCol'.
  assert (HP' : exists P', 中点 A' P P') by (apply 构造对称点).
  destruct HP' as [P' HMid].
  assert (~ Col A' B' P').
  { intro HCol.
    apply HNCol'.
    assert (Col A' P P') by (apply 中点蕴含共线; auto).
    apply (共线的传递性4 A' P'); Col.
    intro; treat_equalities; Col.
  }
  assert (HC' : exists C', 等角 A B C A' B' C' /\ OS A' B' C' P').
  apply (给定角一边可作出与给定点同侧一点构成等角_非平角 A B C A' B' P'); auto.
  destruct HC' as [C' [HConga HOne]].
  exists C'.
  split; auto.
  apply (l9_8_2 A' B' P'); Side.
  split; Col; split; Col.
  exists A'.
  split; Col.
  destruct HMid; Between.
Qed.


Lemma l11_15 : forall A B C D E P, ~ Col A B C -> ~ Col D E P ->
 exists F, 等角 A B C D E F /\ OS E D F P /\
          (forall F1 F2, ((等角 A B C D E F1 /\ OS E D F1 P) /\
                          (等角 A B C D E F2 /\ OS E D F2 P)) -> Out E F1 F2).
Proof.
    intros.
    assert(exists F, 等角 A B C D E F /\  OS D E F P)
      by (apply 给定角一边可作出与给定点同侧一点构成等角_非平角; assumption).
    ex_and H1 F.
    exists F.
    split.
      assumption.
    split.
      apply invert_one_side.
      assumption.
    intros.
    分离合取式.
    apply (conga_os__out D).
      apply 角等的传递性 with A B C.
        apply 等角的对称性.
        assumption.
      assumption.
    apply invert_one_side.
    apply one_side_transitivity with P; Side.
Qed.

Lemma l11_19 : forall A B P1 P2,
  Per A B P1 -> Per A B P2 -> OS A B P1 P2 ->
  Out B P1 P2.
Proof.
    intros.
    induction (共线的决定性 A B P1).
      induction (l8_9_直角三点共线则必有两点重合 A B P1 H H2).
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        intuition.
      subst.
      unfold OS in *.
      decompose [ex and] H1.
      unfold TS in *.
      分离合取式.
      assert (Col B A B) by Col.
      intuition.
    induction (共线的决定性 A B P2).
      induction (l8_9_直角三点共线则必有两点重合 A B P2 H0 ).
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        intuition.
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        分离合取式.
        assert (Col B A B) by Col.
        intuition.
      Col.
    assert (T:=l11_15 A B P1 A B P2 H2 H3).
    decompose [ex and] T.
    apply H7.
    split.
      split.
        apply 同角相等.
          intro;subst;Col.
        intro;subst;Col.
      apply invert_one_side;auto.
    split.
      apply l11_16_直角相等;try assumption.
        intro;subst;Col.
        intro;subst;Col.
        intro;subst;Col.
      intro;subst;Col.
    apply one_side_reflexivity.
    Col.
Qed.

Lemma l11_22_bet :
 forall A B C P A' B' C' P',
  Bet A B C ->
  TS P' B' A' C' ->
  等角 A B P A' B' P' /\ 等角 P B C  P' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    分离合取式.
    prolong A' B' C'' B C.
    assert(等角 C B P C'' B' P').
      eapply l11_13.
        apply H1.
        assumption.
        unfold 等角 in H2.
        分离合取式.
        assumption.
        assumption.
      intro.
      subst C''.
      apply 等长的对称性 in H4.
      apply 等长的同一性 in H4.
      subst C.
      unfold 等角 in H2.
      分离合取式.
      absurde.
    assert (等角 C'' B' P' C' B' P').
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H5.
      apply 等角的交换性.
      assumption.
    assert(Out B' C' C'' \/ TS P' B' C' C'').
      apply conga_cop__or_out_ts.
      apply 等价共面ACBD, col_cop__cop with A'; Col; Cop.
      apply ts_distincts in H0.
      分离合取式.
      auto.
      apply 等角的交换性.
      apply 等角的对称性.
      assumption.
    induction H7.
      unfold Out in H7.
      分离合取式.
      induction H9.
        eapply 中间性的内传递性1.
          apply H3.
        assumption.
      eapply 中间性的外传递性2.
        apply H3.
        assumption.
      auto.
    induction (共线的决定性 C' B' P').
      unfold TS in H7.
      分离合取式.
      apply False_ind.
      apply H7.
      apply 等价共线ACB.
      assumption.
    assert (B' <> P').
      intro.
      subst P'.
      apply H8.
      apply ABB型共线.
    assert (TS B' P' A' C'').
      unfold TS.
      repeat split.
        unfold TS in H0.
        分离合取式.
        intro.
        apply H0.
        apply 等价共线ACB.
        assumption.
        intro.
        unfold TS in H7.
        分离合取式.
        apply H11.
        apply 等价共线ACB.
        assumption.
      exists B'.
      split.
        apply AAB型共线.
      assumption.
    assert (OS B' P' C' C'').
      eapply l9_8_1.
        apply l9_2.
        apply invert_two_sides.
        apply H0.
      apply l9_2.
      assumption.
    apply l9_9_bis in H11.
    apply invert_two_sides in H7.
    contradiction.
Qed.

Lemma l11_22a :
 forall A B C P A' B' C' P',
 TS B P A C /\ TS B' P' A' C' /\
 等角 A B P A' B' P' /\ 等角 P B C  P' B' C' ->
 等角 A B C A' B' C'.
Proof.
    intros.
    分离合取式.
    assert (A <> B /\ A' <> B' /\ P <> B /\ P' <> B' /\ C <> B /\ C' <> B').
      unfold 等角 in *.
      分离合取式.
      repeat split; assumption.
    assert(A <> C /\ A' <> C').
      unfold TS in *.
      分离合取式.
      ex_and H12 T.
      ex_and H10 T'.
      split.
        intro.
        subst C.
        apply 中间性的同一律 in H13.
        subst T.
        contradiction.
      intro.
      subst C'.
      apply 中间性的同一律 in H14.
      subst T'.
      contradiction.
    分离合取式.
    assert(exists A'', Out B' A' A'' /\ Cong B' A'' B A).
      eapply 由一点往一方向构造等长线段_3; auto.
    ex_and H11 A''.
    unfold TS in H.
    assert (~ Col A B P).
      分离合取式.
      assumption.
    分离合取式.
    ex_and H15 T.
    induction (两点重合的决定性 B T).
      subst T.
      assert(Bet A' B' C').
        eapply l11_22_bet.
          apply H16.
          apply invert_two_sides.
          apply H0.
        split.
          apply H1.
        assumption.
      apply 成中间性三点组的角相等.
        assumption.
        auto.
        assumption.
        auto.
      assumption.
      assumption.
    induction(中间性的决定性 P B T).
      assert(exists T'', Col B' P' T'' /\ (Out B' P' T'' <-> Out B P T) /\ Cong B' T'' B T).
        prolong P' B' T'' B T.
        exists T''.
        split.
          unfold Col.
          right; right.
          apply 中间性的对称性.
          assumption.
        split.
          split.
            intro.
            assert(Bet P' B' T'' /\ Out B' P' T'').
              split; assumption.
            apply (not_bet_and_out _ _  _)in H22.
            contradiction.
          intro.
          assert(Bet P B T /\ Out B P T).
            split; assumption.
          apply (not_bet_and_out _ _  _)in H22.
          contradiction.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply 等长的对称性 in H21.
        apply 等长的同一性 in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(等角 A B T A' B' T'').
        apply 等角的交换性.
        eapply l11_13.
          apply 等角的交换性.
          apply H1.
          assumption.
          auto.
          eapply out_to_bet.
            apply 等价共线BAC.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        auto.
      assert(等角 A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        分离合取式.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply 等长的对称性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Cong A C A'' C'').
        eapply 两组连续三点分段等则全体等.
          apply H16.
          apply H24.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Cong C B C'' B').
        apply (五线段公理_等价SAS A A'' T T''); Cong.
        intro.
        subst T.
        apply H13.
        assumption.
      assert(等角 A B C A'' B' C'').
        apply 三角形全等推角等1.
          assumption.
          assumption.
        repeat split.
          apply 等长的交换性.
          apply 等长的对称性.
          assumption.
          assumption.
        apply 等长的交换性.
        assumption.
      assert(等角 C B T  C'' B' T'').
        apply 三角形全等推角等1.
          assumption.
          auto.
        repeat split.
          assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert (等角 P B C P' B' C'').
        eapply l11_13.
          apply 等角的交换性.
          apply H32.
          apply 中间性的对称性.
          assumption.
          assumption.
          apply 中间性的对称性.
          eapply out_to_bet.
            eapply 等价共线BAC.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        assumption.
      assert(等角 P' B' C' P' B' C'').
        eapply 角等的传递性.
          apply 等角的对称性.
          apply H2.
        assumption.
      assert(Out B' C' C'' \/ TS P' B' C' C'').
        apply conga_cop__or_out_ts.
        assert (HH := H0); destruct HH as [HNCol].
        apply coplanar_trans_1 with A'; Col.
          Cop.
        统计不重合点; apply 等价共面DACB, col_cop__cop with A''; Col.
        exists T''.
        right.
        left.
        split; Col.
        assumption.
      induction H35.
        eapply l11_10.
          apply H31.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        assumption.
      assert(TS B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply AAB型共线.
          assumption.
          apply AAB型共线.
        apply out_trivial.
        auto.
      apply invert_two_sides in H35.
      apply l9_2 in H35.
      assert(OS B' P'  A'' C'').
        unfold OS.
        exists C'.
        split; assumption.
      assert (TS B' P' A''  C'').
        unfold TS.
        repeat split.
          intro.
          unfold TS in H0.
          assert (~ Col A' B' P').
            分离合取式.
            assumption.
          分离合取式.
          apply H39.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ A'').
            intro.
            subst A''.
            unfold Out in H11.
            分离合取式.
            absurde.
            apply 等价共线BAC.
            assumption.
          apply out_col in H11.
          apply 等价共线ACB.
          assumption.
          intro.
          unfold TS in H35.
          分离合取式.
          apply H35.
          assumption.
        exists T''.
        split.
          apply 等价共线CAB.
          assumption.
        assumption.
      apply l9_9 in H38.
      contradiction.
    apply not_bet_out in H18.
      assert(exists T'', Col B' P' T'' /\ (Out B' P' T'' <-> Out B P T) /\ Cong B' T'' B T).
        assert (exists T'', Out B' P' T'' /\ Cong B' T'' B T).
          apply 由一点往一方向构造等长线段_3.
            auto.
          assumption.
        ex_and H19 T''.
        exists T''.
        split.
          apply out_col in H19.
          assumption.
        split.
          split.
            intro.
            assumption.
          intro.
          assumption.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply 等长的对称性 in H21.
        apply 等长的同一性 in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(等角 A B T A' B' T'').
        eapply l11_10.
          apply H1.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply l6_6.
        apply H22.
        assumption.
      assert(等角 A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        分离合取式.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          assumption.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply 等长的对称性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Cong A C A'' C'').
        eapply 两组连续三点分段等则全体等.
          apply H16.
          apply H24.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Cong C B C'' B').
        apply (五线段公理_等价SAS A A'' T T''); Cong.
        intro.
        apply H13.
        subst T.
        assumption.
      assert(等角 A B C A'' B' C'').
        apply 三角形全等推角等1.
          assumption.
          assumption.
        repeat split.
          apply 等长的交换性.
          apply 等长的对称性.
          assumption.
          assumption.
        apply 等长的交换性.
        assumption.
      assert(等角 C B T  C'' B' T'').
        apply 三角形全等推角等1.
          assumption.
          auto.
        repeat split.
          assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply 等长的对称性.
        assumption.
      eapply l11_10.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        assumption.
      assert(Out B' C' C'' \/ TS P' B' C' C'').
        apply conga_cop__or_out_ts.
        assert (HH := H0); destruct HH as [HNCol].
        apply coplanar_trans_1 with A'; Col.
          Cop.
        统计不重合点; apply 等价共面DACB, col_cop__cop with A''; Col.
        exists T''.
        right.
        left.
        split; Col.
        apply 等角的交换性.
        eapply 角等的传递性.
          apply 等角的交换性.
          apply 等角的对称性.
          apply H2.
        eapply l11_10.
          apply H32.
          apply out_trivial.
          auto.
          assumption.
          apply out_trivial.
          intro.
          subst C''.
          apply 等长的同一性 in H30.
          contradiction.
        apply H22.
        assumption.
      induction H33.
        assumption.
      assert(TS B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply AAB型共线.
          assumption.
          apply AAB型共线.
        apply out_trivial.
        auto.
      assert(OS B' P'  A'' C'').
        unfold OS.
        exists C'.
        split.
          assumption.
        apply invert_two_sides in H33.
        apply l9_2 in H33.
        assumption.
      assert (TS B' P' A''  C'').
        unfold TS.
        repeat split.
          intro.
          unfold TS in H34.
          分离合取式.
          apply H34.
          assumption.
          intro.
          unfold TS in H33.
          分离合取式.
          apply H37.
          apply 等价共线ACB.
          assumption.
        exists T''.
        split.
          apply 等价共线CAB.
          assumption.
        assumption.
      apply l9_9 in H36.
      contradiction.
      auto.
    apply 等价共线CBA.
    assumption.
Qed.

Lemma l11_22b :
 forall A B C P A' B' C' P',
 OS B P A C /\ OS B' P' A' C' /\
 等角 A B P A' B' P' /\ 等角 P B C  P' B' C' ->
 等角 A B C A' B' C'.
Proof.
    intros.
    分离合取式.
    prolong A B D A B.
    prolong A' B' D' A' B'.
    assert(等角 D B P D' B' P').
      eapply l11_13.
        apply H1.
        assumption.
        intro.
        subst D.
        apply 等长的对称性 in H4.
        apply 等长的同一性 in H4.
        subst A.
        unfold 等角 in H1.
        分离合取式.
        absurde.
        assumption.
      intro.
      subst D'.
      apply 等长的对称性 in H6.
      apply 等长的同一性 in H6.
      subst A'.
      unfold 等角 in H1.
      分离合取式.
      absurde.
    assert (等角 D B C D' B' C').
      eapply (l11_22a _ _ _ P _ _ _ P').
      split.
        eapply l9_2.
        eapply l9_8_2; [|apply H].
        unfold OS in H.
        ex_and H T.
        unfold TS in H.
        unfold TS in H8.
        分离合取式.
        repeat split.
          assumption.
          intro.
          apply H.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ D).
            intro.
            subst D.
            unfold 等角 in H7.
            分离合取式.
            absurde.
            apply 等价共线BAC.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B.
        split.
          apply AAB型共线.
        assumption.
      split.
        eapply l9_2.
        eapply l9_8_2; [|apply H0].
        unfold OS in H0.
        ex_and H0 T'.
        unfold TS in H0.
        unfold TS in H8.
        分离合取式.
        repeat split.
          assumption.
          intro.
          apply H0.
          apply 等价共线CAB.
          eapply (共线的传递性2 _ D').
            intro.
            subst D'.
            unfold 等角 in H7.
            分离合取式.
            absurde.
            apply 等价共线BAC.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B'.
        split.
          apply AAB型共线.
        assumption.
      split; assumption.
    eapply l11_13.
      apply H8.
      apply 中间性的对称性.
      assumption.
      intro.
      subst A.
      unfold 等角 in H1.
      分离合取式.
      absurde.
      apply 中间性的对称性.
      assumption.
    intro.
    subst A'.
    unfold 等角 in H1.
    分离合取式.
    absurde.
Qed.

Lemma l11_22 :
 forall A B C P A' B' C' P',
 ((TS B P A C /\ TS B' P' A' C')\/
  (OS B P A C /\ OS B' P' A' C')) /\
  等角 A B P A' B' P' /\ 等角 P B C  P' B' C' ->
 等角 A B C A' B' C'.
Proof.
    intros.
    分离合取式.
    induction H.
      apply (l11_22a _ _ _ P _ _ _ P');tauto.
    apply (l11_22b _ _ _ P _ _ _ P');tauto.
Qed.

Lemma l11_24_在角内的对称性 :
 forall P A B C,
  在角内 P A B C -> 在角内 P C B A.
Proof.
    unfold 在角内.
    intros.
    分离合取式.
    ex_and H2 X.
    repeat split; try assumption.
    exists X.
    split.
      apply 中间性的对称性.
      assumption.
    assumption.
Qed.

Lemma col_in_angle :
 forall A B C P,
  A <> B -> C <> B -> P <> B ->
  Out B A P \/ Out B C P ->
  在角内 P A B C.
Proof.
    intros.
    induction H2.
      repeat split; try assumption.
      exists A.
      split.
        apply 中间性的对称性.
        apply ABB中间性.
      right.
      assumption.
    repeat split; try assumption.
    exists C.
    split.
      apply ABB中间性.
    right.
    assumption.
Qed.


Lemma out321__inangle :
 forall A B C P,
  C <> B -> Out B A P ->
  在角内 P A B C.
Proof.
    intros.
    统计不重合点.
    apply col_in_angle; auto.
Qed.


Lemma A在角ABC内 :
 forall A B C,
  A <> B -> C <> B ->
  在角内 A A B C.
Proof.
    intros.
    apply out321__inangle; auto.
    apply out_trivial; auto.
Qed.


Lemma out341__inangle :
 forall A B C P,
  A <> B -> Out B C P ->
  在角内 P A B C.
Proof.
    intros.
    统计不重合点.
    apply col_in_angle; auto.
Qed.


Lemma C在角ABC内 :
 forall A B C,
  A <> B -> C <> B ->
  在角内 C A B C.
Proof.
    intros.
    apply out341__inangle; auto.
    apply out_trivial; auto.
Qed.


Lemma 角端点在角内点与顶点连线两侧 :
 forall A B C P,
  ~ Col B A P -> ~ Col B C P ->
  在角内 P A B C ->
  TS P B A C.
Proof.
    intros.
    unfold 在角内 in H1.
    分离合取式.
    ex_and H4 X.
    induction H5.
      subst X.
      unfold TS.
      repeat split.
        intro.
        apply H.
        apply 等价共线CAB.
        assumption.
        intro.
        apply H0.
        apply 等价共线CAB.
        assumption.
      exists B.
      split.
        apply ABA型共线.
      assumption.
    repeat split.
      intro.
      apply H.
      apply 等价共线CAB.
      assumption.
      intro.
      apply H0.
      apply 等价共线CAB.
      assumption.
    exists X.
    split.
      apply out_col in H5.
      apply 等价共线BCA.
      assumption.
    assumption.
Qed.

Lemma in_angle_out :
 forall A B C P,
  Out B A C ->
  在角内 P A B C ->
  Out B A P.
Proof.
    intros.
    unfold 在角内 in H0.
    分离合取式.
    ex_and H3 X.
    induction H4.
      subst X.
      assert( Bet A B C /\ Out B A C).
        split; assumption.
      apply not_bet_and_out in H4.
      contradiction.
    unfold Out in *.
    分离合取式.
    induction H8; induction H6.
      repeat split; try assumption.
      left.
      assert(Bet B A X).
        eapply 中间性的内传递性1.
          apply H8.
        apply H3.
      eapply 中间性的交换传递性2.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B A X).
        eapply 中间性的内传递性1.
          apply H8.
        assumption.
      eapply l5_3.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B X A).
        eapply 中间性的内传递性2.
          apply H8.
        apply 中间性的对称性.
        assumption.
      apply l5_1 with X; auto.
    repeat split; auto.
    right.
    assert(Bet B X A).
      eapply 中间性的内传递性2.
        apply H8.
      apply 中间性的对称性.
      assumption.
    eapply 中间性的交换传递性2.
      apply H6.
    assumption.
Qed.

Lemma col_in_angle_out :
 forall A B C P,
  Col B A P ->
  ~ Bet A B C ->
  在角内 P A B C ->
  Out B A P.
Proof.
    intros.
    unfold 在角内 in H1.
    分离合取式.
    ex_and H4 X.
    induction H5.
      subst X.
      contradiction.
    induction (两点重合的决定性 A X).
      subst X.
      assumption.
    apply not_bet_out in H0.
      assert(Out B A P /\ Out B C P).
        eapply out2_bet_out.
          assumption.
          apply H5.
        assumption.
      分离合取式.
      assumption.
    assert (Col B A X).
      apply 共线的传递性2 with P; Col.
    apply 共线的传递性3 with X; Col.
Qed.

Lemma l11_25_aux : forall P A B C A',
 在角内 P A B C ->
 ~ Bet A B C ->
 Out B A' A ->
 在角内 P A' B C.
Proof.
    intros.
    unfold Out in H1.
    unfold 在角内 in H.
    分离合取式.
    repeat  split ; try assumption.
    induction H3.
      ex_and H6 X.
      assert(exists T, Bet A' T C /\ Bet X T B).
        eapply 帕施公理.
          apply H3.
        apply 中间性的对称性.
        assumption.
      ex_and H8 T.
      exists T.
      split.
        assumption.
      right.
      induction H7.
        subst B.
        contradiction.
      unfold Out in *.
      分离合取式.
      repeat split.
        intro.
        subst T.
        apply H0.
        apply 中间性的对称性.
        eapply 中间性的外传递性2.
          apply 中间性的对称性.
          apply H8.
          assumption.
        auto.
        assumption.
      induction H11.
        left.
        eapply 中间性的交换传递性2.
          apply 中间性的对称性.
          apply H9.
        assumption.
      eapply l5_3.
        apply 中间性的对称性.
        apply H9.
      assumption.
    ex_and H6 X.
    induction H7.
      subst X.
      contradiction.
    assert(exists T, Bet A' T C /\ Bet B X T).
      eapply outer_pasch.
        apply 中间性的对称性.
        apply H3.
      apply 中间性的对称性.
      assumption.
    ex_and H8 T.
    exists T.
    split.
      assumption.
    right.
    unfold Out in H7.
    分离合取式.
    repeat split.
      intro.
      subst T.
      apply 中间性的同一律 in H9.
      subst X.
      absurde.
      assumption.
    induction H11.
      apply l5_1 with X; auto.
    right.
    eapply 中间性的交换传递性2.
      apply H11.
    assumption.
Qed.

Lemma l11_25 : forall P A B C A' C' P',
 在角内 P A B C ->
 Out B A' A ->
 Out B C' C ->
 Out B P' P ->
 在角内 P' A' B C'.
Proof.
    intros.
    induction (中间性的决定性 A B C).
      repeat split.
        unfold Out in H0.
        分离合取式.
        assumption.
        unfold Out in H1.
        分离合取式.
        assumption.
        unfold Out in H2.
        分离合取式.
        assumption.
      exists B.
      split.
        eapply bet_out_out_bet.
          apply H3.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      left.
      reflexivity.
    assert(在角内 P A' B C).
      eapply l11_25_aux.
        apply H.
        assumption.
      assumption.
    assert(在角内 P A' B C').
      apply l11_24_在角内的对称性.
      eapply l11_25_aux.
        apply l11_24_在角内的对称性.
        apply H4.
        intro.
        apply H3.
        apply 中间性的对称性.
        eapply bet_out_out_bet.
          apply H5.
          apply out_trivial.
          unfold 在角内 in H.
          分离合取式.
          auto.
        assumption.
      assumption.
    unfold 在角内 in H5.
    分离合取式.
    ex_and H8 X.
    induction H9.
      subst X.
      apply False_ind.
      apply H3.
      eapply bet_out_out_bet.
        apply H8.
        assumption.
      assumption.
    repeat split.
      assumption.
      assumption.
      intro.
      subst P'.
      unfold Out in H2.
      分离合取式.
      absurde.
    exists X.
    split.
      assumption.
    right.
    eapply l6_7.
      apply H9.
    apply l6_6.
    assumption.
Qed.

Lemma 在角内推出点不重合 : forall A B C P, 在角内 P A B C ->
  A <> B /\ C <> B /\ P <> B.
Proof.
  intros; unfold 在角内 in *; 分离合取式; repeat split; assumption.
Qed.

Lemma 由一点构造等长线段 : forall A B A', exists B', Cong A' B' A B.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      exists A'.
      subst B.
      apply 等长的平凡同一性.
    assert(exists X : Tpoint, A' <> X).
      apply 每个点均有不同点.
    ex_and H0 X.
    assert(HH:=由一点往一方向构造等长线段_3 A' X A B H1 H).
    ex_and HH B'.
    exists B'.
    assumption.
Qed.

Lemma 给定角一边可作出等角 :
 forall A B C A' B',
  A <> B -> C <> B -> A' <> B' ->
  exists C', 等角 A B C A' B' C'.
Proof.
    intros.
    assert(exists P, ~Col A' B' P).
      eapply 两点不重合则存在不共线的点.
      assumption.
    ex_and H2 P.
    induction (两点重合的决定性 A C).
      subst C.
      exists A'.
      apply 角ABA等于角CDC; assumption.
    assert(exists C', 等角 A B C A' B' C' /\ (OS A' B' C' P \/ Col A' B' C')).
      apply 给定角一边可作出与给定点同侧一点构成等角_可平角.
        assumption.
        assumption.
        auto.
        assumption.
      assumption.
    ex_and H4 C'.
    exists C'.
    assumption.
Qed.
(* 无用 *)
Lemma l11_28 : forall A B C D A' B' C',
 三角形全等 A B C A' B' C' -> Col A C D ->
 exists D', Cong A D A' D' /\ Cong B D B' D' /\ Cong C D C' D'.
Proof.
    intros.
    induction (两点重合的决定性 A C).
      subst C.
      unfold 三角形全等 in H.
      分离合取式.
      apply 等长的对称性 in H1.
      apply 等长的同一性 in H1.
      subst C'.
      induction(两点重合的决定性 A B).
        subst B.
        apply 等长的对称性 in H2.
        apply 等长的同一性 in H2.
        subst B'.
        assert(exists D', Cong A' D' A D).
          apply 由一点构造等长线段.
        ex_and H1 D'.
        exists D'.
        apply 等长的对称性 in H2.
        repeat split; assumption.
      induction (两点重合的决定性 A D).
        exists A'.
        subst D.
        repeat split.
          apply 等长的平凡同一性.
          assumption.
        apply 等长的平凡同一性.
      induction (两点重合的决定性 B D).
        subst D.
        exists B'.
        repeat split.
          assumption.
          apply 等长的平凡同一性.
        assumption.
      assert(exists D'', 等角 B A D B' A' D'').
        eapply 给定角一边可作出等角.
          auto.
          auto.
        intro.
        subst B'.
        apply 等长的同一性 in H.
        contradiction.
      ex_and H5 D''.
      assert(exists D', Out A' D'' D' /\ Cong A' D' A D).
        apply 由一点往一方向构造等长线段_3.
          unfold 等角 in H6.
          分离合取式.
          auto.
        assumption.
      ex_and H5 D'.
      exists D'.
      repeat split.
        apply 等长的对称性.
        assumption.
        assert(等角 B A D B' A' D').
          eapply (l11_10 B A D B' A' D''); try apply out_trivial; auto.
            intro.
            subst B'.
            unfold 等角 in H6.
            分离合取式.
            absurde.
          apply l6_6.
          assumption.
        eapply (等角两边等长则端点间距相等 _ A _ _ A' _).
          apply H8.
          assumption.
        Cong.
      Cong.
    unfold 三角形全等 in H.
    分离合取式.
    (*****************)
    induction(两点重合的决定性 A D).
      subst D.
      exists A'.
      repeat split.
        apply 等长的平凡同一性.
        apply 等长的交换性.
        assumption.
      apply 等长的交换性.
      assumption.
    unfold Col in H0.
    induction H0.
      prolong A' C' D' C D.
      exists D'.
      repeat split.
        eapply (两组连续三点分段等则全体等 A C D A' C' D'); try assumption.
        apply 等长的对称性.
        assumption.
        apply 等长的交换性.
        eapply (五线段公理_等价SAS_with_def A C D B A' C' D' B').
          repeat split; try assumption.
            apply 等长的对称性.
            assumption.
          apply 等长的交换性.
          assumption.
        assumption.
      apply 等长的对称性.
      assumption.
    induction H0.
      assert(exists D', Bet A' D' C' /\ 三角形全等 A D C A' D' C').
        eapply l4_5.
          apply 中间性的对称性.
          assumption.
        assumption.
      ex_and H5 D'.
      unfold 三角形全等 in H6.
      分离合取式.
      exists D'.
      repeat split.
        assumption.
        apply 等长的交换性.
        eapply (l4_2 A D C B A' D' C' B').
        repeat split; try assumption.
          apply 中间性的对称性.
          assumption.
        apply 等长的交换性.
        assumption.
      apply 等长的交换性.
      assumption.
    prolong C' A' D' A D.
    exists D'.
    repeat split.
      apply 等长的对称性.
      assumption.
      apply 等长的交换性.
      eapply (五线段公理_等价SAS_with_def C A D B C' A' D' B').
        repeat split; try assumption.
          apply 中间性的对称性.
          assumption.
          apply 等长的交换性.
          assumption.
          apply 等长的对称性.
          assumption.
        apply 等长的交换性.
        assumption.
      auto.
    eapply 两组连续三点分段等则全体等.
      apply 中间性的对称性.
      apply H0.
      apply H5.
      apply 等长的交换性.
      assumption.
    apply 等长的对称性.
    assumption.
Qed.

Lemma 零角的等角是零角 :
 forall A B C A' B' C',
  Bet A B C ->
  等角 A B C A' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    unfold 等角 in H0.
    分离合取式.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert(Bet A0 B C0).
      apply 中间性的外传递性2 with C; auto.
      apply 中间性的对称性.
      apply 中间性的外传递性2 with A; Between.
    assert(三角形全等 A0 B C0 A1 B' C1).
      repeat split.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply 中间性的对称性.
          apply H4.
          apply H8.
          apply 等长的左交换性.
          assumption.
        apply 等长的对称性.
        apply 等长的右交换性.
        assumption.
        assumption.
      apply 等长的右交换性.
      eapply 两组连续三点分段等则全体等.
        apply H6.
        apply 中间性的对称性.
        apply H10.
        apply 等长的对称性.
        apply 等长的左交换性.
        assumption.
      apply 等长的右交换性.
      assumption.
    assert(Bet A1 B' C1).
      eapply l4_6.
        apply H13.
      assumption.
    eapply 中间性的内传递性1 with C1; auto.
    eapply 中间性的交换传递性1.
      apply 中间性的对称性.
      apply H8.
    assumption.
Qed.

Lemma 角内点和一端点在角另一边同侧 :
 forall A B C P,
  ~ Col A B C ->
  ~ Col B A P ->
  在角内 P A B C ->
  OS A B P C.
Proof.
    intros.
    unfold 在角内 in H1.
    分离合取式.
    ex_and H4 X.
    induction H5.
      subst X.
      apply False_ind.
      apply H.
      unfold Col.
      left.
      assumption.
    unfold OS.
    prolong C A C' C A.
    exists C'.
    assert(TS A B X C').
      repeat split.
        intro.
        apply H0.
        eapply (共线的传递性2 _ X).
          intro.
          subst X.
          apply H.
          left.
          assumption.
          eapply (共线的传递性2 _ A).
            auto.
            apply 等价共线CBA.
            assumption.
          apply ABB型共线.
        apply out_col.
        assumption.
        intro.
        apply H.
        eapply (共线的传递性2 _  C').
          intro.
          subst C'.
          apply 等长的对称性 in H7.
          apply 等长的同一性 in H7.
          subst C.
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
      eapply 中间性的交换传递性1 with C; Between.
    split.
      apply l9_5 with X B; Col.
    repeat split.
      intro.
      apply H.
      apply 等价共线BCA.
      assumption.
      intro.
      apply H.
      eapply (共线的传递性2 _ C').
        intro.
        subst C'.
        unfold TS in H8.
        分离合取式.
        apply H10.
        apply AAB型共线.
        apply 等价共线BAC.
        assumption.
      unfold Col.
      right; right.
      assumption.
    exists A.
    split.
      apply AAB型共线.
    assumption.
Qed.

Lemma 角内两点在角一边同侧 : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q ->
    在角内 P A B C -> 在角内 Q A B C ->
    OS A B P Q.
Proof.
    intros.
    unfold 在角内 in *.
    分离合取式.
    ex_and H9 P'.
    ex_and H6 Q'.
    induction H10.
      subst P'.
      apply 中间性蕴含共线1 in H9.
      contradiction.
    induction H11.
      subst Q'.
      apply 中间性蕴含共线1 in H6.
      contradiction.
    assert(OS A B P' Q').
      prolong P' A T A C.
      unfold OS.
      exists T.
      unfold TS.
      assert(A <> P').
        intro.
        subst P'.
        apply out_col in H10.
        apply H0.
        Col.
      repeat split; auto.
        intro.
        apply H0.
        assert(P' <> B).
          unfold Out in H10.
          分离合取式.
          assumption.
        apply out_col in H10.
        ColR.
        intro.
        induction(两点重合的决定性 A T).
          subst T.
          apply 等长的对称性 in H13.
          apply 等长的同一性 in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply 中间性蕴含共线1 in H9.
        apply 中间性蕴含共线1 in H12.
        assert(Col T A C).
          ColR.
        eapply (共线的传递性2 _ T); Col.
        exists A.
        split; Col.
        intro.
        apply H1.
        assert(Q' <> B).
          unfold Out in H11.
          分离合取式.
          assumption.
        apply out_col in H11.
        ColR.
        intro.
        induction(两点重合的决定性 A T).
          subst T.
          apply 等长的对称性 in H13.
          apply 等长的同一性 in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply 中间性蕴含共线1 in H9.
        apply 中间性蕴含共线1 in H12.
        assert(Col T A C).
          ColR.
        eapply (共线的传递性2 _ T); Col.
      exists A.
      split; Col.
      assert(Bet A P' Q' \/ Bet A Q' P').
        eapply l5_3.
          apply H9.
        assumption.
      induction H15.
        eapply (中间性的外传递性1 _ P'); Between.
      eapply (中间性的交换传递性1 P'); Between.
    assert(OS A B P P').
      eapply (out_one_side_1  _ _ _ _  B); Col.
      apply l6_6.
      auto.
    assert(OS A B Q Q').
      eapply (out_one_side_1  _ _ _ _ B); Col.
      apply l6_6.
      auto.
    eapply one_side_transitivity.
      apply H13.
    apply one_side_symmetry.
    eapply one_side_transitivity.
      apply H14.
    apply one_side_symmetry.
    assumption.
Qed.
(* 无用 *)
Lemma 角内两点在角两边同侧 : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q ->
    ~ Col C B P -> ~ Col C B Q ->
    在角内 P A B C -> 在角内 Q A B C ->
    OS A B P Q /\ OS C B P Q.
Proof.
    intros.
    split.
      apply (角内两点在角一边同侧 _ _ C); Col.
    apply (角内两点在角一边同侧 _ _ A); Col.
      apply l11_24_在角内的对称性.
      auto.
    apply l11_24_在角内的对称性.
    auto.
Qed.

Lemma 共线三点构成的角的等角三点也共线 : forall A B C D E F, Col A B C -> 等角 A B C D E F -> Col D E F.
Proof.
    intros.
    induction H.
      assert (Bet D E F).
        eapply 零角的等角是零角.
          apply H.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert (Out E D F).
        apply (l11_21_a A B C); [|apply H0].
        apply bet_out in H.
          apply l6_6.
          assumption.
          unfold 等角 in H0.
          分离合取式.
          assumption.
      unfold Out in H1.
      分离合取式.
      unfold Col.
      induction H3.
        right; right.
        apply 中间性的对称性.
        assumption.
      right; left.
      assumption.
    assert (Out E D F).
      apply (l11_21_a A B C); [|apply H0].
      apply 中间性的对称性 in H.
      apply bet_out.
        unfold 等角 in H0.
        分离合取式.
        auto.
        assumption.
    unfold Out in H1.
    分离合取式.
    unfold Col.
    induction H3.
      right; right.
      apply 中间性的对称性.
      assumption.
    right; left.
    assumption.
Qed.

Lemma 不共线三点构成的角的等角三点也不共线 : forall A B C D E F, ~ Col A B C -> 等角 A B C D E F -> ~ Col D E F.
Proof.
    intros.
    intro.
    apply H.
    eapply 共线三点构成的角的等角三点也共线.
      apply H1.
    apply 等角的对称性.
    assumption.
Qed.

Lemma 给定角一边可作出共面等角 :
 forall A B C A' B' P,
  A <> B -> C <> B -> A' <> B' ->
  exists C', 等角 A B C A' B' C' /\ 共面 A' B' C' P.
Proof.
    intros.
    destruct (共线的决定性 A' B' P).
      destruct (给定角一边可作出等角 A B C A' B') as [C']; auto.
      exists C'; split; Cop.
    destruct (共线的决定性 A B C).
      destruct (给定角一边可作出等角 A B C A' B') as [C']; auto.
      exists C'; split; auto.
      exists C'; left; split; Col.
      apply (共线三点构成的角的等角三点也共线 A B C); assumption.
    destruct (给定角一边可作出与给定点同侧一点构成等角_非平角 A B C A' B' P) as [C' []]; auto.
    exists C'; split; Cop.
Qed.

Lemma 角度小于等于推出点不重合 : forall A B C D E F, 角度小于等于 A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E.
Proof.
  intros A B C D E F Hlea.
  destruct Hlea as [X [H在角内 HConga]].
  destruct H在角内 as [HDE [HEF _]].
  repeat split; auto.
  apply (角等推AB不重合 A B C D E X); auto.
  apply (角等推CB不重合 A B C D E X); auto.
Qed.

Lemma l11_29_a_大角内可找一点构成小角的等角 : forall A B C D E F, 角度小于等于 A B C D E F ->
  exists Q, 在角内 C A B Q /\ 等角 A B Q D E F.
Proof.
    intros.
    unfold 角度小于等于 in H.
    ex_and H P.
    assert(E <> D /\ B <> A /\ E <> F /\ E <> P /\ B <> C).
      unfold 等角 in *.
      unfold 在角内 in H.
      分离合取式.
      repeat split.
        auto.
        auto.
        auto.
        auto.
      auto.
    分离合取式.
    assert(A <> B /\ C <> B).
      intuition.
    分离合取式.
    assert(HH:=or_bet_out A B C).
    induction HH.
      assert(Bet D E P).
        eapply 零角的等角是零角.
          apply H8.
        assumption.
      exists C.
      split.
        apply C在角ABC内; assumption.
      assert(HH:=H).
      unfold 在角内 in HH.
      分离合取式.
      ex_and H13 X.
      induction H14.
        subst X.
        assert(Bet E F P \/ Bet E P F).
          eapply (l5_2 D).
            auto.
            assumption.
          assumption.
        eapply l11_10.
          apply H0.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          assumption.
        repeat split.
          auto.
          auto.
        assumption.
      assert(Out E P F).
        unfold Out in H14.
        分离合取式.
        induction H16.
          assert( Bet D X P).
            eapply 中间性的内传递性2.
              apply H9.
            assumption.
          assert(Bet D E X).
            eapply 中间性的内传递性1.
              apply H9.
            assumption.
          assert(Bet D E F).
            eapply 中间性的交换传递性2.
              apply H18.
            assumption.
          unfold Out.
          repeat split.
            auto.
            auto.
          apply (l5_2 D); auto.
        assert(Bet D P X).
          eapply 中间性的外传递性1.
            apply H9.
            assumption.
          assumption.
        assert(Bet D P F).
          eapply 中间性的交换传递性2.
            apply H17.
          assumption.
        assert(Bet E P F).
          eapply 中间性的交换传递性1.
            apply H9.
          assumption.
        repeat split.
          auto.
          auto.
        left.
        assumption.
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        assumption.
      eapply l6_6.
      assumption.
    induction H8.
      assert(exists Q, 等角 D E F A B Q).
        apply 给定角一边可作出等角.
          auto.
          auto.
        assumption.
      ex_and H9 Q.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold 等角 in H10.
          分离合取式.
          intuition.
          auto.
        exists A.
        split.
          apply AAB中间性.
        right.
        assumption.
      apply 等角的对称性.
      assumption.
    assert(D <> E /\ F <> E).
      intuition.
    分离合取式.
    assert(HH:=or_bet_out D E F).
    induction HH.
      prolong A B Q E F.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
          assumption.
        exists B.
        split.
          assumption.
        left.
        reflexivity.
      eapply 成中间性三点组的角相等; try assumption.
        intro.
        treat_equalities.
        auto.
    induction H11.
      assert(Out E D P).
        eapply in_angle_out.
          apply H11.
        assumption.
      assert (Out B A C).
        eapply l11_21_a.
          apply H12.
        apply 等角的对称性.
        assumption.
      apply False_ind.
      apply H8.
      apply out_col in H13.
      Col.
    (************)
    assert(exists Q, 等角 D E F A B Q /\ OS A B Q C).
      apply 给定角一边可作出与给定点同侧一点构成等角_非平角; assumption.
    ex_and H12 Q.
    exists Q.
    assert(exists DD, Out E D DD /\ Cong E DD B A).
      eapply 由一点往一方向构造等长线段_3; auto.
    ex_and H14 DD.
    assert(exists FF, Out E F FF /\ Cong E FF B Q).
      eapply 由一点往一方向构造等长线段_3.
        auto.
      unfold 等角 in H12.
      分离合取式.
      auto.
    ex_and H16 FF.
    assert(在角内 P DD E FF).
      eapply l11_25.
        apply H.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      apply out_trivial.
      auto.
    assert(HH18:=H18).
    unfold 在角内 in H18.
    分离合取式.
    ex_and H21 X.
    induction H22.
      subst X.
      assert (Bet D E F).
        eapply bet_out_out_bet.
          apply H21.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H11.
      unfold Col.
      left.
      assumption.
    assert(exists CC, Out B C CC /\ Cong B CC E X).
      apply 由一点往一方向构造等长线段_3.
        auto.
      unfold Out in H22.
      分离合取式.
      auto.
    ex_and H23 CC.
    assert (等角 A B CC DD E X).
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      assumption.
    assert(Cong A CC DD X).
      eapply 等角两边等长则端点间距相等.
        apply H25.
        apply 等长的对称性.
        apply 等长的交换性.
        assumption.
      assumption.
    assert(等角 A B Q DD E FF).
      eapply l11_10.
        apply 等角的对称性.
        apply H12.
        apply out_trivial.
        auto.
        apply out_trivial.
        intro.
        subst Q.
        apply 等长的同一性 in H17.
        subst FF.
        absurde.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(Cong A Q DD FF).
      eapply 等角两边等长则端点间距相等.
        apply H27.
        apply 等长的对称性.
        apply 等长的交换性.
        assumption.
      apply 等长的对称性.
      assumption.
    assert(等角 CC B Q X E FF).
      apply l11_22b with A DD.
      split.
        apply one_side_symmetry.
        eapply out_out_one_side.
          apply invert_one_side.
          apply H13.
        assumption.
      split.
        assert(在角内 X DD E FF).
          eapply l11_25.
            apply HH18.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        apply 角内点和一端点在角另一边同侧 in H29.
          apply invert_one_side in H29.
          apply H29.
          intro.
          apply H11.
          eapply col_out2_col.
            apply H30.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
        intro.
        apply H8.
        eapply (共线三点构成的角的等角三点也共线 D E P); [|apply 等角的对称性, H0].
        eapply col_out2_col.
          apply 等价共线BAC.
          apply H30.
          apply l6_6.
          assumption.
        assumption.
      split.
        apply 等角的对称性.
        eapply l11_10.
          apply 等角的对称性.
          apply 等角的交换性.
          apply H0.
          assumption.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assumption.
    assert(Cong CC Q X FF).
      eapply 等角两边等长则端点间距相等.
        apply H29.
        apply 等长的交换性.
        assumption.
      apply 等长的对称性.
      assumption.
    split.
      assert(在角内 CC A B Q).
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold 等角 in H12.
          分离合取式.
          absurde.
          intro.
          subst CC.
          unfold 等角 in H25.
          分离合取式.
          auto.
        exists CC.
        split.
          eapply l4_6.
            apply H21.
          repeat split; Cong.
        right.
        apply out_trivial.
        unfold Out in H23.
        分离合取式.
        auto.
      eapply l11_25.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        unfold 等角 in H27.
        分离合取式.
        auto.
      assumption.
    apply 等角的对称性.
    assumption.
Qed.

Lemma 任何点都在平角内 : forall A B C P, P <> B -> A <> B -> C <> B -> Bet A B C -> 在角内 P A B C.
Proof.
    intros.
    repeat split; try assumption.
    exists B.
    split.
      assumption.
    left.
    reflexivity.
Qed.


Lemma l11_29_b_能在其内找一点构造等角之角较大 : forall A B C D E F, (exists Q, 在角内 C A B Q /\ 等角 A B Q D E F) ->
  角度小于等于 A B C D E F.
Proof.
    intros.
    ex_and H Q.
    unfold 角度小于等于.
    assert(HH:=H).
    unfold 在角内 in HH.
    分离合取式.
    ex_and H4 X.
    induction H5.
      subst X.
      assert(exists P, 等角 A B C D E P).
        apply 给定角一边可作出等角.
          assumption.
          assumption.
        unfold 等角 in H0.
        分离合取式.
        assumption.
      ex_and H5 P.
      exists P.
      split.
        assert(Bet D E F).
          eapply 零角的等角是零角.
            apply H4.
          assumption.
        apply 任何点都在平角内.
          unfold 等角 in H6.
          分离合取式.
          assumption.
          unfold 等角 in H6.
          分离合取式.
          assumption.
          unfold 等角 in H0.
          分离合取式.
          assumption.
        assumption.
      assumption.
    assert(exists DD, Out E D DD /\ Cong E DD B A).
      apply 由一点往一方向构造等长线段_3.
        unfold 等角 in H0.
        分离合取式.
        auto.
      auto.
    ex_and H6 DD.
    assert(exists FF, Out E F FF /\ Cong E FF B Q).
      apply 由一点往一方向构造等长线段_3.
        unfold 等角 in H0.
        分离合取式.
        auto.
      auto.
    ex_and H8 FF.
    assert(D <> E /\ DD <> E /\ F <> E /\ FF <> E).
      unfold Out in *.
      分离合取式.
      repeat split; try assumption.
    分离合取式.
    assert(HI:=or_bet_out A B C).
    induction HI.
      exists F.
      split.
        apply C在角ABC内.
          assumption.
        assumption.
      assert(等角 A B C A B Q).
        apply out2__conga.
          apply out_trivial.
          auto.
        unfold Out in H5.
        分离合取式.
        induction H16.
          assert(Bet A B X).
            eapply 中间性的内传递性1.
              apply H14.
            assumption.
          assert(Bet B X Q).
            eapply 中间性的交换传递性1.
              apply H17.
            assumption.
          assert(Bet B Q C \/ Bet B C Q).
            apply l5_1 with X; auto.
          unfold Out.
          repeat split; auto.
        assert(Bet A B X).
          eapply 中间性的外传递性2.
            apply H14.
            assumption.
          auto.
        assert(Bet B X Q).
          eapply 中间性的交换传递性1.
            apply H17.
          assumption.
        assert(Bet B C Q).
          eapply 中间性的交换传递性2.
            apply H16.
          assumption.
        unfold Out.
        repeat split.
          auto.
          auto.
        right.
        assumption.
      eapply 角等的传递性.
        apply H15.
      assumption.
    induction H14.
      exists D.
      split.
        apply A在角ABC内.
          assumption.
        assumption.
      assert(等角 A B C A B A).
        apply out2__conga.
          apply out_trivial.
          auto.
        assumption.
      eapply 角等的传递性.
        apply H15.
      apply 角ABA等于角CDC.
        assumption.
      assumption.
    assert(HJ:=or_bet_out A B Q).
    induction HJ.
      assert(exists P, 等角 A B C D E P).
        apply 给定角一边可作出等角.
          auto.
          auto.
        unfold Out in H6.
        分离合取式.
        auto.
      ex_and H16 P.
      exists P.
      split.
        apply 任何点都在平角内.
          unfold 等角 in H17.
          分离合取式.
          assumption.
          assumption.
          assumption.
        eapply 零角的等角是零角.
          apply H15.
        assumption.
      assumption.
    induction H15.
      assert(Out B A C).
        eapply in_angle_out.
          apply H15.
        assumption.
      apply False_ind.
      apply H14.
      unfold Out in H16.
      分离合取式.
      unfold Col.
      induction H18.
        right; right.
        apply 中间性的对称性.
        assumption.
      right; left.
      assumption.
    assert(exists P, 等角 A B C D E P /\ OS D E P F).
      eapply 给定角一边可作出与给定点同侧一点构成等角_非平角.
        assumption.
      eapply 不共线三点构成的角的等角三点也不共线.
        apply H15.
      apply H0.
    ex_and H16 P.
    exists P.
    split.
      assert(exists PP, Out E P PP /\ Cong E PP B X).
        eapply 由一点往一方向构造等长线段_3.
          unfold 等角 in H16.
          分离合取式.
          auto.
        unfold Out in H5.
        分离合取式.
        auto.
      ex_and H18 PP.
      apply l11_25 with PP DD FF; trivial.
      repeat split.
        auto.
        auto.
        unfold Out in H18.
        分离合取式.
        auto.
      exists PP.
      split.
        assert(等角 C B Q P E F).
          apply l11_22b with A D.
          split.
            apply invert_one_side.
            eapply 角内点和一端点在角另一边同侧.
              assumption.
              intro.
              apply H14.
              apply 等价共线BAC.
              assumption.
            assumption.
          split.
            apply invert_one_side.
            apply H17.
          split.
            apply 等角的交换性.
            assumption.
          assumption.
        assert (Cong DD FF A Q).
          eapply 等角两边等长则端点间距相等.
            eapply l11_10.
              apply 等角的对称性.
              apply H0.
              apply l6_6.
              assumption.
              apply l6_6.
              assumption.
              apply l6_6.
              apply out_trivial.
              auto.
            apply out_trivial.
            auto.
            apply 等长的交换性.
            assumption.
          assumption.
        assert(Cong A X DD PP).
          eapply 等角两边等长则端点间距相等.
            eapply l11_10.
              apply H16.
              apply out_trivial.
              auto.
              assumption.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply 等长的对称性.
            apply 等长的交换性.
            assumption.
          apply 等长的对称性.
          assumption.
        assert(Cong X Q PP FF).
          eapply 等角两边等长则端点间距相等.
            eapply l11_10.
              apply H20.
              assumption.
              apply out_trivial.
              auto.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply 等长的对称性.
            apply 等长的交换性.
            assumption.
          apply 等长的对称性.
          assumption.
        eapply l4_6.
          apply H4.
        repeat split.
          assumption.
          apply 等长的对称性.
          assumption.
        assumption.
      right.
      apply out_trivial.
      unfold Out in H15.
      分离合取式.
      unfold Out in H18.
      分离合取式.
      auto.
    assumption.
Qed.

Lemma 角一边反向延长线上点在角内则该角为平角 : forall A B C P, Bet A B P -> 在角内 P A B C -> Bet A B C.
Proof.
    intros.
    unfold 在角内 in H0.
    分离合取式.
    ex_and H3 X.
    induction H4.
      subst X.
      assumption.
    unfold Out in H4.
    分离合取式.
    induction H6.
      assert(Bet A X P).
        eapply 中间性的内传递性2.
          apply H.
        assumption.
      assert(Bet A P C \/ Bet A C P).
        apply (l5_1 _ X).
          intro.
          subst X.
          assert(A = B).
            eapply 双中间性推出点重合.
              apply H.
            assumption.
          contradiction.
          assumption.
        assumption.
      induction H8.
        eapply 中间性的交换传递性2.
          apply H.
        assumption.
      assert(Bet A B X).
        eapply 中间性的内传递性1.
          apply H.
        assumption.
      eapply 中间性的交换传递性2.
        apply H9.
      assumption.
    assert(Bet A B X).
      eapply 中间性的外传递性2.
        apply H.
        assumption.
      auto.
    eapply 中间性的交换传递性2.
      apply H7.
    assumption.
Qed.

Lemma 平角小于等于之角为平角 : forall A B C P, Bet A B P -> 角度小于等于 A B P A B C -> Bet A B C.
Proof.
    intros.
    unfold 角度小于等于 in H0.
    ex_and H0 PP.
    assert (HH:=H0).
    unfold 在角内 in H0.
    分离合取式.
    ex_and H4 X.
    induction H5.
      subst X.
      assumption.
    assert (Bet A B PP).
      eapply 零角的等角是零角.
        apply H.
      assumption.
    eapply 角一边反向延长线上点在角内则该角为平角.
      apply H6.
    assumption.
Qed.


Lemma 零角的等角推出外共线 : forall A B D E F, 等角 A B A D E F -> Out E D F.
Proof.
    intros.
    assert(HH:=H).
    unfold 等角 in H.
    分离合取式.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    assert(三角形全等 B A' C' E D' F').
      repeat split.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply H3.
          apply 中间性的对称性.
          apply H7.
          apply 等长的右交换性.
          apply 等长的对称性.
          assumption.
        apply 等长的右交换性.
        assumption.
        apply 等长的右交换性.
        eapply 两组连续三点分段等则全体等.
          apply H5.
          apply 中间性的对称性.
          apply H9.
          apply 等长的右交换性.
          apply 等长的对称性.
          assumption.
        apply 等长的右交换性.
        assumption.
      assumption.
    assert(Out E D' F').
      apply (cong3_preserves_out B A' C'); [|apply H12].
      unfold Out.
      repeat split.
        intro.
        subst A'.
        apply 中间性的同一律 in H3.
        subst A.
        absurde.
        intro.
        subst C'.
        apply 中间性的同一律 in H5.
        subst A.
        absurde.
      apply l5_1 with A; auto.
    eapply bet2_out_out.
      assumption.
      assumption.
      apply H13.
      assumption.
    assumption.
Qed.
(* 无用 *)
Lemma conga_ex_cong3 : forall A B C A' B' C',
  等角 A B C A' B' C' -> exists AA, exists CC, Out B A AA -> Out B C CC -> 三角形全等 AA B CC A' B' C'.
Proof.
    intros.
    assert(B <> A /\ B <> C /\ B' <> A' /\ B' <> C').
      unfold 等角 in H.
      分离合取式.
      repeat split; auto.
    分离合取式.
    assert(exists AA, Out B A AA /\ Cong B AA B' A').
      apply 由一点往一方向构造等长线段_3; assumption.
    assert(exists CC, Out B C CC /\ Cong B CC B' C').
      apply 由一点往一方向构造等长线段_3; assumption.
    ex_and H4 AA.
    ex_and H5 CC.
    exists AA.
    exists CC.
    intros.
    repeat split.
      apply 等长的交换性.
      assumption.
      eapply 等角两边等长则端点间距相等.
        eapply l11_10.
          apply H.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        auto.
        Cong.
      assumption.
    assumption.
Qed.
(* 不翻译 *)
Lemma conga_preserves_in_angle : forall A B C I A' B' C' I',
 等角 A B C A' B' C' -> 等角 A B I A' B' I' ->
 在角内 I A B C -> OS A' B' I' C' ->
 在角内 I' A' B' C'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ I <> B /\ I' <> B').
      unfold 等角 in *.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    assert(HH1:= or_bet_out A B C).
    induction HH1.
      assert(Bet A' B' C').
        eapply 零角的等角是零角.
          apply H9.
        assumption.
      apply 任何点都在平角内; assumption.
    induction H9.
      assert(Out B A I).
        eapply in_angle_out.
          apply H9.
        assumption.
      assert(Out B' A' I').
        eapply l11_21_a.
          apply H10.
        assumption.
      apply out321__inangle.
        auto.
      assumption.
    assert(HH2:= or_bet_out A B I).
    induction HH2.
      assert(Bet A B C).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H10.
        assumption.
      apply False_ind.
      apply H9.
      unfold Col.
      left.
      assumption.
    induction H10.
      assert(Out B' A' I').
        eapply l11_21_a.
          apply H10.
        assumption.
      eapply col_in_angle; try assumption.
      left.
      assumption.
    (*****************************)
    assert(exists AA', Out B' A' AA' /\ Cong B' AA' B A).
      apply 由一点往一方向构造等长线段_3; auto.
    assert(exists CC', Out B' C' CC' /\ Cong B' CC' B C).
      apply 由一点往一方向构造等长线段_3; auto.
    ex_and H11 AA'.
    ex_and H12 CC'.
    assert(HH:=H1).
    unfold 在角内 in H1.
    分离合取式.
    ex_and H17 J.
    induction H18.
      subst J.
      eapply 任何点都在平角内; try assumption.
      eapply 零角的等角是零角.
        apply H17.
      assumption.
    assert(B <> J).
      unfold Out in H18.
      分离合取式.
      auto.
    assert(~Col A B J).
      intro.
      apply H10.
      apply 等价共线CAB.
      eapply (共线的传递性2 _ J).
        assumption.
        apply out_col.
        assumption.
      apply 等价共线BCA.
      assumption.
    assert(exists J', 等角 A B J  A' B' J' /\ OS A' B' J' I').
      apply 给定角一边可作出与给定点同侧一点构成等角_非平角.
        intro.
        apply H10.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ J).
          unfold Out in H18.
          分离合取式.
          auto.
          apply out_col.
          assumption.
        apply 等价共线BCA.
        assumption.
      eapply 不共线三点构成的角的等角三点也不共线.
        apply H10.
      assumption.
    ex_and H21 J'.
    assert(B' <> J').
      unfold 等角 in H21.
      分离合取式.
      auto.
    assert(exists JJ', Out B' J' JJ' /\ Cong B' JJ' B J).
      apply 由一点往一方向构造等长线段_3.
        assumption.
      assumption.
    ex_and H24 JJ'.
    assert(~Col A' B' J').
      intro.
      apply H20.
      eapply 共线三点构成的角的等角三点也共线.
        apply H26.
      apply 等角的对称性.
      assumption.
    assert(A' <> JJ').
      intro.
      subst JJ'.
      apply H20.
      eapply 共线三点构成的角的等角三点也共线.
        apply out_col in H24.
        apply 等价共线CAB.
        apply H24.
      apply 等角的对称性.
      assumption.
    assert(B' <> JJ').
      unfold Out in H24.
      分离合取式.
      auto.
    assert(~Col A' B' JJ').
      intro.
      apply H26.
      apply 等价共线CAB.
      eapply (共线的传递性2 _ JJ').
        assumption.
        apply 等价共线ACB.
        apply out_col.
        assumption.
      apply 等价共线BCA.
      assumption.
    (****************************************************************)
    assert(等角 A B C AA' B' CC').
      eapply l11_10.
        apply H.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(等角 A' B' J' A' B' JJ').
      apply out2__conga.
        apply out_trivial.
        auto.
      apply l6_6.
      assumption.
    assert(Out B' I' JJ' \/ TS A' B' I' JJ').
      apply conga_cop__or_out_ts.
      apply 等价共面ACBD, col_cop__cop with J'; Col; Cop.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H0.
      apply 等角的对称性.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H31.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H21.
      eapply l11_10.
        apply (同角相等 A B I).
          assumption.
        assumption.
        apply out_trivial.
        auto.
        assumption.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    induction H32.
      assert(等角 J B C J' B' C').
        apply (l11_22b _ _ _ A _ _ _ A').
        split.
          apply invert_one_side.
          apply 角内点和一端点在角另一边同侧.
            assumption.
            intro.
            apply H10.
            apply 等价共线CAB.
            eapply (共线的传递性2 _ J).
              assumption.
              apply out_col.
              assumption.
            apply 等价共线ACB.
            assumption.
          eapply l11_25.
            apply HH.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        split.
          apply one_side_transitivity with I'; apply invert_one_side; assumption.
        split.
          apply 等角的交换性.
          assumption.
        assumption.
      assert(Cong A C AA' CC').
        eapply 等角两边等长则端点间距相等.
          eapply l11_10.
            apply H.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Cong A J AA' JJ').
        eapply 等角两边等长则端点间距相等.
          eapply l11_10.
            apply H0.
            apply out_trivial.
            auto.
            assumption.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(等角 J' B' C' JJ' B' CC').
        apply out2__conga; apply l6_6; assumption.
      assert(Cong J C JJ' CC').
        eapply (等角两边等长则端点间距相等).
          eapply 角等的传递性.
            apply H33.
          apply H36.
          apply 等长的对称性.
          apply 等长的交换性.
          assumption.
        apply 等长的对称性.
        assumption.
      assert(Bet AA' JJ' CC').
        apply (l4_6 A J C).
          apply H17.
        repeat split; assumption.
      apply l11_25 with JJ' AA' CC'; trivial.
        repeat split; auto.
          unfold Out in H11.
          分离合取式.
          auto.
          unfold Out in H12.
          分离合取式.
          auto.
      exists JJ'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(OS B' A' I' JJ').
      eapply out_out_one_side.
        apply invert_one_side.
        apply one_side_symmetry.
        apply H22.
      assumption.
    apply invert_two_sides in H32.
    apply l9_9 in H32.
    contradiction.
Qed.

Lemma l11_30_等角保持小于等于 : forall A B C D E F A' B' C' D' E' F',
 角度小于等于 A B C D E F ->
 等角 A B C A' B' C' ->
 等角 D E F D' E' F' ->
 角度小于等于 A' B' C' D' E' F'.
Proof.
    intros.
    assert(HH:=H).
    apply l11_29_a_大角内可找一点构成小角的等角 in H.
    ex_and H Q.
    apply l11_29_b_能在其内找一点构造等角之角较大.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ D <> E /\ F <> E /\ D' <> E' /\ F' <> E').
      unfold 等角 in *.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    assert(Hi:=or_bet_out A' B' C').
    induction Hi.
      prolong A' B' Q' A' B'.
      exists Q'.
      assert(B' <> Q').
        intro.
        subst Q'.
        apply 等长的对称性 in H13.
        apply 等长的同一性 in H13.
        contradiction.
      assert(A' <> Q').
        intro.
        subst Q'.
        apply 中间性的同一律 in H12.
        contradiction.
      assert(等角 A' B' Q' A' B' C').
        apply 成中间性三点组的角相等; try assumption.
          auto.
      split.
        apply 任何点都在平角内; try assumption.
        auto.
      assert(Bet A B C).
        eapply 零角的等角是零角.
          apply H11.
        apply 等角的对称性.
        assumption.
      assert(Bet A B Q).
        eapply 平角小于等于之角为平角.
          apply H17.
        apply l11_29_b_能在其内找一点构造等角之角较大.
        exists Q.
        split.
          assumption.
        apply 同角相等.
          assumption.
        unfold 等角 in H2.
        分离合取式.
        assumption.
      assert(Bet D E F).
        eapply 零角的等角是零角.
          apply H18.
        assumption.
      assert (Bet D' E' F').
        eapply 零角的等角是零角.
          apply H19.
        assumption.
      eapply 成中间性三点组的角相等; try assumption.
        auto.
    (************************)
    induction H11.
      assert(exists Q', 等角 D' E' F' A' B' Q').
        eapply 给定角一边可作出等角; assumption.
      ex_and H12 Q'.
      exists Q'.
      split.
        apply col_in_angle; try assumption.
          unfold 等角 in H13.
          分离合取式.
          assumption.
        left.
        assumption.
      apply 等角的对称性.
      assumption.
    assert(Hi:=or_bet_out D' E' F').
    induction Hi.
      assert(exists Q', 等角  D' E' F' A' B' Q').
        eapply 给定角一边可作出等角; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(Bet A' B' Q').
        eapply 零角的等角是零角.
          apply H12.
        assumption.
      split.
        apply 任何点都在平角内; try assumption.
        unfold 等角 in H14.
        分离合取式.
        assumption.
      apply 等角的对称性.
      assumption.
    induction H12.
      assert(exists Q', 等角  D' E' F' A' B' Q').
        eapply 给定角一边可作出等角; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(Out B' A' Q').
        eapply l11_21_a.
          apply H12.
        assumption.
      assert(等角 A B Q D' E' F').
        eapply 角等的传递性.
          apply H2.
        assumption.
      assert(Out B A Q).
        eapply l11_21_a.
          apply H12.
        apply 等角的对称性.
        assumption.
      assert(Out B A C).
        eapply in_angle_out.
          apply H16.
        assumption.
      assert(Out  B' A' C').
        eapply l11_21_a.
          apply H17.
        assumption.
      split.
        apply out321__inangle.
          apply out_distinct in H13.
          分离合取式.
          auto.
        assumption.
      apply 等角的对称性.
      assumption.
    assert(exists QQ, 等角 D' E' F' A' B' QQ /\ OS A' B' QQ C').
      eapply 给定角一边可作出与给定点同侧一点构成等角_非平角.
        assumption.
      assumption.
    ex_and H13 Q'.
    exists Q'.
    split.
      apply (conga_preserves_in_angle A B Q C); trivial.
        eapply 角等的传递性.
          apply H2.
        eapply 角等的传递性.
          apply H1.
        assumption.
      apply one_side_symmetry.
      assumption.
    apply 等角的对称性.
    assumption.
Qed.

Lemma l11_31_1_任何角小于等于平角_Out表述 : forall A B C D E F,
 Out B A C -> D <> E -> F <> E ->
 角度小于等于 A B C D E F.
Proof.
    intros.
    unfold 角度小于等于.
    exists D.
    split.
      apply A在角ABC内; assumption.
    apply l11_21_b.
      assumption.
    apply out_trivial.
    auto.
Qed.

Lemma l11_31_1_任何角小于等于平角_Bet表述 : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 Bet D E F ->
 角度小于等于 A B C D E F.
Proof.
intros; destruct (给定角一边可作出等角 A B C D E) as [P H等角]; auto.
exists P; split; try apply 任何点都在平角内; unfold 等角 in *; 分离合取式; auto.
Qed.

Lemma 任何角小于等于自己 : forall A B C,
 A <> B -> C <> B -> 角度小于等于 A B C A B C.
Proof.
    intros.
    unfold 角度小于等于.
    exists C .
    split.
      apply C在角ABC内; assumption.
    apply 同角相等; assumption.
Qed.

Lemma 等角小于等于自己 : forall A B C D E F,
 等角 A B C D E F -> 角度小于等于 A B C D E F.
Proof.
    intros.
    unfold 角度小于等于.
    exists F.
    split.
      apply C在角ABC内.
        apply (角等推DE不重合 A B C D E F); assumption.
        apply (角等推FE不重合 A B C D); assumption.
    assumption.
Qed.

Lemma 等角小于等于自己_交换 : forall A B C D E F,
 等角 A B C D E F -> 角度小于等于 D E F A B C.
Proof.
    intros; apply 等角小于等于自己, 等角的对称性; trivial.
Qed.

Lemma 角度小于等于的左交换性 : forall A B C D E F, 角度小于等于 A B C D E F -> 角度小于等于 C B A D E F.
Proof.
    intros.
    unfold 角度小于等于 in *.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply 等角的左交换性.
    assumption.
Qed.

Lemma 角度小于等于的右交换性 : forall A B C D E F, 角度小于等于 A B C D E F -> 角度小于等于 A B C F E D.
Proof.
    intros.
    apply l11_29_b_能在其内找一点构造等角之角较大.
    apply l11_29_a_大角内可找一点构成小角的等角 in H.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply 等角的右交换性.
    assumption.
Qed.

Lemma 角度小于等于的交换性 : forall A B C D E F, 角度小于等于 A B C D E F -> 角度小于等于 C B A F E D.
Proof.
    intros.
    apply 角度小于等于的左交换性.
    apply 角度小于等于的右交换性.
    assumption.
Qed.

Lemma 角度小于的左交换性 : forall A B C D E F, 角度小于 A B C D E F -> 角度小于 C B A D E F.
Proof.
    unfold 角度小于.
    intros.
    分离合取式.
    split.
      apply 角度小于等于的左交换性.
      assumption.
    intro.
    apply H0.
    apply 等角的左交换性.
    assumption.
Qed.

Lemma 角度小于的右交换性 : forall A B C D E F, 角度小于 A B C D E F -> 角度小于 A B C F E D.
Proof.
    unfold 角度小于.
    intros.
    分离合取式.
    split.
      apply 角度小于等于的右交换性.
      assumption.
    intro.
    apply H0.
    apply 等角的右交换性.
    assumption.
Qed.

Lemma 角度小于的交换性 : forall A B C D E F, 角度小于 A B C D E F -> 角度小于 C B A F E D.
Proof.
    intros.
    apply 角度小于的左交换性.
    apply 角度小于的右交换性.
    assumption.
Qed.
(* 不翻译 *)
Lemma lea_out4__lea : forall A B C D E F A' C' D' F',
 角度小于等于 A B C D E F -> Out B A A' -> Out B C C' -> Out E D D' -> Out E F F' ->
 角度小于等于 A' B C' D' E F'.
Proof.
  intros A B C D E F A' C' D' F' Hl HA HC HD HF.
  apply (l11_30_等角保持小于等于 A B C D E F); trivial; apply out2__conga; apply l6_6; assumption.
Qed.

Lemma 零角小于等于任何角 : forall A B C D E, A<>B -> C<>D -> D<>E -> 角度小于等于 A B A C D E.
Proof.
  intros A B C D E HAB HCD HDE.
  apply l11_31_1_任何角小于等于平角_Out表述; try (apply out_trivial); auto.
Qed.

Lemma 角内点分角小于等于大角1 : forall A B C P, 在角内 P A B C -> 角度小于等于 A B P A B C.
Proof.
  intros A B C P HIn.
  exists P; split; trivial.
  unfold 在角内 in HIn; 分离合取式.
  apply 同角相等; auto.
Qed.

Lemma 角内点分角小于等于大角2 : forall A B C P, 在角内 P A B C -> 角度小于等于 P B C A B C.
Proof.
  intros; apply 角度小于等于的交换性, 角内点分角小于等于大角1, l11_24_在角内的对称性; assumption.
Qed.

Lemma 非边上角内点分角小于大角 : forall A B C P, ~ Col P B C -> 在角内 P A B C -> 角度小于 A B P A B C.
Proof.
  intros A B C P HNCol HIn.
  split.
    apply 角内点分角小于等于大角1, HIn.
  intro HConga.
  apply conga_cop__or_out_ts in HConga; [|Cop].
  destruct HConga as [|Habs].
    apply HNCol; Col.
  apply (l9_9 A B P C).
    assumption.
  destruct Habs as [HP [HC]].
  apply 角内点和一端点在角另一边同侧; Col.
Qed.

Lemma 在角内的传递性 : forall A B C D E,
 在角内 C A B D -> 在角内 D A B E -> 在角内 C A B E.
Proof.
    intros.
    assert(HA1 :=H).
    assert(HA2:= H0).
    unfold 在角内 in H.
    unfold 在角内 in H0.
    分离合取式.
    ex_and H3 DD.
    ex_and H6 CC.
    induction H8; induction H7.
      subst CC.
      subst DD.
      apply 任何点都在平角内; assumption.
      subst CC.
      assert(Bet A B E).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H6.
        assumption.
      apply 任何点都在平角内; assumption.
      subst DD.
      apply 任何点都在平角内; assumption.
    assert(在角内 C A B DD).
      eapply l11_25.
        apply HA1.
        apply out_trivial.
        auto.
        assumption.
      apply out_trivial.
      auto.
    unfold 在角内 in H9.
    分离合取式.
    ex_and H12 CC'.
    induction H13.
      subst CC'.
      assert(Bet A B E).
        eapply 中间性的交换传递性2.
          apply H12.
        assumption.
      apply 任何点都在平角内; assumption.
    apply l11_25 with CC' A E; [|apply out_trivial..|apply l6_6]; auto.
      repeat split; auto.
        unfold Out in H13.
        分离合取式.
        auto.
      exists CC'.
      split.
        eapply 中间性的交换传递性2.
          apply H12.
        assumption.
      right.
      apply out_trivial.
      unfold Out in H13.
      分离合取式.
      auto.
Qed.

Lemma 角度小于等于的传递性 : forall A B C A1 B1 C1 A2 B2 C2,
 角度小于等于 A B C A1 B1 C1 ->
 角度小于等于 A1 B1 C1 A2 B2 C2 ->
 角度小于等于 A B C A2 B2 C2.
Proof.
    intros.
    assert(Hlea1 := H).
    assert (Hlea2 := H0).
    unfold 角度小于等于 in H.
    unfold 角度小于等于 in H0.
    ex_and H P1.
    ex_and H0 P2.
    assert( A <> B /\ C <> B /\ A1 <> B1 /\ C1 <> B1 /\ A2 <> B2 /\ C2 <> B2).
      unfold 等角 in *.
      unfold 在角内 in H0.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    assert(HH1 := or_bet_out A B C).
    induction HH1.
      assert(Bet A1 B1 P1).
        eapply 零角的等角是零角.
          apply H9.
        assumption.
      assert(Bet A1 B1 C1).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H10.
        assumption.
      assert(Bet A2 B2 P2).
        eapply 零角的等角是零角.
          apply H11.
        assumption.
      assert(Bet A2 B2 C2).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H12.
        assumption.
      apply l11_31_1_任何角小于等于平角_Bet表述; assumption.
    induction H9.
      apply l11_31_1_任何角小于等于平角_Out表述; assumption.
    assert(HH2 := or_bet_out A2 B2 C2).
    induction HH2.
      apply l11_31_1_任何角小于等于平角_Bet表述; assumption.
    induction H10.
      assert(Out B2 A2 P2).
        eapply in_angle_out.
          apply H10.
        assumption.
      assert(Out B1 A1 C1).
        eapply l11_21_a.
          apply H11.
        apply 等角的对称性.
        assumption.
      assert(Out B1 A1 P1).
        eapply in_angle_out.
          apply H12.
        assumption.
      assert(Out B A C).
        eapply l11_21_a.
          apply H13.
        apply 等角的对称性.
        assumption.
      apply l11_31_1_任何角小于等于平角_Out表述; assumption.
    assert(exists P, 等角 A B C A2 B2 P /\ OS A2 B2 P C2).
      apply 给定角一边可作出与给定点同侧一点构成等角_非平角; assumption.
    ex_and H11 P.
    assert (OS A2 B2 P2 C2).
      apply 角内点和一端点在角另一边同侧.
        assumption.
        assert (B2 <> A2).
          auto.
        assert(P2 <> A2).
          intro.
          subst P2.
          assert(Out B1 A1 C1).
            apply (l11_21_a A2 B2 A2).
              apply out_trivial.
              auto.
            apply 等角的对称性.
            apply H2.
          assert(Out B1 A1 P1).
            eapply in_angle_out.
              apply H14.
            assumption.
          assert(Out B A C).
            eapply l11_21_a.
              apply H15.
            apply 等角的对称性.
            assumption.
          apply H9.
          apply out_col in H16.
          apply 等价共线BAC.
          assumption.
        assert(HH:=or_bet_out A2 B2 P2 ).
        induction HH.
          assert (Bet A2 B2 C2).
            eapply 角一边反向延长线上点在角内则该角为平角.
              apply H15.
            apply H0.
          intro.
          apply H10.
          unfold Col.
          left.
          assumption.
          induction H15.
            assert(Out B1 A1 C1).
              eapply l11_21_a.
                apply H15.
              apply 等角的对称性.
              assumption.
            assert( Out B1 A1 P1).
              eapply in_angle_out.
                apply H16.
              assumption.
            assert (Out B A C).
              eapply l11_21_a.
                apply H17.
              apply 等角的对称性.
              assumption.
            apply False_ind.
            apply H9.
            apply out_col in H18.
            apply 等价共线BAC.
            assumption.
          intro.
          apply H15.
          apply 等价共线BAC.
          assumption.
          assumption.
        unfold 等角 in H2.
    assert(OS A2 B2 P P2).
      eapply one_side_transitivity.
        apply H12; eapply l11_21_a.
      apply one_side_symmetry.
      assumption.
    unfold 角度小于等于.
    exists P.
    split.
      eapply (在角内的传递性 _ _ _ P2).
        apply (conga_preserves_in_angle A1 B1 C1 P1); trivial.
          eapply 角等的传递性.
            apply 等角的对称性.
            apply H1.
          assumption.
        assumption.
      assumption.
Qed.


Lemma 双在角内推等角 : forall A B C D,
 在角内 D A B C -> 在角内 C A B D -> 等角 A B C A B D.
Proof.
    intros.
    unfold 在角内 in *.
    分离合取式.
    ex_and H3 CC.
    ex_and H6 DD.
    induction H7; induction H8.
      subst DD.
      subst CC.
      apply 成中间性三点组的角相等; try assumption.
        auto.
        auto.
      subst CC.
      unfold Out in H8.
      分离合取式.
      induction H9.
        assert(Bet A B C).
          apply 中间性的交换传递性2 with DD; trivial.
          eapply 中间性的内传递性1.
            apply H3.
          assumption.
        apply 成中间性三点组的角相等; try assumption.
          auto.
          auto.
      assert(Bet A B C).
        eapply 中间性的交换传递性2.
          eapply 中间性的外传递性2.
            apply H3.
            apply H9.
          auto.
        assumption.
        apply 成中间性三点组的角相等; try assumption.
          auto.
          auto.
      subst DD.
      assert(Bet A B D).
        unfold Out in H7.
        分离合取式.
        induction H9.
          eapply 中间性的交换传递性2.
            eapply 中间性的内传递性1.
              apply H6.
            apply H9.
          assumption.
        eapply 中间性的交换传递性2.
          eapply 中间性的外传递性2.
            apply H6.
            apply H9.
          auto.
        assumption.
        apply 成中间性三点组的角相等; try assumption.
          auto.
          auto.
    assert(exists B', Bet CC B' C /\ Bet DD B' D).
      eapply 帕施公理.
        apply 中间性的对称性.
        apply H3.
      apply 中间性的对称性.
      assumption.
    ex_and H9 X.
    assert (Out B X C).
      eapply out_bet_out_2.
        apply H7.
      assumption.
    assert(Out B X D).
      eapply out_bet_out_2.
        apply H8.
      assumption.
    assert (Out B C D).
      apply l6_7 with X.
        apply l6_6.
        assumption.
      assumption.
    apply out2__conga.
      apply out_trivial.
      auto.
    apply l6_6.
    assumption.
Qed.

Lemma 双角度偏序推等角 : forall A B C D E F,
 角度小于等于 A B C D E F -> 角度小于等于 D E F A B C -> 等角 A B C D E F.
Proof.
    intros.
    induction (共线的决定性 A B C).
      induction (中间性的决定性 A B C).
        apply 角度小于等于推出点不重合 in H0; 分离合取式.
        apply 成中间性三点组的角相等; auto.
        ex_and H P.
        apply 角一边反向延长线上点在角内则该角为平角 with P; trivial.
        apply (零角的等角是零角 A B C); assumption.
      apply not_bet_out in H2; trivial.
      apply l11_21_b; trivial.
      ex_and H0 P.
      apply (l11_21_a A B P).
        apply in_angle_out with C; assumption.
      apply 等角的对称性; assumption.
    apply l11_29_a_大角内可找一点构成小角的等角 in H.
    unfold 角度小于等于 in *.
    ex_and H Q.
    ex_and H0 P.
    assert(A <> B /\ Q <> B /\ P <> B /\ D <> E /\ F <> E).
      unfold 等角 in *.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    assert(等角 A B Q A B P).
      eapply 角等的传递性.
        apply H2.
      assumption.
    assert(HH1:= or_bet_out A B Q).
    induction HH1.
      assert(Bet A B P).
        eapply 零角的等角是零角.
          apply H10.
        assumption.
      assert(Bet A B C).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H11.
        assumption.
      assert(Bet D E F).
        eapply 零角的等角是零角.
          apply H10.
        assumption.
      eapply 成中间性三点组的角相等; try assumption.
        unfold 在角内 in H0.
        分离合取式.
        auto.
        auto.
    induction H10.
      assert(Out E D F).
        eapply l11_21_a.
          apply H10.
        assumption.
      assert(Out B A P).
        eapply l11_21_a.
          apply H11.
        apply H3.
      assert(Out B A C).
        eapply in_angle_out.
          apply H10.
        assumption.
      eapply l11_21_b.
        assumption.
      assumption.
    assert(HH2:= or_bet_out A B P).
    induction HH2.
      assert(Bet A B C).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H11.
        assumption.
      assert(Bet D E F).
        eapply 零角的等角是零角.
          apply H11.
        apply 等角的对称性.
        assumption.
      apply 成中间性三点组的角相等; try assumption.
        unfold 在角内 in H0.
        分离合取式.
        auto.
        auto.
    induction H11.
      assert(Out B A Q).
        eapply l11_21_a.
          apply H11.
        apply 等角的对称性.
        assumption.
      assert (Out B A C).
        eapply in_angle_out.
          apply H12.
        assumption.
      assert(Out E D F).
        eapply l11_21_a.
          apply H12.
        assumption.
      apply l11_21_b.
        assumption.
      assumption.
    assert(Out B P Q \/ TS A B P Q).
      apply conga_cop__or_out_ts.
      apply coplanar_trans_1 with C; Cop; Col.
      apply 等角的对称性.
      assumption.
    induction H12.
      assert(在角内 C A B P).
        eapply l11_25.
          apply H.
          apply out_trivial.
          auto.
          assumption.
        apply out_trivial.
        intro.
        subst C.
        unfold 在角内 in H0.
        分离合取式.
        absurde.
      assert(等角 A B C A B P).
        apply 双在角内推等角; assumption.
      eapply 角等的传递性.
        apply H14.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H9.
      assumption.
    assert(C <> B).
      unfold 在角内 in H0.
      分离合取式.
      assumption.
    assert(HH:=or_bet_out A B C).
    induction HH.
      assert(Bet A B Q).
        eapply 角一边反向延长线上点在角内则该角为平角.
          apply H14.
        apply H.
      apply False_ind.
      apply H10.
      unfold Col.
      left.
      assumption.
    induction H14.
      assert(Out B A P).
        eapply in_angle_out.
          apply H14.
        assumption.
      apply False_ind.
      apply H11.
      apply out_col in H15.
      apply 等价共线BAC.
      assumption.
    apply 角内点和一端点在角另一边同侧 in H.
      apply 角内点和一端点在角另一边同侧 in H0.
        assert(OS A B P Q).
          eapply one_side_transitivity.
            apply H0.
          assumption.
        apply l9_9 in H15.
          contradiction.
        assumption.
        assumption.
      intro.
      apply H11.
      apply 等价共线BAC.
      assumption.
      assumption.
    intro.
    apply H14.
    apply 等价共线BAC.
    assumption.
Qed.

Lemma 共线三点构成的角大于等于任何角则该三点构成中间性 : forall A B C X Y Z, Col X Y Z -> 角度小于 A B C X Y Z -> Bet X Y Z.
Proof.
    intros.
    destruct H0.
    assert (Hd := H0).
    apply not_out_bet.
      assumption.
    intro.
    apply H1.
    apply 双角度偏序推等角.
      assumption.
    apply 角度小于等于推出点不重合 in H0.
    分离合取式.
    apply l11_31_1_任何角小于等于平角_Out表述; auto.
Qed.

Lemma 共线三点构成的角大于等于任何角则该三点构成外共线 : forall A B C X Y Z, Col A B C -> 角度小于 A B C X Y Z -> Out B A C.
Proof.
    intros.
    apply not_bet_out.
      assumption.
    intro.
    destruct H0.
    apply H2.
    apply 双角度偏序推等角.
      assumption.
    apply 角度小于等于推出点不重合 in H0.
    分离合取式.
    apply l11_31_1_任何角小于等于平角_Bet表述; auto.
Qed.

Lemma 角度小于推不重合 : forall A B C D E F, 角度小于 A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E /\ D <> F.
Proof.
  intros A B C D E F Hlta.
  assert (Hlea : 角度小于等于 A B C D E F) by (destruct Hlta; assumption).
  apply 角度小于等于推出点不重合 in Hlea.
  分离合取式.
  repeat split; auto.
  intro.
  subst F.
  assert (Bet D E D) by (apply (共线三点构成的角大于等于任何角则该三点构成中间性 A B C); Col).
  treat_equalities; auto.
Qed.

Lemma 角度大于推不重合 : forall A B C D E F, 角度大于 A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E /\ A <> C.
Proof.
  intros A B C D E F Hgta.
  apply 角度小于推不重合 in Hgta.
  分离合取式.
  repeat split; auto.
Qed.

Lemma 角为锐角推不重合 : forall A B C, 为锐角 A B C -> A<>B /\ C<>B.
Proof.
  intros A B C Hacute.
  destruct Hacute as [x [y [z [HPer Hlta]]]].
  apply 角度小于推不重合 in Hlta.
  分离合取式.
  split; auto.
Qed.

Lemma 角为钝角推不重合 : forall A B C, 为钝角 A B C -> A<>B /\ C<>B /\ A <> C.
Proof.
  intros A B C Hobtuse.
  destruct Hobtuse as [x [y [z [HPer Hgta]]]].
  apply 角度大于推不重合 in Hgta.
  分离合取式.
  split; auto.
Qed.
(* 
   P'
   |
   |
   B
  /|\
 / | \
A  |  C
   |
   P
*)
Lemma 角两侧两点必有一点在角内 : forall A B C P P',
 B <> P' ->
 TS B P A C ->
 Bet P B P' ->
 在角内 P A B C \/ 在角内 P' A B C.
Proof.
    intros.
    unfold TS in H0.
    分离合取式.
    ex_and H3 T.
    assert(A <> B).
      intro.
      subst A.
      apply H0.
      apply AAB型共线.
    assert(C <> B).
      intro.
      subst C.
      apply H2.
      apply AAB型共线.
    induction (两点重合的决定性 B T).
      subst T.
      left.
      repeat split.
        assumption.
        assumption.
        intro.
        subst B.
        Col.
      exists B.
      split.
        assumption.
      left.
      reflexivity.
    assert(P <> B /\ T <> B).
      split.
        intro.
        subst B.
        Col.
      auto.
    分离合取式.
    assert(HH:= or_bet_out P B T).
    induction HH.
      right.
      unfold 在角内.
      repeat split; try assumption.
        unfold Out in H1.
        分离合取式.
        auto.
      exists T.
      split.
        assumption.
      right.
      unfold Out.
      repeat split.
        auto.
        auto.
      apply (l5_2 P); auto.
    induction H10.
      left.
      unfold 在角内.
      repeat split; try assumption.
      auto.
      exists T.
      split.
        assumption.
      right.
      apply l6_6.
      assumption.
    apply 等价共线CBA in H3.
    contradiction.
Qed.
(* 
                     D
      C            _//
       \         _//
        \      _//
         \   _//
          \ //
  A--------B------------A'
*)
Lemma 在角内的特殊反向性 :
 forall A B A' C D,
  A' <> B ->
  Bet A B A' ->
  在角内 C A B D ->
  在角内 D A' B C.
Proof.
    intros.
    assert (Hd := H1).
    apply 在角内推出点不重合 in Hd.
    分离合取式.
    induction (共线的决定性 B A C).
      assert(HH:=or_bet_out C B A).
      induction HH.
        assert(Bet A B D).
          eapply 角一边反向延长线上点在角内则该角为平角.
            apply 中间性的对称性.
            apply H6.
          assumption.
        assert(Out B A' C).
          repeat split; try assumption.
          eapply l5_2.
            apply H2.
            assumption.
          apply 中间性的对称性.
          assumption.
        assert( Out B D A').
          repeat split; try assumption.
          eapply l5_2.
            apply H2.
            assumption.
          assumption.
        apply out321__inangle.
          auto.
        apply l6_6.
        assumption.
      induction H6.
        repeat split; try assumption.
        exists B.
        split.
          unfold Out in H6.
          分离合取式.
          induction H8.
            eapply 中间性的内传递性1.
              apply 中间性的对称性.
              apply H0.
            assumption.
          eapply 中间性的外传递性2.
            apply 中间性的对称性.
            apply H0.
            assumption.
          auto.
        left.
        reflexivity.
      apply False_ind.
      apply H6.
      apply 等价共线CAB.
      assumption.
    induction (共线的决定性 B D C).
      assert(HH:=or_bet_out C B D).
      induction HH.
        assert(OS A B C D).
          apply 角内点和一端点在角另一边同侧.
            intro.
            apply H5.
            eapply (共线的传递性2 _ D).
              auto.
              apply 等价共线BCA.
              assumption.
            assumption.
            assumption.
          assumption.
        assert(TS A B C D).
          repeat split; try assumption.
            intro.
            apply H5.
            apply 等价共线CBA.
            assumption.
            intro.
            apply H5.
            eapply (共线的传递性2 _ D).
              auto.
              apply 等价共线CAB.
              assumption.
            assumption.
          exists B.
          split.
            apply ABA型共线.
          assumption.
        apply l9_9 in H9.
        contradiction.
      induction H7.
        assert(在角内 C A' B C).
          apply C在角ABC内; assumption.
        eapply l11_25.
          apply H8.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H7.
      apply 等价共线CAB.
      assumption.
    assert( HH:= H1).
    apply 角端点在角内点与顶点连线两侧 in HH.
      assert(HH1:=H1).
      unfold 在角内 in H1.
      分离合取式.
      ex_and H9 X.
      induction H10.
        subst X.
        apply col_in_angle; try assumption.
        left.
        repeat split; try assumption.
        eapply l5_2.
          apply H1.
          assumption.
        assumption.
      assert(HH0:= HH).
      unfold TS in HH.
      assert (C <> B).
        分离合取式.
        intro.
        subst B.
        Col.
      分离合取式.
      assert(OS D B C A).
        apply 角内点和一端点在角另一边同侧.
          intro.
          apply H12.
          apply 等价共线BCA.
          eapply (共线的传递性2 _ X).
            unfold Out in H10.
            分离合取式.
            auto.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ D).
              intro.
              subst D.
              apply 中间性的同一律 in H9.
              subst X.
              ex_and H14 T.
              apply 中间性的同一律 in H14.
              subst T.
              contradiction.
              apply 等价共线CAB.
              assumption.
            apply 等价共线ACB.
            apply 中间性蕴含共线1.
            assumption.
          apply out_col.
          assumption.
          intro.
          apply H13.
          apply 等价共线BCA.
          assumption.
        apply l11_24_在角内的对称性.
        assumption.
      assert(~Col A D B).
        intro.
        apply H12.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ X).
          unfold Out in H10.
          分离合取式.
          auto.
          apply 等价共线BCA.
          eapply (共线的传递性2 _ D).
            intro.
            subst D.
            apply 中间性的同一律 in H9.
            subst X.
            apply H13.
            apply 等价共线BCA.
            apply out_col.
            assumption.
            assumption.
          apply 等价共线ACB.
          apply 中间性蕴含共线1.
          assumption.
        apply out_col.
        assumption.
      assert(~Col A' D B).
        intro.
        apply H16.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ A').
          auto.
          apply 等价共线BCA.
          apply 中间性蕴含共线1.
          assumption.
        apply 等价共线CAB.
        assumption.
      assert(TS D B A A').
        repeat split; try assumption.
        exists B.
        split.
          apply ABA型共线.
        assumption.
      assert(TS D B C A' ).
        eapply l9_8_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      unfold TS in H19.
      assert (~ Col C D B).
        分离合取式.
        assumption.
      分离合取式.
      ex_and H22 Y.
      repeat split; try assumption.
      exists Y.
      split.
        apply 中间性的对称性.
        assumption.
      right.
      apply 等价共线BCA in H22.
      unfold Col in H22.
      induction H22.
        assert(OS C B A' Y).
          apply out_one_side.
            left.
            intro.
            apply H12.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ A').
              auto.
              apply 等价共线BCA.
              apply 中间性蕴含共线1.
              assumption.
            apply 等价共线BCA.
            assumption.
          apply l6_6.
          apply bet_out.
            intro.
            subst Y.
            apply H13.
            apply 等价共线ACB.
            apply 中间性蕴含共线1.
            assumption.
          assumption.
        assert(TS C B Y D).
          repeat split.
            intro.
            apply H20.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ Y).
              intro.
              subst Y.
              unfold OS in H24.
              ex_and H24 C0.
              unfold TS in H26.
              分离合取式.
              apply H26.
              apply ABA型共线.
              apply 等价共线CAB.
              assumption.
            apply 等价共线BCA.
            apply 中间性蕴含共线1.
            assumption.
            intro.
            apply H20.
            apply 等价共线BAC.
            assumption.
          exists B.
          split.
            apply ABA型共线.
          apply 中间性的对称性.
          assumption.
        assert(TS C B A A').
          repeat split; try assumption.
            intro.
            apply H12.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ A').
              auto.
              apply 等价共线BCA.
              apply 中间性蕴含共线1.
              assumption.
            apply 等价共线CAB.
            assumption.
          exists B.
          split.
            apply ABA型共线.
          assumption.
        assert(TS C B Y A).
          eapply l9_8_2.
            apply l9_2.
            apply H26.
          assumption.
        assert(OS C B A D).
          eapply l9_8_1.
            apply l9_2.
            apply H27.
          apply l9_2.
          assumption.
        apply l9_9 in HH0.
        contradiction.
      repeat split.
        intro.
        subst Y.
        apply H12.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ A').
          auto.
          apply 等价共线BCA.
          apply 中间性蕴含共线1.
          assumption.
        apply 等价共线BCA.
        apply 中间性蕴含共线1.
        assumption.
        assumption.
      induction H22.
        left.
        assumption.
      right.
      apply 中间性的对称性.
      assumption.
      intro.
      apply H5.
      assumption.
    assumption.
Qed.

Lemma 在角内的传递性2 : forall A B C D E, 在角内 C A B D -> 在角内 D A B E -> 在角内 D C B E.
Proof.
  intros A B C D E HC HD.
  destruct (由一点往一方向构造等长线段 E B E B) as [E' [HE1 HE2]].
  assert (Hd := HD).
  apply 在角内推出点不重合 in Hd.
  分离合取式; 统计不重合点.
  apply l11_24_在角内的对称性, 在角内的特殊反向性 with E'; Between.
  apply l11_24_在角内的对称性, 在角内的传递性 with A; apply l11_24_在角内的对称性; trivial.
  apply 在角内的特殊反向性 with E; auto.
  apply l11_24_在角内的对称性; trivial.
Qed.
(*
   C    D----E---D'
    \         \
 A---B----A'   F
*)
Lemma l11_36_双补角组中的角度偏序 : forall A B C D E F A' D',
 A <> B -> A' <> B -> D <> E -> D' <> E ->
 Bet A B A' -> Bet D E D' ->
 (角度小于等于 A B C D E F <-> 角度小于等于 D' E F A' B C).
Proof.
    intros.
    split.
      intro.
      assert(HH:=H5).
      apply l11_29_a_大角内可找一点构成小角的等角 in H5.
      unfold 角度小于等于.
      ex_and H5 P.
      exists P.
      split.
        eapply (在角内的特殊反向性 A); try assumption.
      eapply l11_13.
        apply 等角的对称性.
        apply H6.
        assumption.
        assumption.
        assumption.
      assumption.
    intro.
    assert(HH:=H5).
    unfold 角度小于等于 in H5.
    apply l11_29_b_能在其内找一点构造等角之角较大.
    ex_and H5 P.
    exists P.
    split.
      eapply (在角内的特殊反向性 A'); try assumption.
      apply 中间性的对称性.
      assumption.
    eapply l11_13.
      apply 等角的对称性.
      apply H6.
      apply 中间性的对称性.
      assumption.
      assumption.
      apply 中间性的对称性.
      assumption.
    assumption.
Qed.

Lemma l11_41_证明辅助定理 : forall A B C D,
 ~ Col A B C ->
 Bet B A D ->
 A <> D ->
 角度小于 A C B C A D.
Proof.
    intros.
    assert(exists M , 中点 M A C).
      apply 中点的存在性.
    ex_and H2 M.
    double B M P.
    assert(三角形全等 A C B C A P).
      repeat split.
        apply 等长的伪自反性.
        eapply l7_13_同中点组两侧等长.
          apply M是AB中点则M是BA中点.
          apply H3.
        apply M是AB中点则M是BA中点.
        assumption.
      eapply l7_13_同中点组两侧等长.
        apply H3.
      apply M是AB中点则M是BA中点.
      assumption.
    assert(A <> C).
      intro.
      subst C.
      apply H.
      apply ABA型共线.
    assert(B <> C).
      intro.
      subst C.
      apply H.
      apply ABB型共线.
    assert(C <> D).
      intro.
      subst C.
      apply H.
      apply 等价共线BAC.
      apply 中间性蕴含共线1.
      assumption.
    assert(A <> M).
      intro.
      subst M.
      apply A是AB中点则A与B重合 in H3.
      contradiction.
    assert(等角 A C B C A P).
      apply 三角形全等推角等1; assumption.
    assert(exists X, Bet A X P /\ Bet M X D).
      eapply 帕施公理.
        apply 中间性的对称性.
        apply H0.
      apply midpoint_bet.
      apply M是AB中点则M是BA中点.
      assumption.
    ex_and H10 X.
    split.
      unfold 角度小于等于.
      exists P.
      split.
        assert(在角内 P M A D).
          repeat split.
            auto.
            auto.
            intro.
            subst P.
            unfold 等角 in H9.
            分离合取式.
            absurde.
          exists X.
          split.
            assumption.
          right.
          apply bet_out.
            intro.
            subst X.
            apply H.
            eapply (共线的传递性2 _ M).
              assumption.
              eapply (共线的传递性2 _ D).
                assumption.
                apply 等价共线BCA.
                apply 中间性蕴含共线1.
                assumption.
              apply 等价共线BCA.
              apply 中间性蕴含共线1.
              assumption.
            apply 中间性蕴含共线1.
            apply midpoint_bet.
            assumption.
          assumption.
        eapply l11_25.
          apply H12.
          apply l6_6.
          apply bet_out.
            auto.
            auto.
          apply midpoint_bet.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        unfold 等角 in H9.
        分离合取式.
        auto.
      assumption.
    intro.
    assert(等角 C A D C A P).
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H12.
      assumption.
    assert (共面 C A D P).
      统计不重合点.
      apply 等价共面ACDB, col_cop__cop with B; Col.
      exists M.
      right.
      left.
      split; Col.
    apply conga_cop__or_out_ts in H13; trivial.
    induction H13.
      apply H.
      assert(Col B A P).
        apply 等价共线CAB.
        apply (共线的传递性2 _ D).
          assumption.
          apply out_col.
          assumption.
        apply 等价共线BCA.
        apply 中间性蕴含共线1.
        assumption.
      assert(B <> P).
        intro.
        subst P.
        apply M是AA中点则M与A重合 in H2.
        subst M.
        apply H.
        apply 中间性蕴含共线1.
        apply midpoint_bet.
        assumption.
      assert(Col M B A).
        apply 等价共线CAB.
        apply (共线的传递性2 _ P).
          assumption.
          apply 等价共线ACB.
          assumption.
        apply 等价共线ACB.
        apply 中间性蕴含共线1.
        apply midpoint_bet.
        assumption.
      eapply 共线的传递性2.
        apply H8.
        apply 等价共线CAB.
        assumption.
      apply 中间性蕴含共线1.
      apply midpoint_bet.
      assumption.
    assert(TS A C B P).
      repeat split.
        intro.
        apply H.
        apply 等价共线BAC.
        assumption.
        intro.
        apply H.
        assert(Col M C P).
          apply 等价共线CAB.
          apply (共线的传递性2 _ A).
            auto.
            apply 等价共线CBA.
            assumption.
          apply 等价共线CAB.
          apply 中间性蕴含共线1.
          apply midpoint_bet.
          assumption.
        assert(Col M B C).
          apply (共线的传递性2 _ P).
            intro.
            subst M.
            apply M是AB中点则M是BA中点 in H2.
            apply A是AB中点则A与B重合 in H2.
            subst P.
            apply H.
            apply 等价共线BAC.
            assumption.
            apply 等价共线BCA.
            apply 中间性蕴含共线1.
            apply midpoint_bet.
            assumption.
          apply 等价共线ACB.
          assumption.
        apply 等价共线BCA.
        apply (共线的传递性2 _ M).
          intro.
          subst M.
          apply M是AB中点则M是BA中点 in H3.
          apply A是AB中点则A与B重合 in H3.
          subst C.
          absurde.
          apply 等价共线CBA.
          apply 中间性蕴含共线1.
          apply midpoint_bet.
          assumption.
        apply 等价共线CAB.
        assumption.
      exists M.
      split.
        apply 等价共线BAC.
        apply 中间性蕴含共线1.
        apply midpoint_bet.
        assumption.
      apply midpoint_bet.
      assumption.
    assert(TS A C B D).
      repeat split.
        intro.
        apply H.
        apply 等价共线BAC.
        assumption.
        intro.
        apply H.
        apply (共线的传递性2 _ D).
          assumption.
          apply 等价共线BCA.
          apply 中间性蕴含共线1.
          assumption.
        apply 等价共线BAC.
        assumption.
      exists A.
      split.
        apply AAB型共线.
      assumption.
    assert(OS A C D P).
      unfold OS.
      exists B.
      split.
        apply l9_2.
        assumption.
      apply l9_2.
      assumption.
    apply invert_two_sides in H13.
    apply l9_9 in H13.
    contradiction.
Qed.

(** This is exterior angle theorem *)

Lemma l11_41_三角形两内角小于另一外角 : forall A B C D,
  ~ Col A B C ->
  Bet B A D ->
  A <> D ->
  角度小于 A C B C A D /\ 角度小于 A B C C A D.
Proof.
    intros.
    split.
      apply l11_41_证明辅助定理.
        assumption.
        assumption.
      assumption.
    prolong C A E C A.
    assert(角度小于 A B C B A E).
      eapply l11_41_证明辅助定理.
        intro.
        apply H.
        apply 等价共线ACB.
        assumption.
        assumption.
        统计不重合点;auto.
    assert(等角 B A C C A B).
    {
      apply 等角的左交换性.
      apply 同角相等;
      统计不重合点;auto.
    }
    assert(等角 D A C E A B)
      by (eapply l11_13 with B C;统计不重合点;auto).
    unfold 角度小于 in *.
    分离合取式.
    repeat split.
      apply l11_30_等角保持小于等于 with A B C B A E; trivial.
        apply 同角相等;统计不重合点;auto.
      apply 等角的对称性.
      apply 等角的交换性.
      assumption.
    intro.
    apply H7.
    eapply 角等的传递性.
      apply H8.
    apply 等角的交换性.
    assumption.
Qed.

Lemma 等角保持不等角性质 : forall A B C A' B' C' D E F ,
 等角 A B C A' B' C' ->
 ~ 等角 A B C D E F ->
 ~ 等角 A' B' C' D E F.
Proof.
    intros.
    intro.
    apply H0.
    eapply 角等的传递性.
      apply H.
    assumption.
Qed.

Lemma 不等角的对称性 : forall A B C D E F,
 ~ 等角 A B C D E F ->
 ~ 等角 D E F A B C.
Proof.
    intros.
    intro.
    apply H.
    apply 等角的对称性.
    assumption.
Qed.

Lemma 两角度不可能互相小于对方 : forall A B C D E F, ~ (角度小于 A B C D E F /\ 角度小于 D E F A B C).
Proof.
    intros.
    intro.
    unfold 角度小于 in *.
    分离合取式.
    assert(等角 A B C D E F).
      apply 双角度偏序推等角.
        assumption.
      assumption.
    contradiction.
Qed.

Lemma 等角保持角度小于性质 : forall A B C D E F A' B' C' D' E' F',
 等角 A B C A' B' C' ->
 等角 D E F D' E' F' ->
 角度小于 A B C D E F ->
 角度小于 A' B' C' D' E' F'.
Proof.
    intros.
    unfold 角度小于 in *.
    分离合取式.
    split.
      eapply l11_30_等角保持小于等于.
        apply H1.
        assumption.
      assumption.
    intro.
    apply H2.
    eapply 角等的传递性.
      apply H.
    eapply 角等的传递性.
      apply H3.
    apply 等角的对称性.
    assumption.
Qed.

Lemma 角度小于的传递性 : forall A B C A1 B1 C1 A2 B2 C2,
 角度小于 A B C A1 B1 C1 ->
 角度小于 A1 B1 C1 A2 B2 C2 ->
 角度小于 A B C A2 B2 C2.
Proof.
    intros.
    assert(HH1:= H).
    assert(HH2:= H0).
    unfold 角度小于 in H.
    unfold 角度小于 in H0.
    分离合取式.
    assert(角度小于等于 A B C A2 B2 C2).
      eapply 角度小于等于的传递性.
        apply H.
      assumption.
    split.
      assumption.
    intro.
    assert(角度小于 A2 B2 C2 A1 B1 C1).
      eapply 等角保持角度小于性质.
        apply H4.
        apply 同角相等.
          unfold 角度小于等于 in H0.
          ex_and H0 X.
          unfold 等角 in H5.
          分离合取式.
          assumption.
        unfold 角度小于等于 in H0.
        ex_and H0 X.
        unfold 等角 in H5.
        分离合取式.
        assumption.
      assumption.
    apply (两角度不可能互相小于对方 A1 B1 C1 A2 B2 C2).
    split; assumption.
Qed.

Lemma 为钝角的对称性 : forall A B C, 为钝角 A B C -> 为钝角 C B A.
Proof.
    unfold 为钝角.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    apply 角度小于的右交换性.
    assumption.
Qed.

Lemma 为锐角的对称性 : forall A B C, 为锐角 A B C -> 为锐角 C B A.
Proof.
    unfold 为锐角.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split;auto using 角度小于的左交换性.
Qed.

Lemma 共线锐角推外共线 : forall A B C, Col A B C -> 为锐角 A B C -> Out B A C.
Proof.
    intros.
    destruct H0 as [X [Y [Z []]]].
    apply 共线三点构成的角大于等于任何角则该三点构成外共线 with X Y Z; assumption.
Qed.

Lemma 共线钝角推中间性 : forall A B C, Col A B C -> 为钝角 A B C -> Bet A B C.
Proof.
    intros.
    destruct H0 as [X [Y [Z []]]].
    apply (共线三点构成的角大于等于任何角则该三点构成中间性 X Y Z); assumption.
Qed.

Lemma 外共线零角为锐角 : forall A B C, Out B A C -> 为锐角 A B C.
Proof.
  intros A B C Hout.
  统计不重合点.
  assert(HD := 垂点的存在性 B A B).
  destruct HD as [D]; auto.
  统计不重合点.
  exists A.
  exists B.
  exists D.
  split; Perp.
  split.
  apply l11_31_1_任何角小于等于平角_Out表述; auto.
  intro.
  assert(HNCol : ~ Col A B D) by (apply 成直角三点不共线; Perp).
  apply HNCol.
  apply 等价共线BAC.
  apply out_col.
  apply (l11_21_a A B C); auto.
Qed.

Lemma 中间性平角为钝角 : forall A B C, Bet A B C -> A <> B -> B <> C -> 为钝角 A B C.
Proof.
  intros A B C HBet HAB HBC.
  assert(HD := 垂点的存在性 B A B).
  destruct HD as [D]; auto.
  统计不重合点.
  exists A.
  exists B.
  exists D.
  split; Perp.
  split.
  apply l11_31_1_任何角小于等于平角_Bet表述; auto.
  intro.
  assert(HNCol : ~ Col A B D) by (apply 成直角三点不共线; Perp).
  apply HNCol.
  apply 中间性蕴含共线1.
  apply (零角的等角是零角 A B C); try (apply 等角的对称性); auto.
Qed.

Lemma l11_43_证明辅助定理 : forall A B C, A <> B -> A <> C -> (Per B A C \/ 为钝角 B A C) -> 为锐角 A B C.
Proof.
    intros.
    induction (共线的决定性 A B C).
      induction H1.
        exfalso.
        apply (成直角三点不共线 B A C); Col.
      apply 外共线零角为锐角, bet_out; auto.
      apply 共线钝角推中间性; Col.
    统计不重合点.
    prolong B A B' B A.
    assert(~ Col B' A C).
      intro.
      apply H2.
      eapply (共线的传递性2 _ B').
        intro.
        subst B'.
        apply 等长的对称性 in H4.
        apply 等长的同一性 in H4.
        subst A.
        apply H2.
        apply AAB型共线.
        apply 等价共线BCA.
        apply 中间性蕴含共线1.
        assumption.
      apply 等价共线BAC.
      assumption.
    apply 不共线则不重合 in H6.
    分离合取式.
    assert(角度小于 A C B C A B'/\ 角度小于 A B C C A B').
      apply l11_41_三角形两内角小于另一外角.
        assumption.
        assumption.
      auto.
    分离合取式.
    induction H1.
      unfold 为锐角.
      exists C.
      exists A.
      exists B.
      split.
        apply 直角的对称性.
        assumption.
      分离合取式.
      unfold 角度小于.
      unfold 角度小于 in H11.
      分离合取式.
      assert(Per B' A C).
        apply 直角的对称性.
        eapply (直角边共线点也构成直角2 _ _ B).
          assumption.
          apply 直角的对称性.
          assumption.
        apply 等价共线BAC.
        apply 中间性蕴含共线1.
        assumption.
      assert(等角 B A C B' A C).
        apply l11_16_直角相等.
          assumption.
          auto.
          auto.
          assumption.
          assumption.
        auto.
      split.
        eapply l11_30_等角保持小于等于.
          apply H11.
          apply 同角相等.
            assumption.
          auto.
        apply 等角的交换性.
        apply 等角的对称性.
        assumption.
      intro.
      apply H12.
      eapply 角等的传递性.
        apply H15.
      apply 等角的交换性.
      assumption.
    unfold 为锐角.
    unfold 为钝角 in H1.
    ex_and H1 a.
    ex_and H12 b.
    ex_and H1 c.
    assert(HH1:= H12).
    unfold 角度小于 in H12.
    分离合取式.
    unfold 角度小于等于 in H12.
    ex_and H12 P.
    exists B.
    exists A.
    exists P.
    assert(Per B A P).
      eapply l11_17_等于直角的角是直角.
        apply H1.
      assumption.
    split.
      assumption.
    assert(Per P A B').
      eapply 直角边共线点也构成直角2.
        apply H.
        apply 直角的对称性.
        assumption.
      apply 等价共线BAC.
      apply 中间性蕴含共线1.
      assumption.
    assert(等角 B A P B' A P).
      eapply l11_16_直角相等.
        assumption.
        auto.
        intro.
        subst P.
        unfold 等角 in H14.
        分离合取式.
        absurde.
        apply 直角的对称性.
        assumption.
        assumption.
      intro.
      subst P.
      unfold 等角 in H14.
      分离合取式.
      absurde.
    assert(角度小于 C A B' P A B).
      assert(B <> A).
        auto.
      assert(HH := l11_36_双补角组中的角度偏序 B A P B A C B' B' H18 H7 H18 H7 H3 H3).
      destruct HH.
      unfold 角度小于.
      split.
        eapply l11_30_等角保持小于等于.
          apply H19.
          unfold 角度小于 in HH1.
          分离合取式.
          eapply l11_30_等角保持小于等于.
            apply H21.
            assumption.
          apply 同角相等.
            auto.
          auto.
          apply 等角的左交换性.
          apply 同角相等.
            auto.
          assumption.
        apply 等角的右交换性.
        apply 等角的对称性.
        assumption.
      intro.
      apply H13.
      assert(Per B' A C).
        eapply l11_17_等于直角的角是直角.
          apply H15.
        apply 等角的交换性.
        apply 等角的对称性.
        assumption.
      assert(Per C A B).
        eapply (直角边共线点也构成直角2 _ _ B').
          auto.
          apply 直角的对称性.
          assumption.
        apply 等价共线BCA.
        apply 中间性蕴含共线1.
        assumption.
      apply l11_16_直角相等.
        assumption.
        unfold 等角 in H14.
        分离合取式.
        assumption.
        unfold 等角 in H14.
        分离合取式.
        assumption.
        apply 直角的对称性.
        assumption.
        auto.
      auto.
    eapply 角度小于的传递性.
      apply H11.
    apply 角度小于的右交换性.
    assumption.
Qed.

Lemma l11_43_非锐角三角形两小内角为锐角 : forall A B C, A <> B -> A <> C -> (Per B A C \/ 为钝角 B A C) -> 为锐角 A B C /\ 为锐角 A C B.
Proof.
    intros.
    split.
      apply l11_43_证明辅助定理;auto.
    apply l11_43_证明辅助定理;auto.
    induction H1.
      left;Perp.
    right;apply 为钝角的对称性;assumption.
Qed.

Lemma 小于等于锐角之角为锐角 : forall A B C D E F, 为锐角 D E F -> 角度小于等于 A B C D E F -> 为锐角 A B C.
Proof.
    intros.
    unfold 为锐角 in *.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A', B', C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold 角度小于 in H1.
    分离合取式.
    unfold 角度小于.
    split.
      eapply 角度小于等于的传递性.
        apply H0.
      assumption.
    intro.
    assert(角度小于 A' B' C' D E F).
      eapply 等角保持角度小于性质.
        apply H3.
        apply 同角相等.
          unfold 角度小于等于 in H0.
          ex_and H0 X.
          unfold 等角 in H4.
          分离合取式.
          assumption.
        apply 角度小于等于的交换性 in H0.
        unfold 角度小于等于 in H0.
        ex_and H0 X.
        unfold 等角 in H4.
        分离合取式.
        assumption.
      split.
        assumption.
      intro.
      apply H2.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H4.
      assumption.
    apply (两角度不可能互相小于对方 A' B' C' D E F).
    split; assumption.
Qed.

Lemma 一角小于等于钝角则该角为钝角 : forall A B C D E F, 为钝角 D E F -> 角度小于等于 D E F A B C -> 为钝角 A B C.
Proof.
    intros.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A', B', C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold 角度小于 in H1.
    分离合取式.
    split.
      eapply 角度小于等于的传递性.
        apply H1.
      assumption.
    intro.
    assert(角度小于 D E F A' B' C').
      eapply 等角保持角度小于性质.
        apply 同角相等.
          unfold 角度小于等于 in H0.
          ex_and H0 X.
          unfold 等角 in H4.
          分离合取式.
          assumption.
        apply 角度小于等于的交换性 in H0.
          unfold 角度小于等于 in H0.
          ex_and H0 X.
          unfold 等角 in H4.
          分离合取式.
          assumption.
      apply 等角的对称性.
      apply H3.
      split.
        assumption.
      intro.
      apply H2.
      eapply 角等的传递性.
        apply H3.
      apply 等角的对称性.
      assumption.
    apply (两角度不可能互相小于对方 A' B' C' D E F).
    split; assumption.
Qed.

(** In an 等腰三角形 triangle the two base angles are equal.
    This is Euclid: Book 1, Proposition 5.
 *)

Lemma l11_44_1_a_等腰三角形底角相等 : forall A B C, A <> B -> A <> C -> Cong B A B C -> 等角 B A C B C A.
Proof.
    intros.
    destruct (中点的存在性 A C) as [P HP].
    统计不重合点.
    assert(等角 B A P B C P) by (apply 三角形全等推角等1; auto; repeat split; Cong).
    apply l11_10 with B P B P; Out.
Qed.

(** This is Euclid: Book 1, Proposition 18 *)
(*
      B
     / \_
    /    \_
   /  L: < \_
  /#  A: >  #\
 A------------C
*)
Lemma l11_44_2_a_三角形长边对小角 : forall A B C, ~ Col A B C -> Lt B A B C -> 角度小于 B C A B A C.
Proof.
    intros.
    apply 不共线则不重合 in H.
    分离合取式.
    unfold Lt in H0.
    分离合取式.
    unfold Le in H0.
    ex_and H0 C'.
    assert(C <> C').
      intro.
      subst C'.
      contradiction.
    assert(C' <> A).
      intro.
      subst C'.
      apply H.
      apply 等价共线BAC.
      apply 中间性蕴含共线1.
      assumption.
    assert(C' <> B).
      intro.
      subst C'.
      apply 等长的同一性 in H5.
      subst A.
      absurde.
    assert(在角内 C' B A C).
      repeat split.
        auto.
        auto.
        assumption.
      exists C'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(HH:=l11_41_三角形两内角小于另一外角 C' C A B).
    assert(角度小于 C' A C A C' B /\ 角度小于 C' C A A C' B).
      apply HH.
        intro.
        apply H.
        apply 等价共线BCA.
        eapply 共线的传递性2.
          apply H6.
          apply 等价共线BAC.
          assumption.
        apply 等价共线CBA.
        apply 中间性蕴含共线1.
        assumption.
        apply 中间性的对称性.
        assumption.
      assumption.
    clear HH.
    分离合取式.
    assert(角度小于 B A C' B A C).
      split.
        unfold 角度小于等于.
        exists C'.
        split.
          assumption.
        apply 同角相等.
          auto.
        assumption.
      intro.
      apply conga_os__out in H12.
        apply H.
        apply out_col in H12.
        apply 中间性蕴含共线1 in H0.
        apply 等价共线BCA.
        eapply 共线的传递性2.
          apply H6.
          Col.
        Col.
        apply out_one_side.
          right.
          intro.
          apply H.
          Col.
        apply bet_out;auto.
    assert(角度小于 B C A A C' B).
      apply (等角保持角度小于性质 C' C A A C' B).
        apply out2__conga.
          apply l6_6.
          apply bet_out.
            auto.
          apply 中间性的对称性.
          assumption.
          apply out_trivial.
          auto.
      apply 同角相等; auto.
      assumption.
    assert(等角 B A C' B C' A).
      apply (l11_44_1_a_等腰三角形底角相等 A B C'); auto.
    apply 等角的右交换性 in H14.
    assert(角度小于 B C A B A C').
      apply (等角保持角度小于性质 B C A A C' B).
        apply 同角相等; auto.
        apply 等角的对称性.
        assumption.
      assumption.
    eapply 角度小于的传递性.
      apply H15.
    assumption.
Qed.
(* 无用 *)
Lemma 一角不可能既小于又等于另一角 : forall A B C D E F, ~ (角度小于 A B C D E F /\ 等角 A B C D E F).
Proof.
    intros.
    intro.
    分离合取式.
    unfold 角度小于 in H.
    分离合取式.
    contradiction.
Qed.
(* 无用 *)
Lemma 等角的对称等价性 : forall A B C A' B' C', 等角 A B C A' B' C' <-> 等角 A' B' C' A B C.
Proof.
    intros.
    split; apply 等角的对称性.
Qed.

Lemma 等角的决定性 :
  forall A B C D E F,
   等角 A B C D E F \/ ~ 等角 A B C D E F.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst;right;intro;unfold 等角 in *;intuition.
    induction (两点重合的决定性 C B).
      subst;right;intro;unfold 等角 in *;intuition.
    induction (两点重合的决定性 D E).
      subst;right;intro;unfold 等角 in *;intuition.
    induction (两点重合的决定性 F E).
      subst;right;intro;unfold 等角 in *;intuition.
    assert (exists A' : Tpoint, Bet B A A' /\ Cong A A' E D) by (apply 由一点往一方向构造等长线段).
    decompose [ex and] H3; clear H3.
    assert (exists C' : Tpoint, Bet B C C' /\ Cong C C' E F) by (apply 由一点往一方向构造等长线段).
    decompose [ex and] H3; clear H3.
    assert (exists D' : Tpoint, Bet E D D' /\ Cong D D' B A) by (apply 由一点往一方向构造等长线段).
    decompose [ex and] H3; clear H3.
    assert (exists F' : Tpoint, Bet E F F' /\ Cong F F' B C) by (apply 由一点往一方向构造等长线段).
    decompose [ex and] H3; clear H3.
    induction (等长的决定性 x x0 x1 x2).
      left.
      unfold 等角.
      repeat split; try assumption.
      exists x; exists x0; exists x1; exists x2.
      repeat split; assumption.
    right.
    unfold 等角.
    intro.
    decompose [and ex] H4; clear H4.
    assert (x3 = x) by (apply 点的唯一构造 with B A E D; auto).
    assert (x4 = x0) by (apply 点的唯一构造 with B C E F; auto).
    assert (x5 = x1) by (apply 点的唯一构造 with E D B A; auto).
    assert (x6 = x2) by (apply 点的唯一构造 with E F B C; auto).
    subst.
    contradiction.
Qed.

Lemma 一角小于另一角则两角不可能相等 : forall A B C D E F, 角度小于 A B C D E F -> ~ 等角 A B C D E F.
Proof.
    intros.
    intro.
    unfold 角度小于 in H.
    分离合取式.
    contradiction.
Qed.

Lemma 角度小于蕴含角度小于等于 : forall A B C D E F, 角度小于 A B C D E F -> 角度小于等于 A B C D E F.
Proof.
  intros.
  destruct H.
  assumption.
Qed.

Lemma 一角不可能小于自己 : forall A B C, ~ 角度小于 A B C A B C.
Proof.
  intros A B C.
  intro.
  apply (两角度不可能互相小于对方 A B C A B C).
  split; assumption.
Qed.

Lemma 两角成偏序关系则不可能成反全序关系 : forall A B C D E F, 角度小于等于 A B C D E F -> ~ 角度小于 D E F A B C.
Proof.
  intros.
  intro Hlta.
  destruct Hlta as [Hlea HNConga].
  apply HNConga.
  apply 双角度偏序推等角; assumption.
Qed.

Lemma 角度小于蕴含反向角度小于等于的否定 : forall A B C D E F, 角度小于 A B C D E F -> ~ 角度小于等于 D E F A B C.
Proof.
  intros A B C D E F Hlta.
  destruct Hlta as [Hlea HNConga].
  intro.
  apply HNConga.
  apply 双角度偏序推等角; assumption.
Qed.

(** If the base angles are equal, then the triangle is 等腰三角形 *)

Lemma l11_44_1_三角形底角相等等价于等腰_b_底角相等的三角形是等腰三角形 : forall A B C, ~ Col A B C -> 等角 B A C B C A -> Cong B A B C.
Proof.
    intros.
    apply 不共线则不重合 in H.
    分离合取式.
    assert(HH:= 两长度必大于小于或等于 B A B C).
    induction HH.
      apply l11_44_2_a_三角形长边对小角 in H4.
        apply 一角小于另一角则两角不可能相等 in H4.
          apply 等角的对称性 in H0.
          contradiction.
      assumption.
    induction H4.
      unfold Gt in H4.
      apply l11_44_2_a_三角形长边对小角 in H4.
        apply 一角小于另一角则两角不可能相等 in H4.
          contradiction.
      intro.
      apply H.
      apply 等价共线CBA.
      assumption.
    assumption.
Qed.

(** This is Euclid Book I, Proposition 19 *)
(*
      B
     / \_
    /    \_
   /  L: < \_
  /#  A: >  #\
 C------------A
*)
Lemma l11_44_2_b_三角形小角对长边 : forall A B C, 角度小于 B A C B C A -> Lt B C B A.
Proof.
    intros.
    induction (共线的决定性 A B C).
      assert (Hd := H).
      apply 角度小于推不重合 in Hd; 分离合取式; clean_reap_hyps.
      apply 共线三点构成的角大于等于任何角则该三点构成中间性 in H; Col; Le.
    apply 不共线则不重合 in H0.
    分离合取式.
    assert(HH:= 两长度必大于小于或等于 B A B C).
    induction HH.
      apply l11_44_2_a_三角形长边对小角 in H4.
        assert(HH:= 两角度不可能互相小于对方 B A C B C A).
        exfalso.
        apply HH.
        split; assumption.
      assumption.
    induction H4.
      unfold Gt in H4.
      assumption.
    apply l11_44_1_a_等腰三角形底角相等 in H4; auto.
    apply 一角小于另一角则两角不可能相等 in H; auto.
    contradiction.
Qed.

Lemma l11_44_1_三角形底角相等等价于等腰 : forall A B C, ~ Col A B C -> (等角 B A C B C A <-> Cong B A B C).
Proof.
    intros; 统计不重合点; split; intro; auto using l11_44_1_三角形底角相等等价于等腰_b_底角相等的三角形是等腰三角形, l11_44_1_a_等腰三角形底角相等.
Qed.

Lemma l11_44_2_三角形小角对长边 : forall A B C, ~ Col A B C -> (角度小于 B A C B C A <-> Lt B C B A).
Proof.
    intros; split; intro; auto using l11_44_2_b_三角形小角对长边, l11_44_2_a_三角形长边对小角 with col. 
Qed.

Lemma l11_44_2_三角形小角对长边_偏序版 : forall A B C, ~ Col A B C -> (角度小于等于 B A C B C A <-> Le B C B A).
Proof.
    intros; split; intro.
      apply 不小于推出反向小于等于.
      intro.
      apply (两角成偏序关系则不可能成反全序关系 B A C B C A).
        assumption.
      apply l11_44_2_三角形小角对长边; Col.
    induction (等长的决定性 B C B A).
      apply 等角小于等于自己.
      apply l11_44_1_三角形底角相等等价于等腰; Cong.
    apply 角度小于蕴含角度小于等于.
    apply l11_44_2_三角形小角对长边.
      assumption.
    split; assumption.
Qed.

Lemma l11_46_非锐角三角形中大角对边最长 : forall A B C, A <> B -> B <> C -> (Per A B C \/ 为钝角 A B C) -> Lt B A A C /\ Lt B C A C.
Proof.
    intros.
    induction (共线的决定性 A B C).
      induction H1.
        exfalso.
        apply (成直角三点不共线 A B C); auto.
      apply 共线钝角推中间性 in H1; auto.
      repeat split; Le.
        intro.
        apply H0, between_cong with A; Cong.
      intro.
      apply H, eq_sym, between_cong with C; Between; Cong.
    统计不重合点.
    assert(HH:= H1).
    apply l11_43_非锐角三角形两小内角为锐角 in H1; auto.
      分离合取式.
      split.
        apply 长度小于的左交换性.
        apply l11_44_2_b_三角形小角对长边.
        unfold 为锐角 in H3.
        ex_and H3 A'.
        ex_and H4 B'.
        ex_and H3 C'.
        assert (Hd := H4).
        apply 角度小于推不重合 in Hd.
        分离合取式.
        induction HH.
         {
            eapply 等角保持角度小于性质 with A C B A' B' C'.
              apply 同角相等;auto.
              apply l11_16_直角相等;auto.
          apply 角度小于的左交换性.
          assumption.
         }
        unfold 为钝角 in H11.
        ex_and H11 A''.
        ex_and H12 B''.
        ex_and H11 C''.
        eapply 角度小于的传递性.
          apply 角度小于的左交换性.
          apply H4.
        eapply 等角保持角度小于性质 with A'' B'' C'' A B C.
          assert (Hd := H12).
          apply 角度小于推不重合 in Hd.
          分离合取式.
          apply l11_16_直角相等; auto.
          apply 同角相等; auto.
        assumption.
      apply 长度小于的左交换性.
      apply 长度小于的右交换性.
      apply l11_44_2_b_三角形小角对长边.
      unfold 为锐角 in H1.
      ex_and H1 A'.
      ex_and H4 B'.
      ex_and H1 C'.
      assert (Hd := H4).
      apply 角度小于推不重合 in Hd.
      分离合取式.
      induction HH.
        eapply 等角保持角度小于性质.
          apply 同角相等; auto.
          apply l11_16_直角相等.
            apply H1.
            auto.
            auto.
            apply 直角的对称性.
            assumption.
            auto.
          auto.
        apply 角度小于的左交换性.
        assumption.
      unfold 为钝角 in H11.
      ex_and H11 A''.
      ex_and H12 B''.
      ex_and H11 C''.
      eapply 角度小于的传递性.
        apply 角度小于的左交换性.
        apply H4.
      eapply 等角保持角度小于性质.
        apply 角度小于推不重合 in H12.
        分离合取式.
        apply (l11_16_直角相等 A'' B'' C''); auto.
        apply 同角相等; auto.
      apply 角度小于的右交换性.
      assumption.
Qed.

Lemma l11_47 : forall A B C H , Per A C B -> 垂直于 H C H A B ->
 Bet A H B /\ A <> H /\ B <> H.
Proof.
    intros.
    assert(HH1:= H1).
    unfold 垂直于 in H1.
    分离合取式.
    assert(Per C H A).
      apply H5.
        apply AAB型共线.
      apply AAB型共线.
    assert(Perp C H A B).
      eapply l8_14_2_1a_垂直于转垂直.
      apply HH1.
    induction (共线的决定性 A C B).
      assert(A <> H).
        intro.
        subst H.
        apply H1.
        apply sym_equal.
        eapply 直角边共线点也构成直角2_eq.
          apply H0.
          assumption.
        intro.
        subst B.
        assert(垂直于 C C A A C).
          apply L形垂直转垂直于.
          assumption.
        apply H2.
        eapply l8_14_3_垂点的唯一性.
          apply HH1.
        assumption.
      apply False_ind.
      apply H9.
      eapply 直角边共线点也构成直角2_eq.
        apply 直角的对称性.
        apply H6.
        apply (共线的传递性2 _ B); Col.
      auto.
    apply 不共线则不重合 in H8.
    分离合取式.
    assert(A <> H).
      intro.
      subst A.
      assert(Per C H B).
        apply L形垂直于转直角.
        assumption.
      apply H1.
      eapply ABC和ACB均直角则B与C重合.
        apply 直角的对称性.
        apply H0.
      apply 直角的对称性.
      assumption.
    assert(Per C H B).
      apply 直角边共线点也构成直角2 with A; auto.
    assert(H <> B).
      intro.
      subst B.
      apply H10.
      eapply ABC和ACB均直角则B与C重合.
        apply H0.
      apply 直角的对称性.
      assumption.
    assert(Lt H A A C /\ Lt H C A C).
      apply l11_46_非锐角三角形中大角对边最长; auto.
      left.
      apply 直角的对称性.
      assumption.
    assert(Lt C A A B /\ Lt C B A B).
      apply l11_46_非锐角三角形中大角对边最长; auto.
    assert(Lt H B B C /\ Lt H C B C).
      apply l11_46_非锐角三角形中大角对边最长; auto.
      left.
      Perp.
    split.
      unfold Lt in *.
      分离合取式.
      apply l5_12_b.
        Col.
        eapply 长度小于等于的传递性.
          apply 长度小于等于的左交换性.
          apply H15.
        apply 长度小于等于的左交换性.
        assumption.
      eapply 长度小于等于的传递性.
        apply H17.
      apply 长度小于等于的左交换性.
      assumption.
    split;auto.
Qed.


(** This is SAS congruence. *)

Lemma l11_49 : forall A B C A' B' C',
 等角 A B C A' B' C' -> Cong B A B' A' -> Cong B C B' C' ->
 Cong A C A' C' /\ (A <> C -> 等角 B A C B' A' C' /\ 等角 B C A B' C' A').
Proof.
    intros.
    assert(Cong A C A' C').
      eapply 等角两边等长则端点间距相等.
        apply H.
        apply 等长的交换性.
        assumption.
      assumption.
    split.
      assumption.
    intro.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold 等角 in H.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    split.
      apply l11_3_bis.
      exists B.
      exists C.
      exists B'.
      exists C'.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        intro.
        subst C'.
        apply 等长的同一性 in H2.
        contradiction.
      repeat split; assumption.
    apply l11_3_bis.
    exists B, A, B', A'.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      intro.
      subst C'.
      apply 等长的同一性 in H2.
      contradiction.
    repeat split.
      assumption.
      assumption.
    apply 等长的交换性.
    assumption.
Qed.

(** This is ASA congruence. *)

Lemma l11_50_1  : forall A B C A' B' C',
  ~ Col A B C -> 等角 B A C B' A' C' -> 等角 A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ 等角 A C B A' C' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B') by (unfold 等角 in *;intuition).
    分离合取式.
    assert(exists C'', Out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence;auto.
    ex_and H7 C''.
    assert(B' <> C'') by (unfold Out in *;intuition).
    assert(~ Col A' B' C') by (eapply 不共线三点构成的角的等角三点也不共线;eauto).
    assert(~ Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply 等价共线CAB.
      eapply (共线的传递性2 _ C'').
        assumption.
        assumption.
      apply 等价共线BCA.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    分离合取式.
    assert(Cong A C A' C'').
      apply H16.
      assert (C''<> B') by auto.
      repeat split;try assumption.
        left.
        apply ABB中间性.
        left.
        apply ABB中间性.
        left.
        apply ABB中间性.
        auto.
        unfold Out in  H7.
        分离合取式.
        assumption.
        apply 等长的交换性.
        assumption.
      apply 等长的对称性.
      assumption.
    assert(三角形全等 B A C B' A' C'').
      repeat split.
        apply 等长的交换性.
        assumption.
        apply 等长的对称性.
        assumption.
      assumption.
    assert(等角 B A C B' A' C'').
      apply 三角形全等推角等1.
        auto.
        apply 不共线则不重合 in H.
        分离合取式.
        auto.
      assumption.
    assert(等角 B' A' C' B' A' C'').
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H0.
      assumption.
    assert(C' = C'').
      apply conga_os__out in H20.
        eapply l6_21_两线交点的唯一性.
          apply 共线否定排列ACB.
          apply H10.
          apply H9.
          apply ABB型共线.
          apply out_col.
          assumption.
          apply out_col in H7.
          assumption.
          apply ABB型共线.
        apply out_one_side.
          left.
          intro.
          apply H10.
          apply 等价共线BAC.
          assumption.
        apply l6_6.
        assumption.
    subst C''.
    clear H20.
    split.
      assumption.
    split.
      eapply 等角两边等长则端点间距相等.
        apply H19.
        apply 等长的交换性.
        assumption.
      assumption.
    apply 三角形全等推角等1.
      apply 不共线则不重合 in H.
      分离合取式.
      assumption.
      auto.
    unfold 三角形全等.
    repeat split.
      assumption.
      assumption.
    apply 等长的对称性.
    apply 等长的交换性.
    assumption.
Qed.

(** This is AAS congruence. *)

Lemma l11_50_2  : forall A B C A' B' C',
  ~ Col A B C -> 等角 B C A B' C' A' -> 等角 A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ 等角 C A B C' A' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold 等角 in H1.
      分离合取式.
      repeat split; assumption.
    分离合取式.
    assert(exists C'',  Out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence.
        assumption.
      auto.
    ex_and H7 C''.
    assert(B' <> C'').
      unfold Out in H7.
      分离合取式.
      auto.
    assert(~Col A' B' C').
      eapply 不共线三点构成的角的等角三点也不共线.
        apply H.
      assumption.
    assert(~Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply 等价共线CAB.
      eapply (共线的传递性2 _ C'').
        assumption.
        assumption.
      apply 等价共线BCA.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    分离合取式.
    assert(Cong A C A' C'').
      apply H16.
      repeat (split; [Out|]); Cong.
    assert(三角形全等 B C A B' C'' A').
      repeat split; Cong.
    assert(等角 B C A B' C'' A').
      apply 三角形全等推角等1.
        auto.
        apply 不共线则不重合 in H.
        分离合取式.
        auto.
      assumption.
    assert(等角 B' C' A' B' C'' A').
      eapply 角等的传递性.
        apply 等角的对称性.
        apply H0.
      assumption.
    apply 不共线则不重合 in H.
    apply 不共线则不重合 in H10.
    分离合取式.
    clear H16.
    induction(两点重合的决定性 C' C'').
      induction (两点重合的决定性 C' C'').
        subst C''.
        split.
          assumption.
        split.
          apply 等长的对称性.
          assumption.
        assert(三角形全等 C A B C' A' B').
          repeat split.
            apply 等长的交换性.
            assumption.
            apply 等长的交换性.
            apply 等长的对称性.
            assumption.
          assumption.
        apply 三角形全等推角等1.
          auto.
          auto.
        assumption.
      apply False_ind.
      apply H27.
      assumption.
    assert(~ Col C'' C' A').
      intro.
      apply H10.
      apply 等价共线BCA.
      eapply 共线的传递性2.
        apply H16.
        apply 等价共线BAC.
        assumption.
      apply 等价共线CBA.
      apply out_col.
      assumption.
    apply 不共线则不重合 in H27.
    分离合取式.
    unfold Out in H7.
    分离合取式.
    induction H32.
      assert(HH:=l11_41_三角形两内角小于另一外角).
      assert(HH1:=l11_41_三角形两内角小于另一外角 C'' C' A' B' H27 (中间性的对称性 _ _ _ H32) H7).
      分离合取式.
      assert(等角 B' C' A' C'' C' A').
        eapply (l11_10 B' C' A' B' C' A').
          apply 同角相等.
            auto.
          assumption.
          apply out_trivial.
          assumption.
          apply out_trivial.
          auto.
          apply bet_out.
            auto.
          apply  中间性的对称性.
          assumption.
        apply out_trivial.
        auto.
      assert(角度小于 B' C' A' A' C'' B').
        eapply 等角保持角度小于性质.
          apply 等角的对称性.
          apply H35.
          apply 同角相等.
            auto.
          auto.
        assumption.
      unfold 角度小于 in H36.
      分离合取式.
      apply 等角的右交换性 in H20.
      contradiction.
    assert(~Col C' C'' A').
      intro.
      apply H27.
      apply 等价共线BAC.
      assumption.
    assert(HH1:=l11_41_三角形两内角小于另一外角 C' C'' A' B' H33 (中间性的对称性 _ _ _ H32) H15).
    分离合取式.
    assert(等角 B' C'' A' C' C'' A').
      apply out2__conga.
        apply bet_out.
          auto.
        apply 中间性的对称性.
        assumption.
      apply out_trivial.
      auto.
    assert(角度小于 B' C'' A' A' C' B').
      eapply 等角保持角度小于性质.
        apply 等角的对称性.
        apply H36.
        apply 同角相等.
          auto.
        auto.
      assumption.
    unfold 角度小于 in H37.
    分离合取式.
    apply 等角的对称性 in H20.
    apply 等角的右交换性 in H20.
    contradiction.
Qed.

(** This is SSS congruence. *)

Lemma l11_51 : forall A B C A' B' C',
  A <> B -> A <> C -> B <> C -> Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C' ->
  等角 B A C B' A' C' /\ 等角 A B C A' B' C' /\ 等角 B C A B' C' A'.
Proof.
    intros.
    assert(三角形全等 B A C B' A' C' /\ 三角形全等 A B C A' B' C' /\ 三角形全等 B C A B' C' A').
      repeat split; Cong.
    分离合取式.
    split; [|split]; apply 三角形全等推角等1; auto.
Qed.

Lemma conga_distinct : forall A B C D E F, 等角 A B C D E F -> 等角 A B C D E F /\ A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
    intros.
    split.
      assumption.
    unfold 等角 in H.
    分离合取式.
    repeat split; assumption.
Qed.

(** This is SSA congruence with a restriction *)

Lemma l11_52 : forall A B C A' B' C',
  等角 A B C A' B' C' -> Cong A C A' C' -> Cong B C B' C' -> Le B C A C ->
  Cong B A B' A' /\ 等角 B A C B' A' C' /\ 等角 B C A B' C' A'.
Proof.
    intros.
    apply conga_distinct in H.
    分离合取式.
    assert(Cong B A B' A').
      induction(共线的决定性 A B C).
        unfold Col in H7.
        induction H7.
          assert(Bet A' B' C').
            eapply 零角的等角是零角.
              apply H7.
            assumption.
          apply 等长的交换性.
          eapply l4_3.
            apply H7.
            apply H8.
            assumption.
          assumption.
        induction H7.
          assert(Out B' A' C').
            eapply l11_21_a.
              apply bet_out.
                apply H4.
              apply H7.
            apply 等角的左交换性.
            assumption.
          unfold Out in H8.
          分离合取式.
          induction H10.
            assert(Le B' C' A' C').
              eapply l5_6_等长保持小于等于关系.
              repeat split.
                apply H2.
                assumption.
              assumption.
            assert(B'=A').
              eapply bet_le_eq.
                apply H10.
              assumption.
            subst B'.
            absurde.
          eapply 两组连续三点分段等则全体等.
            apply H7.
            apply H10.
            assumption.
          Cong.
        assert(B = A).
          eapply bet_le_eq.
            apply 中间性的对称性.
            apply H7.
          assumption.
        subst B.
        absurde.
      assert(exists A'', Out B' A'' A' /\ Cong B' A'' B A).
        apply l6_11_existence.
          assumption.
        auto.
      ex_and H8 A''.
      assert(等角 A' B' C' A'' B' C').
        apply out2__conga.
          assumption.
          apply out_trivial.
          auto.
      assert(等角 A B C A'' B' C').
        eapply l11_10.
          apply H.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A'' C' A C).
        eapply 等角两边等长则端点间距相等.
          apply 等角的对称性.
          apply H11.
          Cong.
        Cong.
      assert(三角形全等 A'' B' C' A B C).
        repeat split; Cong.
      assert(Cong A'' C' A' C').
        eapply 等长的传递性.
          apply H12.
        assumption.
      assert(~Col A' B' C').
        eapply 不共线三点构成的角的等角三点也不共线.
          apply H7.
        assumption.
      assert(~Col A'' B' C').
        intro.
        apply H15.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ A'').
          intro.
          subst A''.
          unfold Out in H8.
          分离合取式.
          absurde.
          Col.
        Col.
      induction(两点重合的决定性 A'' A').
        subst A''.
        unfold 三角形全等 in H13.
        分离合取式.
        Cong.
      unfold Out in H8.
      分离合取式.
      induction H19.
        assert(HH:= l11_41_三角形两内角小于另一外角 A'' B' C' A' H16 H19 H17).
        分离合取式.
        assert(Cong A' C' A'' C').
          apply (等长的传递性 _ _ A C).
            Cong.
          unfold 三角形全等 in H13.
          分离合取式.
          Cong.
        assert(~ Col A'' C' A').
          intro.
          apply H15.
          apply (共线的传递性2 _ A''); Col.
        assert (HH:= l11_44_1_三角形底角相等等价于等腰 A'' C' A' H23).
        destruct HH.
        apply 等长的交换性 in H22.
        apply 等长的对称性 in H22.
        apply H25 in H22.
        assert(~ Col B' C' A'').
          Col.
        assert(等角 B' A' C' A'' A' C').
          apply out2__conga.
            apply bet_out; Between.
            apply out_trivial.
            intro.
            subst C'.
            apply H15.
            apply ABA型共线.
        assert(~Col B' C' A').
          Col.
        assert(HH:=l11_44_2_三角形小角对长边 B' C' A' H28).
        destruct HH.
        assert(Lt C' A'  C' B').
          apply H29.
          apply (等角保持角度小于性质 A'' B' C' C' A'' A').
            apply 等角的右交换性.
            apply 等角的对称性.
            apply H10.
            eapply 角等的传递性.
              apply H22.
            apply 等角的交换性.
            apply 等角的对称性.
            assumption.
          assumption.
        assert(Lt C' A'' C' B').
          unfold Lt in H31.
          分离合取式.
          unfold Lt.
          split.
            eapply l5_6_等长保持小于等于关系.
              apply H31.
              Cong.
            Cong.
          intro.
          apply H32.
          eapply 等长的传递性.
            apply 等长的交换性.
            apply 等长的对称性.
            apply H14.
          assumption.
        unfold Lt in H32.
        分离合取式.
        assert(Le C A C B).
          eapply l5_6_等长保持小于等于关系.
          repeat split.
            apply H32.
            apply 等长的交换性.
            assumption.
          Cong.
        assert(Cong C A C B).
          apply 长度小于等于的反对称性.
            assumption.
          apply 长度小于等于的交换性.
          assumption.
        apply False_ind.
        apply H33.
        apply 等长的对称性.
        eapply 等长的传递性.
          apply 等长的交换性.
          apply 等长的对称性.
          apply H1.
        eapply 等长的传递性.
          apply 等长的对称性.
          apply H35.
        Cong.
      assert(A' <> A'').
        auto.
      assert(HH:= l11_41_三角形两内角小于另一外角 A' B' C' A'' H15 H19 H20).
      分离合取式.
      assert(Cong A' C' A'' C').
        apply (等长的传递性 _ _ A C).
          Cong.
        unfold 三角形全等 in H13.
        分离合取式.
        Cong.
      assert(~ Col A'' C' A').
        intro.
        apply H15.
        eapply (共线的传递性2 _ A'' ); Col.
      assert (HH:= l11_44_1_三角形底角相等等价于等腰 A'' C' A' H24 ).
      destruct HH.
      apply 等长的交换性 in H23.
      apply 等长的对称性 in H23.
      apply H26 in H23.
      assert(~Col B' C' A'').
        Col.
      assert(等角 B' A'' C' A' A'' C').
        apply out2__conga.
          apply bet_out; Between.
          apply out_trivial.
          intro.
          subst C'.
          apply H16.
          apply ABA型共线.
      assert(~Col B' C' A'').
        Col.
      assert(HH:=l11_44_2_三角形小角对长边 B' C' A'' H29).
      destruct HH.
      assert(Lt C' A''  C' B').
        apply H30.
        apply (等角保持角度小于性质 A' B' C' C' A' A'').
          apply 等角的右交换性.
          apply 等角的对称性.
          apply 等角的对称性.
          apply H10.
          eapply 角等的传递性.
            apply 等角的对称性.
            apply H23.
          apply 等角的交换性.
          apply 等角的对称性.
          assumption.
        assumption.
      assert(Lt C' A' C' B').
        unfold Lt in H32.
        分离合取式.
        unfold Lt.
        split.
          eapply l5_6_等长保持小于等于关系.
            apply H32.
            Cong.
          Cong.
        intro.
        apply H33.
        eapply 等长的传递性.
          apply 等长的交换性.
          apply H14.
        assumption.
      unfold Lt in H33.
      分离合取式.
      assert(Le C A C B).
        eapply l5_6_等长保持小于等于关系.
        repeat split.
          apply H32.
          apply 等长的交换性.
          assumption.
        Cong.
      assert(Cong C A C B).
        apply 长度小于等于的反对称性.
          assumption.
        apply 长度小于等于的交换性.
        assumption.
      apply False_ind.
      apply H34.
      apply 等长的对称性.
      eapply 等长的传递性.
        apply 等长的交换性.
        apply 等长的对称性.
        apply H1.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H36.
      Cong.
    assert(三角形全等 A B C A' B' C').
      repeat split; Cong.
    split.
      assumption.
    split.
      apply 三角形全等推角等1.
        auto.
        intro.
        subst C.
        apply AB小于等于CC推出A与B重合 in H2.
        subst B.
        absurde.
      auto with cong3.
    apply 三角形全等推角等1.
      auto.
      intro.
      subst C.
      apply AB小于等于CC推出A与B重合 in H2.
      subst B.
      absurde.
    auto with cong3.
Qed.

Lemma l11_53 : forall A B C D,
 Per D C B -> C <> D -> A <> B -> B <> C -> Bet A B C ->
 角度小于 C A D C B D /\ Lt B D A D.
Proof.
    intros.
    assert(A<>C) by (intro; treat_equalities; auto).
    分离合取式.
    assert(~ Col B A D).
      intro.
      assert(Col B C D).
        apply (共线的传递性2 _ A); Col.
      assert(~Col B C D).
        apply 成直角三点不共线.
          auto.
          auto.
        apply 直角的对称性.
        assumption.
      contradiction.
    assert(A <> D).
      intro.
      subst D.
      apply H5.
      apply ABB型共线.
    assert(角度小于 C A D C B D).
      assert(HH:=l11_41_三角形两内角小于另一外角 B A D C H5 H3 H2).
      分离合取式.
      assert(等角 C A D B A D).
        apply out2__conga.
          apply bet_out.
            auto.
          assumption.
        apply out_trivial.
        auto.
      eapply 等角保持角度小于性质.
        apply 等角的对称性.
        apply H9.
        apply 等角的右交换性.
        apply 同角相等.
          intro.
          subst D.
          apply H5.
          apply ABA型共线.
        auto.
      assumption.
    split.
      assumption.
    unfold Per in H.
    ex_and H B'.
    unfold 中点 in H.
    分离合取式.
    assert(HH:= H8).
    assert(~Col B D B').
      intro.
      apply H5.
      apply (共线的传递性2 _ B').
        intro.
        subst B'.
        apply 中间性的同一律 in H.
        contradiction.
        apply (共线的传递性2 _ C).
          assumption.
          apply 中间性蕴含共线1.
          assumption.
        Col.
      Col.
    destruct(l11_44_1_三角形底角相等等价于等腰 B D B').
      assumption.
    apply H12 in H8.
    destruct(l11_44_2_三角形小角对长边 A D B').
      intro.
      apply H10.
      apply 等价共线BCA.
      apply (共线的传递性2 _ A).
        intro.
        subst B'.
        apply 中间性的对称性 in H3.
        assert(B = C).
          apply (双中间性推出点重合 _ _ A); assumption.
        contradiction.
        apply 等价共线BCA.
        eapply (共线的传递性2 _ C).
          assumption.
          Col.
        Col.
      Col.
    assert(角度小于 C A D C B' D).
      apply (等角保持角度小于性质 C A D C B D).
        apply 同角相等.
          auto.
        auto.
        apply 等角的对称性.
        apply l11_10 with B D B' D.
          apply 等角的对称性 in H8.
          apply 等角的交换性 in H8.
          apply H8.
          apply bet_out.
            intro.
            subst B'.
            apply 等长的同一性 in H9.
            contradiction.
          apply 中间性的对称性.
          assumption.
          apply out_trivial.
          intro.
          subst B'.
          apply H10.
          apply ABB型共线.
          apply bet_out; auto.
        apply out_trivial.
        intro.
        subst D.
        apply H10.
        apply AAB型共线.
      assumption.
    assert(B' <> A).
      intro.
      subst B'.
      apply 中间性的对称性 in H3.
      assert(B=C).
        eapply 双中间性推出点重合.
          apply H.
        assumption.
      contradiction.
    assert (Lt D B' D A).
      apply l11_44_2_b_三角形小角对长边.
      apply (等角保持角度小于性质 D A C D B' C).
        apply out2__conga.
          apply out_trivial.
          auto.
          apply l6_6.
          apply bet_out.
            auto.
          eapply 中间性的外传递性1.
            apply H3.
            assumption.
          auto.
        apply out2__conga.
          apply out_trivial.
          intro.
          subst B'.
          apply H10.
          apply ABB型共线.
          apply l6_6.
          apply bet_out.
            intro.
            subst B'.
            apply 等长的同一性 in H9.
            contradiction.
          eapply 中间性的外传递性2.
            apply 中间性的对称性.
            apply H.
            apply 中间性的对称性.
            assumption.
          auto.
      apply 角度小于的交换性.
      assumption.
    unfold Lt in H17.
    分离合取式.
    unfold Lt.
    split.
      eapply l5_6_等长保持小于等于关系.
        apply H17.
        Cong.
      apply 等长的伪自反性.
    intro.
    apply H18.
    eapply 等长的传递性.
      apply 等长的对称性.
      apply HH.
    apply 等长的交换性.
    assumption.
Qed.

(** This is SSA congruence with an obtuse angle *)

Lemma cong2_conga_obtuse__cong_conga2 :
forall A B C A' B' C',
       为钝角 A B C ->
       等角 A B C A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A' /\ 等角 B A C B' A' C' /\ 等角 B C A B' C' A'.
Proof.
intros.
apply (l11_52 A B C A' B' C'); auto.
destruct (共线的决定性 A B C).
  apply bet__le2313, 共线钝角推中间性; assumption.
统计不重合点; apply l11_46_非锐角三角形中大角对边最长; auto.
Qed.

(** This is SSA congruence with a right angle *)

Lemma cong2_per2__cong_conga2 :
forall A B C A' B' C',
       A<>B -> B<>C ->
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A' /\ 等角 B A C B' A' C' /\ 等角 B C A B' C' A'.
Proof.
intros.
统计不重合点.
destruct (l11_46_非锐角三角形中大角对边最长 A B C) as [_ []]; auto using 成直角三点不共线.
apply (l11_52 A B C A' B' C');auto.
apply l11_16_直角相等;auto.
intro.
subst B'.
apply H9, 等长的传递性 with A' C'; Cong.
Qed.

Lemma cong2_per2__cong :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A'.
Proof.
intros.
destruct (两点重合的决定性 B C).
  treat_equalities; Cong.
destruct (两点重合的决定性 A B).
  destruct (两点重合的决定性 A' B'); subst; [Cong|].
  统计不重合点.
  destruct (cong2_per2__cong_conga2 A' B' C' B B C); Cong; Perp.
apply cong2_per2__cong_conga2 with C C'; auto.
Qed.

Lemma cong2_per2__cong_3 :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       三角形全等 A B C A' B' C'.
Proof.
intros.
unfold 三角形全等.
assert (Cong B A B' A') by
 (apply (cong2_per2__cong A B C A' B' C');auto).
repeat split;Cong.
Qed.

Lemma cong_lt_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (两点重合的决定性 A B).
  treat_equalities; auto.
destruct (两点重合的决定性 B C).
  subst C.
  apply (等长保持小于关系 B' A' C' A'); Cong.
  统计不重合点.
  apply l11_46_非锐角三角形中大角对边最长; Perp.
destruct H2 as [[C0 []] HNCong].
统计不重合点.
assert (Per A' B' C0) by (apply 直角边共线点也构成直角2 with C'; Col).
apply (等长保持小于关系 A' C0 A' C'); [|apply l10_12 with B' B|]; Cong.
apply 长度小于的交换性.
destruct (l11_53 C' C0 B' A'); Between.
intro; subst; auto.
Qed.

Lemma cong_le_per2__le :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A B A' B' ->
       Le B C B' C' ->
       Le A C A' C'.
Proof.
intros.
destruct (等长的决定性 B C B' C').
  apply 等长则小于等于, l10_12 with B B'; assumption.
assert (Lt B C B' C') by (split; assumption).
apply 长度小于蕴含小于等于, cong_lt_per2__lt with B B'; assumption.
Qed.

Lemma lt2_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Lt A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (两点重合的决定性 B C).
  subst C.
  apply 长度小于的传递性 with A' B'; auto.
  统计不重合点.
  apply 长度小于的交换性, l11_46_非锐角三角形中大角对边最长; Perp.
apply 长度小于的交换性 in H1.
assert (HC0 := H2).
destruct HC0 as [[C0 []] HNCong].
assert (Per A' B' C0).
  统计不重合点; apply 直角边共线点也构成直角2 with C'; Col.
apply 长度小于的传递性 with A' C0.
  apply 长度小于的交换性, cong_lt_per2__lt with B B'; Cong; Perp.
apply cong_lt_per2__lt with B' B'; Cong.
apply (等长保持小于关系 B C B' C'); Cong.
Qed.

Lemma le_lt_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Le A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (等长的决定性 A B A' B').
  apply cong_lt_per2__lt with B B'; assumption.
assert (Lt A B A' B') by (split; assumption).
apply lt2_per2__lt with B B'; assumption.
Qed.

Lemma le2_per2__le :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Le A B A' B' ->
       Le B C B' C' ->
       Le A C A' C'.
Proof.
intros.
destruct (等长的决定性 B C B' C').
  apply 长度小于等于的交换性, cong_le_per2__le with B B'; Perp; Le; Cong.
assert (Lt B C B' C') by (split; assumption).
apply le_lt_per2__lt with B B'; assumption.
Qed.

Lemma cong_lt_per2__lt_1 :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Lt A B A' B' ->
       Cong A C A' C' ->
       Lt B' C' B C.
Proof.
intros.
apply 不小于等于推出反向小于.
intro.
destruct (le_lt_per2__lt C B A C' B' A'); Perp; Le; Cong.
Qed.

Lemma symmetry_preserves_conga :
 forall A B C A' B' C' M, A <> B -> C <> B ->
  中点 M A A' ->
  中点 M B B' ->
  中点 M C C' ->
  等角 A B C A' B' C'.
Proof.
  intros.
  assert(Cong A B A' B').
    apply (l7_13_同中点组两侧等长 M); 中点.
  assert(Cong B C B' C').
    apply (l7_13_同中点组两侧等长 M); 中点.
  assert(Cong A C A' C').
    apply (l7_13_同中点组两侧等长 M); 中点.
  apply 三角形全等推角等1; auto.
  repeat split; Cong.
Qed.

Lemma l11_57 : forall A B C A' B' C',
  OS A A' B B' -> Per B A A' -> Per B' A' A ->
  OS A A' C C' -> Per C A A' -> Per C' A' A ->
  等角 B A C B' A' C'.
Proof.
  intros A B C A' B' C' HOSB HPer1 HPer2 HOSC HPer3 HPer4.
  destruct (中点的存在性 A A') as [M HM].
  destruct (构造对称点 B M) as [B'' HB''].
  destruct (构造对称点 C M) as [C'' HC''].
  assert (HNColB := one_side_not_col123 A A' B B' HOSB).
  assert (HNColC := one_side_not_col123 A A' C C' HOSC).
  apply 角等的传递性 with B'' A' C''.
    统计不重合点; apply symmetry_preserves_conga with M; auto.
  assert (~ Col B'' A A').
    assert (B <> M) by (intro; subst; apply HNColB; Col); intro; apply HNColB; ColR.
  assert (Bet B'' A' B').
  { assert (Col B' B'' A').
    { 统计不重合点; apply (cop_per2__col A); auto.
        apply 等价共面ACDB, coplanar_trans_1 with B; [Col|Cop|].
        exists M; right; right; split; Col.
      apply midpoint_preserves_per with B A A' M; 中点.
    }
    apply col_two_sides_bet with A; Col.
    apply invert_two_sides, l9_2, l9_8_2 with B; trivial.
    repeat split; Col.
    exists M; split; [Col|Between].
  }
  assert (~ Col C'' A A').
    assert (C <> M) by (intro; subst; apply HNColC; Col); intro; apply HNColC; ColR.
  assert (Bet C'' A' C').
  { assert (Col C' C'' A').
    { 统计不重合点; apply (cop_per2__col A); auto.
        apply 等价共面ACDB, coplanar_trans_1 with C; [Col|Cop|].
        exists M; right; right; split; Col.
      apply midpoint_preserves_per with C A A' M; 中点.
    }
    apply col_two_sides_bet with A; Col.
    apply invert_two_sides, l9_2, l9_8_2 with C; trivial.
    repeat split; Col.
    exists M; split; [Col|Between].
  }
  apply one_side_not_col124 in HOSB.
  apply one_side_not_col124 in HOSC.
  统计不重合点; apply l11_14; auto.
Qed.

Lemma cop3_orth_at__orth_at : forall A B C D E F U V X, ~ Col D E F ->
  共面 A B C D -> 共面 A B C E -> 共面 A B C F -> 垂直平面于 X A B C U V ->
  垂直平面于 X D E F U V.
Proof.
  intros A B C D E F U V X HNCol HD HE HF [HNCol1 [HUV [HX1 [HX2 HX3]]]].
  repeat split; trivial.
    apply coplanar_pseudo_trans with A B C; assumption.
  assert (HCop : forall M, 共面 A B C M -> 共面 D E F M);
    [intro; apply coplanar_pseudo_trans; Cop|];
  assert (forall M, 共面 D E F M -> 共面 A B C M);
    [intro; apply coplanar_pseudo_trans; auto with cop 共面的排列|
  intros; apply HX3; auto].
Qed.

Lemma col2_orth_at__orth_at : forall A B C P Q U V X, U <> V ->
  Col P Q U -> Col P Q V -> 垂直平面于 X A B C P Q -> 垂直平面于 X A B C U V.
Proof.
  intros A B C P Q U V X HUV HU HV [HNCol [HPQ [HX1 [HX2 HX3]]]].
  repeat split; trivial.
    apply (共线的传递性4 P Q); auto.
  intros D W HD HW.
  apply HX3; [|apply (共线的传递性5 U V)]; assumption.
Qed.

Lemma col_orth_at__orth_at : forall A B C U V W X, U <> W ->
  Col U V W -> 垂直平面于 X A B C U V -> 垂直平面于 X A B C U W.
Proof.
  intros A B C U V W X HUW HCol HX.
  apply col2_orth_at__orth_at with U V; Col.
Qed.

Lemma orth_at_symmetry : forall A B C U V X,
  垂直平面于 X A B C U V -> 垂直平面于 X A B C V U.
Proof.
  unfold 垂直平面于.
  intros A B C U V X HX; 分离合取式.
  repeat split; Col.
Qed.

Lemma orth_at_distincts : forall A B C U V X, 垂直平面于 X A B C U V ->
  A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
  unfold 垂直平面于; intros; 分离合取式; 统计不重合点.
  repeat split; auto.
Qed.

Lemma orth_at_chara : forall A B C P X, 垂直平面于 X A B C X P <->
  ~ Col A B C /\ X <> P /\ 共面 A B C X /\ (forall D, 共面 A B C D -> Per D X P).
Proof.
  intros A B C P X; split.
  - unfold 垂直平面于; intro; 分离合取式.
    repeat split; Col.
  - intro; 分离合取式.
    repeat split; Col.
    intros; apply 直角边共线点也构成直角2 with P; auto.
Qed.

Lemma cop3_orth__orth : forall A B C D E F U V, ~ Col D E F ->
  共面 A B C D -> 共面 A B C E -> 共面 A B C F -> Orth A B C U V ->
  Orth D E F U V.
Proof.
  intros A B C D E F U V HNCol HD HE HF [X HX].
  exists X.
  apply (cop3_orth_at__orth_at A B C); assumption.
Qed.

Lemma col2_orth__orth : forall A B C P Q U V, U <> V ->
  Col P Q U -> Col P Q V -> Orth A B C P Q -> Orth A B C U V.
Proof.
  intros A B C P Q U V HUV HU HV [X HX].
  exists X.
  apply col2_orth_at__orth_at with P Q; assumption.
Qed.

Lemma col_orth__orth : forall A B C U V W, U <> W ->
  Col U V W -> Orth A B C U V -> Orth A B C U W.
Proof.
  intros A B C U V W HUW HCol HOrth.
  apply col2_orth__orth with U V; Col.
Qed.

Lemma orth_symmetry : forall A B C U V,
  Orth A B C U V -> Orth A B C V U.
Proof.
  intros A B C U V [X HX].
  exists X.
  apply orth_at_symmetry, HX.
Qed.

Lemma orth_distincts : forall A B C U V, Orth A B C U V ->
  A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
  intros A B C U V [X HX].
  apply orth_at_distincts with X, HX.
Qed.

Lemma col_cop_orth__orth_at : forall A B C U V X,
  Orth A B C U V -> 共面 A B C X -> Col U V X -> 垂直平面于 X A B C U V.
Proof.
  intros A B C U V X [Y [HNCol [HUV [HY1 [HY2 HY3]]]]] HX1 HX2.
  repeat split; trivial.
  replace X with Y; [assumption|].
  apply eq_sym, ABA直角则A与B重合; auto.
Qed.

Lemma l11_60_aux : forall A B C D P Q, ~ Col A B C ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q -> 共面 A B C D ->
  Cong D P D Q.
Proof.
  intros A B C D P Q HNCol HA HB HC HCop.
  destruct (中点的存在性 P Q) as [M []].
  统计不重合点; destruct HCop as [X [|[|]]]; 分离合取式.
  - apply l4_17 with C X; Col.
      intro; subst; apply HNCol; assumption.
    apply l4_17 with A B; auto.
  - apply l4_17 with B X; Col.
      intro; subst; apply HNCol; Col.
    apply l4_17 with A C; auto.
  - apply l4_17 with A X; Col.
      intro; subst; apply HNCol; Col.
    apply l4_17 with B C; auto.
Qed.

Lemma l11_60 : forall A B C D E P, ~ Col A B C ->
  Per A D P -> Per B D P -> Per C D P -> 共面 A B C E ->
  Per E D P.
Proof.
  intros A B C D E P HNCol HPerA HPerB HPerC HCop.
  destruct (两点重合的决定性 D P).
    subst; apply 角ABB成直角.
  destruct (构造对称点 P D) as [P'].
  exists P'; split; auto.
  apply (l11_60_aux A B C); [|apply 直角端点和其关于顶点的对称点与另一端点等距 with D..|]; assumption.
Qed.

Lemma l11_60_bis : forall A B C D P, ~ Col A B C -> D <> P ->
  共面 A B C D -> Per A D P -> Per B D P -> Per C D P ->
  垂直平面于 D A B C D P.
Proof.
  intros A B C D P HNCol HDP HD HA HB HC.
  repeat split; Col.
  intros E Q HE HQ.
  apply 直角边共线点也构成直角2 with P; auto.
  apply (l11_60 A B C); assumption.
Qed.

Lemma l11_61 : forall A B C A' B' C',
  A <> A' -> A <> B -> A <> C ->
  共面 A A' B B' -> Per B A A' -> Per B' A' A ->
  共面 A A' C C' -> Per C A A' ->
  Per B A C -> Per B' A' C'.
Proof.
  intros A B C A' B' C'; intros.
  assert (~ Col C A A') by (统计不重合点; apply 成直角三点不共线; auto).
  destruct (l10_15 A A' A' C) as [C'' []]; Col.
  统计不重合点.
  apply 直角的对称性, (l11_60 A' A C'');
    [apply one_side_not_col124 with C; Side|Perp..| |apply coplanar_trans_1 with C; Col; Cop].
  apply 直角的对称性.
  revert dependent B'.
  assert (Haux : forall B', OS A A' B B' -> Per B' A' A -> Per B' A' C'').
  { intros B' HOS HPer.
    apply (l11_17_等于直角的角是直角 B A C); trivial.
    apply l11_57; Perp.
  }
  intro B'; intros.
  destruct (两点重合的决定性 B' A'); [subst; Perp|].
  assert (HNCol : ~ Col B' A' A) by (apply 成直角三点不共线; auto).
  destruct (cop__one_or_two_sides A A' B B'); Col.
    apply 成直角三点不共线; auto.
  destruct (由一点往一方向构造等长线段 B' A' A' B') as [B'' []].
  统计不重合点.
  apply 直角的对称性, 直角边共线点也构成直角2 with B''; Col.
  apply 直角的对称性, Haux; [|apply 直角的对称性, 直角边共线点也构成直角2 with B'; Perp; Col].
  exists B'; split; trivial.
  repeat split; Col.
    intro; apply HNCol; ColR.
  exists A'; split; Col; Between.
Qed.

Lemma l11_61_bis : forall A B C D E P Q,
  垂直平面于 D A B C D P -> Perp D E E Q -> 共面 A B C E -> 共面 D E P Q ->
  垂直平面于 E A B C E Q.
Proof.
  intros A B C D E P Q [HNCol [HDP [HD [_ HOrth]]]] HPerp HE HCop.
  统计不重合点.
  repeat split; Col.
  assert (Haux : forall M, 共面 A B C M -> Per M E Q).
  { intros M HM.
    assert (HD' : exists D', Perp D E D' D /\ 共面 A B C D').
    { destruct (ex_ncol_cop A B C D E) as [F []]; auto.
      destruct (ex_perp_cop D E D F) as [D' []]; auto.
      exists D'; split; auto.
      apply coplanar_pseudo_trans with D E F; trivial;
      apply coplanar_pseudo_trans with A B C; Cop.
    }
    destruct HD' as [D' []].
    统计不重合点.
    apply 直角的对称性, (l11_61 D P D'); auto.
      apply 直角的对称性; Col.
      Perp.
      apply coplanar_pseudo_trans with A B C; assumption.
      Perp.
      apply 直角的对称性; Col.
  }
  intros; apply 直角边共线点也构成直角2 with Q; Cop.
Qed.

Lemma l11_62_unicity : forall A B C D D' P,
  共面 A B C D -> 共面 A B C D' ->
  (forall E, 共面 A B C E -> Per E D P) ->
  (forall E, 共面 A B C E -> Per E D' P) ->
  D = D'.
Proof.
  intros A B C D D' P HCop HCop' HD HD'.
  apply ABC和ACB均直角则B与C重合 with P; Perp.
Qed.

Lemma l11_62_unicity_bis : forall A B C U X Y,
  垂直平面于 X A B C X U -> 垂直平面于 Y A B C Y U -> X = Y.
Proof.
  unfold 垂直平面于.
  intros A B C U X Y HX HY.
  分离合取式.
  apply l11_62_unicity with A B C U; trivial; intros; Col.
Qed.

Lemma orth_at2__eq : forall A B C U V X Y,
  垂直平面于 X A B C U V -> 垂直平面于 Y A B C U V -> X = Y.
Proof.
  unfold 垂直平面于.
  intros A B C U V X Y HX HY.
  分离合取式.
  apply l11_62_unicity with A B C U; trivial; intros; Col.
Qed.

Lemma col_cop_orth_at__eq : forall A B C U V X Y,
  垂直平面于 X A B C U V -> 共面 A B C Y -> Col U V Y -> X = Y.
Proof.
  intros A B C U V X Y HOrth HCop HCol.
  apply (orth_at2__eq A B C U V); [assumption|].
  apply col_cop_orth__orth_at; [exists X|..]; assumption.
Qed.

Lemma orth_at__ncop1 : forall A B C U V X, U <> X ->
  垂直平面于 X A B C U V -> ~ 共面 A B C U.
Proof.
  intros A B C U V X HUX HOrth HCop.
  apply HUX, eq_sym, (col_cop_orth_at__eq A B C U V); Col.
Qed.

Lemma orth_at__ncop2 : forall A B C U V X, V <> X ->
  垂直平面于 X A B C U V -> ~ 共面 A B C V.
Proof.
  intros A B C U V X HUX HOrth.
  apply orth_at__ncop1 with U X; [assumption|apply orth_at_symmetry, HOrth].
Qed.

Lemma orth_at__ncop : forall A B C P X,
  垂直平面于 X A B C X P -> ~ 共面 A B C P.
Proof.
  intros A B C P X HOrth.
  assert (Hd := HOrth); apply orth_at_distincts in Hd; 分离合取式.
  apply orth_at__ncop2 with X X; auto.
Qed.

Lemma l11_62_existence : forall A B C P, exists D,
  共面 A B C D /\ forall E, 共面 A B C E -> Per E D P.
Proof.
  intros A B C P.
  destruct (cop_dec A B C P) as [|HNCop].
    exists P; split; [assumption|intros; Perp].
  assert (HNCol : ~ Col A B C) by (apply 四点不共面则前三点不共线 with P, HNCop).
  destruct (l8_18_过一点垂线之垂点的存在性 A B P) as [D0 [HCol0 HPerp0]].
    intro; apply HNCop; exists P; left; split; Col.
  assert (HCop0 : 共面 A B C D0) by (exists D0; left; split; Col).
  统计不重合点.
  destruct (ex_perp_cop A B D0 C) as [D1 [HPerp1 HCop1]]; auto.
  destruct (垂直推出不共线 A B D1 D0 HPerp1) as [HNCol1|]; [|exfalso; Col].
  assert (Haux : forall D, Col D0 D1 D -> 共面 A B C D).
  { intros D HD.
    apply coplanar_trans_1 with D1; [Col|Cop|].
    统计不重合点; apply 等价共面CABD, col_cop__cop with D0; Col; Cop.
  }
  destruct (每组共线三点都有另一共线点 A B D0 HCol0) as [A0].
  分离合取式.
  assert (HCopA : 共面 A B C A0) by (exists A0; left; split; Col).
  assert (Per P D0 A0) by (destruct (l8_16_1_共线四点和一垂直推另一直角 A B P A0 D0); auto).
  destruct (直角的决定性 P D0 D1) as [|HNPer].
  { exists D0.
    split; Col.
    intros E HE.
    apply l11_60 with A0 D1 D0; Perp.
      intro; apply HNCol1; ColR.
    apply coplanar_pseudo_trans with A B C; trivial.
  }
  destruct (l8_18_过一点垂线之垂点的存在性 D0 D1 P) as [D []]; Col.
    intro Habs; apply HNCop, Haux, Habs.
  exists D; split; auto.
  intros E HE.
  assert (D <> D0) by (intro; subst; apply HNPer; Perp).
  assert (HPer : Per D0 D P) by (apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with D1; auto).
  assert (HPer1 : Per D D0 A0).
    统计不重合点; apply 直角的对称性, 直角边共线点也构成直角2 with D1; auto; destruct (l8_16_1_共线四点和一垂直推另一直角 A B D1 A0 D0); Perp.
  apply l11_60 with D0 A0 D; Perp; [apply 成直角三点不共线 in HPer1; Col|..].
  { destruct (构造对称点 A0 D) as [A0'].
    apply 直角的对称性; exists A0'; split; trivial.
    destruct (构造对称点 D0 D) as [D0'].
    apply l10_12 with D0 D0';
    [..|apply 直角端点和其关于顶点的对称点与另一端点等距 with D|apply 等长的对称性, l7_13_同中点组两侧等长 with D]; Perp.
    destruct (构造对称点 P D) as [P'].
    apply midpoint_preserves_per with P' D0 A0 D; 中点.
    apply l11_60 with P D D0; Perp; [|exists P'; left; split; Col].
    intro; apply HNCop, coplanar_trans_1 with D1; Col; [Cop|].
    exists D0; right; right; split; ColR.
  }
  apply coplanar_pseudo_trans with A B C; trivial.
  apply coplanar_trans_1 with D1; Col.
    Cop.
  exists D0; right; right; split; Col.
Qed.

Lemma l11_62_existence_bis : forall A B C P, ~ 共面 A B C P ->
  exists X, 垂直平面于 X A B C X P.
Proof.
  intros A B C P HNCop.
  destruct (l11_62_existence A B C P) as [X [HCop HX]].
  assert (X <> P) by (intro; subst; apply (HNCop HCop)).
  exists X; repeat split; Col.
    apply 四点不共面则前三点不共线 with P, HNCop.
  intros D Q HD HQ.
  apply 直角边共线点也构成直角2 with P; auto.
Qed.

Lemma l11_63_aux : forall A B C D E P,
  共面 A B C D -> D <> E -> 垂直平面于 E A B C E P ->
  exists Q, OS D E P Q /\ Orth A B C D Q.
Proof.
  intros A B C D E P HD HDE HOrth.
  assert (H' := HOrth).
  destruct H' as [HNCol [HEP [HE1 [_ HE2]]]].
  assert (HNCop : ~ 共面 A B C P).
    intro; apply HEP, (col_cop_orth_at__eq A B C E P); Col.
  destruct (l10_15 D E D P) as [Q [HQ1 HQ2]]; Col.
    intro; apply HNCop, col_cop2__cop with D E; auto.
  exists Q.
  split; [assumption|].
  destruct (ex_ncol_cop A B C D E HDE) as [F [HF1 HF2]].
  destruct (ex_perp_cop D E D F) as [D' [HD'1 HD'2]]; auto.
  assert (~ Col D' D E) by (统计不重合点; apply 成直角三点不共线; Perp).
  assert (共面 D E F A) by (apply coplanar_pseudo_trans with A B C; Cop).
  assert (共面 D E F B) by (apply coplanar_pseudo_trans with A B C; Cop).
  assert (共面 D E F C) by (apply coplanar_pseudo_trans with A B C; Cop).
  exists D.
  apply (cop3_orth_at__orth_at D' D E);
    [assumption|apply coplanar_pseudo_trans with D E F; Cop..|].
  统计不重合点.
  apply l11_60_bis; Cop; [|Perp..].
  destruct (ex_perp_cop D E E F) as [E' [HE'1 HE'2]]; auto.
  统计不重合点.
  apply (l11_61 E E' P); Perp.
    apply coplanar_trans_1 with F; Col; Cop.
    apply os__coplanar in HQ2; Cop.
    apply 直角的对称性, HE2; Col.
    apply HE2; Col; apply coplanar_pseudo_trans with D E F; assumption.
Qed.

Lemma l11_63_existence : forall A B C D P,
  共面 A B C D -> ~ 共面 A B C P ->
  exists Q, Orth A B C D Q.
Proof.
  intros A B C D P HCop HNCop.
  destruct (l11_62_existence_bis A B C P HNCop) as [E HE].
  destruct (两点重合的决定性 D E).
    exists P, D; subst; assumption.
  destruct (l11_63_aux A B C D E P) as [Q []]; auto.
  exists Q; assumption.
Qed.

Lemma 十字上的中间性_3 : forall A B C D X, 共面 A B C D -> ~ 共面 A B C X ->
  exists P T, Orth A B C D P /\ 共面 A B C T /\ Bet X T P.
Proof.
  intros A B C D X HD HX.
  destruct (l11_62_existence_bis A B C X HX) as [E HE].
  destruct (两点重合的决定性 D E).
  { subst E.
    destruct (由一点往一方向构造等长线段 X D D X) as [Y []].
    exists Y, D; subst; repeat split; trivial.
    assert (D <> X) by (intro; subst; apply (HX HD)); 统计不重合点.
    apply col_orth__orth with X; Col.
    exists D; assumption.
  }
  destruct (l11_63_aux A B C D E X) as [P' [HOS HP']]; auto.
  destruct HE as [HNCol [HEX [HE [_ HOrth]]]].
  assert (HOrth' : 垂直平面于 D A B C D P') by (apply col_cop_orth__orth_at; Col).
  assert (HDP' : D <> P') by (apply orth_distincts in HP'; 分离合取式; auto).
  assert (HNCop : ~ 共面 A B C P').
    apply orth_at__ncop2 with D D; auto; apply col_cop_orth__orth_at; Col.
  destruct HOrth' as [_ [_ [_ [_ HOrth']]]].
  destruct (由一点往一方向构造等长线段 P' D D P') as [P []].
  assert (HT : TS D E X P).
  { apply l9_8_2 with P'; [|Side].
    repeat split; [intro; apply HNCop, col_cop2__cop with D E; ColR..|exists D; split; Col].
  }
  destruct HT as [_ [_ [T []]]].
  exists P, T; repeat split; [|apply col_cop2__cop with D E; Col|assumption].
  统计不重合点.
  apply col_orth__orth with P'; Col.
Qed.

Lemma mid2_orth_at2__cong : forall A B C X Y P Q P' Q',
  垂直平面于 X A B C X P -> 垂直平面于 Y A B C Y Q -> 中点 X P P' -> 中点 Y Q Q' ->
  Cong P Q P' Q'.
Proof.
  intros A B C X Y P Q P' Q' HX1 HY1 HX2 HY2.
  assert (HX3 := HX1).
  destruct HX3 as [HNCol [HXP [HCop1 [_ HX3]]]].
  assert (HY3 := HY1).
  destruct HY3 as [_ [HYQ [HCop2 [_ HY3]]]].
  destruct (中点的存在性 X Y) as [Z].
  destruct (构造对称点 P Z) as [R].
  destruct (构造对称点 P' Z) as [R'].
  assert (共面 A B C Z) by (apply bet_cop2__cop with X Y; Between).
  assert (Cong Z P Z P').
    apply 直角端点和其关于顶点的对称点与另一端点等距 with X; Col.
  apply 五线段公理_等价SAS with R R' Z Z; Between.
    apply 等长的传递性 with P Z; [|apply 等长的传递性 with P' Z]; Cong.
    apply 等长的对称性, l7_13_同中点组两侧等长 with Y; [apply 对称保持中点 with P X P' Z|]; assumption.
    apply 直角端点和其关于顶点的对称点与另一端点等距 with Y; Col.
    intro; treat_equalities; auto.
Qed.

Lemma orth_at2_tsp__ts : forall A B C X Y P Q, P <> Q ->
  垂直平面于 P A B C P X -> 垂直平面于 Q A B C Q Y -> 在平面异侧 A B C X Y -> TS P Q X Y.
Proof.
  intros A B C X Y P Q HPQ HP HQ [HX [HY [T [HT HBet]]]].
  assert (HP1 := HP).
  apply orth_at_chara in HP1; 分离合取式.
  assert (HQ1 := HQ).
  apply orth_at_chara in HQ1; 分离合取式.
  repeat split.
    intro; apply HX, col_cop2__cop with P Q; Col.
    intro; apply HY, col_cop2__cop with P Q; Col.
  exists T; split; [|assumption].
  destruct (构造对称点 X P) as [X'].
  destruct (构造对称点 Y Q) as [Y'].
  assert (Cong T X T X') by (apply 直角端点和其关于顶点的对称点与另一端点等距 with P; auto).
  assert (Cong T Y T Y') by (apply 直角端点和其关于顶点的对称点与另一端点等距 with Q; auto).
  apply 等价共线BAC, 中间性蕴含共线1, M是AB中点则M是BA中点2 with X Y X' Y'; trivial.
  apply (l4_6 X T Y); repeat split; Cong.
  assert (~ Col A B C) by (apply 四点不共面则前三点不共线 with X, HX).
  apply mid2_orth_at2__cong with A B C P Q; auto.
Qed.

Lemma orth_dec : forall A B C U V, Orth A B C U V \/ ~ Orth A B C U V.
Proof.
  intros A B C U V.
  destruct (两点重合的决定性 U V).
    unfold Orth, 垂直平面于; right; intros [X []]; 分离合取式; auto.
  revert dependent V.
  revert U.
  assert (Haux : forall U V, U <> V -> ~ 共面 A B C U -> Orth A B C U V \/ ~ Orth A B C U V).
  { intros U V HUV HU.
    destruct (l11_62_existence_bis A B C U HU) as [X HX].
    destruct (共线的决定性 U V X).
      left; apply col_orth__orth with X; Col; apply orth_symmetry; exists X; apply HX.
    right; intros [Y HY].
    assert (X = Y).
    { apply l11_62_unicity_bis with A B C U; [assumption|].
      apply orth_at_symmetry, col_orth_at__orth_at with V; [destruct HY; 分离合取式..|]; trivial.
      intro; subst Y; absurd (共面 A B C U); [|assumption].
      统计不重合点; apply orth_at__ncop2 with X X; auto.
    }
    subst; destruct HY; 分离合取式; Col.
  }
  intros U V HUV.
  destruct (共线的决定性 A B C).
    unfold Orth, 垂直平面于; right; intros [X []]; 分离合取式; auto.
  destruct (cop_dec A B C U); [|auto].
  destruct (cop_dec A B C V).
  - right; intro.
    apply HUV, (orth_at2__eq A B C U V); apply col_cop_orth__orth_at; Col.
  - destruct (Haux V U) as [HOrth|HNOrth]; auto;
    [left|right; intro HOrth; apply HNOrth]; apply orth_symmetry, HOrth.
Qed.

Lemma orth_at_dec : forall A B C U V X, 垂直平面于 X A B C U V \/ ~ 垂直平面于 X A B C U V.
Proof.
  intros A B C U V X.
  destruct (orth_dec A B C U V) as [|HNOrth]; [|right; intro HX; apply HNOrth; exists X; apply HX].
  destruct (cop_dec A B C X); [|unfold 垂直平面于; right; intro; 分离合取式; auto].
  destruct (共线的决定性 U V X) as [HCol|]; [|unfold 垂直平面于; right; intro; 分离合取式; auto].
  left; apply col_cop_orth__orth_at; assumption.
Qed.

Lemma tsp_dec : forall A B C X Y, 在平面异侧 A B C X Y \/ ~ 在平面异侧 A B C X Y.
Proof.
  intros A B C X Y.
  destruct (cop_dec A B C X) as [|HX].
    right; intros [Ha]; apply Ha; assumption.
  destruct (cop_dec A B C Y) as [|HY].
    right; intros [_ [Ha]]; apply Ha; assumption.
  destruct (l11_62_existence_bis A B C X HX) as [P HP].
  destruct (l11_62_existence_bis A B C Y HY) as [Q HQ].
  assert (HP1 := HP).
  apply orth_at_chara in HP1; 分离合取式.
  assert (HQ1 := HQ).
  apply orth_at_chara in HQ1; 分离合取式.
  destruct (两点重合的决定性 P Q).
  { subst Q; clear HQ; destruct (中间性的决定性 X P Y) as [|HNBet].
      left; repeat split; trivial; exists P; split; trivial.
    right; intro HQ; apply HNBet.
    destruct HQ as [_ [_ [Q [HQ HBet]]]].
    replace P with Q; [assumption|].
    apply ABA直角则A与B重合, (三共线点中两点分别与另两点成直角则余下点也行 X Y); try (apply 直角的对称性); Col.
    intro; treat_equalities; auto.
  }
  destruct (two_sides_dec P Q X Y) as [HT|HNTS].
    left; apply cop2_ts__tsp with P Q; assumption.
    right; intro; apply HNTS, (orth_at2_tsp__ts A B C); assumption.
Qed.

Lemma osp_dec : forall A B C X Y, 在平面同侧 A B C X Y \/ ~ 在平面同侧 A B C X Y.
Proof.
  intros A B C X Y.
  destruct (cop_dec A B C X) as [|HX].
    right; intros [X' [[Ha _] _]]; apply Ha; assumption.
  destruct (tsp_exists A B C X HX) as [X'].
  destruct (tsp_dec A B C Y X') as [|HNTS].
    left; exists X'; split; assumption.
    right; intro; apply HNTS; apply l9_41_2 with X; assumption.
Qed.

Lemma ts2__inangle : forall A B C P, TS A C B P -> TS B P A C ->
  在角内 P A B C.
Proof.
  intros A B C P HTS1 HTS2.
  destruct (ts2__ex_bet2 A B C P) as [X [HBet1 HBet2]]; trivial.
  apply ts_distincts in HTS2; 分离合取式.
  repeat split; auto.
  exists X; split; trivial.
  right; apply bet_out; auto.
  intro; subst X.
  apply (two_sides_not_col A C B P HTS1); Col.
Qed.

Lemma os_ts__inangle : forall A B C P, TS B P A C -> OS B A C P -> 在角内 P A B C.
Proof.
  intros A B C P Hts Hos.
  assert(HNCol : ~ Col A B P) by (destruct Hts as []; Col).
  assert(~ Col B A C) by (apply (one_side_not_col123 _ _ _ P); auto).
  assert (HP' := 构造对称点 P B).
  destruct HP' as [P'].
  统计不重合点.
  assert(~ Col B A P') by (intro; apply HNCol; ColR).
  assert(HUn := 角两侧两点必有一点在角内 A B C P P').
  destruct HUn as [|Habs]; Between.
  exfalso.
  apply 角内点和一端点在角另一边同侧 in Habs; Col.
  apply l9_9_bis in Habs.
  apply Habs.
  apply invert_two_sides; apply l9_2.
  apply (l9_8_2 _ _ P); Side.
  repeat split; Col; exists B; split; Col; Between.
Qed.

Lemma os2__inangle : forall A B C P, OS B A C P -> OS B C A P -> 在角内 P A B C.
Proof.
  intros A B C P Hos1 Hos2.
  apply os_ts__inangle; auto.
  apply l9_31; Side.
Qed.

Lemma acute_conga__acute : forall A B C D E F, 为锐角 A B C -> 等角 A B C D E F -> 为锐角 D E F.
Proof.
  intros A B C D E F Hacute HConga.
  apply (小于等于锐角之角为锐角 _ _ _ A B C); auto.
  apply 等角小于等于自己.
  apply 等角的对称性; assumption.
Qed.

Lemma acute_out2__acute : forall A B C A' C', Out B A' A -> Out B C' C -> 为锐角 A B C ->
  为锐角 A' B C'.
Proof.
  intros A B C A' C' HA HC HB.
  apply (acute_conga__acute A B C).
    assumption.
  apply out2__conga; assumption.
Qed.

Lemma conga_obtuse__obtuse : forall A B C D E F, 为钝角 A B C -> 等角 A B C D E F -> 为钝角 D E F.
Proof.
  intros A B C D E F Hobtuse HConga.
  apply (一角小于等于钝角则该角为钝角 _ _ _ A B C); auto.
  apply 等角小于等于自己; assumption.
Qed.

Lemma obtuse_out2__obtuse : forall A B C A' C', Out B A' A -> Out B C' C -> 为钝角 A B C ->
  为钝角 A' B C'.
Proof.
  intros A B C A' C' HA HC HB.
  apply (conga_obtuse__obtuse A B C).
    assumption.
  apply out2__conga; assumption.
Qed.

Lemma bet_lea__bet : forall A B C D E F, Bet A B C -> 角度小于等于 A B C D E F -> Bet D E F.
Proof.
  intros A B C D E F HBet Hlea.
  apply (零角的等角是零角 A B C); auto.
  apply 双角度偏序推等角; auto.
  apply 角度小于等于推出点不重合 in Hlea.
  分离合取式.
  apply l11_31_1_任何角小于等于平角_Bet表述; auto.
Qed.

Lemma out_lea__out : forall A B C D E F, Out E D F -> 角度小于等于 A B C D E F -> Out B A C.
Proof.
  intros A B C D E F Hout Hlea.
  apply (l11_21_a D E F); auto.
  apply 双角度偏序推等角; auto.
  apply 角度小于等于推出点不重合 in Hlea.
  分离合取式.
  apply l11_31_1_任何角小于等于平角_Out表述; auto.
Qed.

Lemma bet2_lta__lta : forall A B C D E F A' D',
  角度小于 A B C D E F -> Bet A B A' -> A' <> B -> Bet D E D' -> D' <> E ->
  角度小于 D' E F A' B C.
Proof.
  intros A B C D E F A' D' Hlta.
  intros.
  assert (Hd := Hlta).
  apply 角度小于推不重合 in Hd.
  unfold 角度小于 in *.
  分离合取式.
  split.
  apply (l11_36_双补角组中的角度偏序 A _ _ D); auto.
  intro.
  assert(等角 A B C D E F); auto.
  apply (l11_13 A' _ _ D'); try (apply 等角的对称性); Between.
Qed.

Lemma lea123456_lta__lta : forall A B C D E F G H I, 角度小于等于 A B C D E F -> 角度小于 D E F G H I ->
   角度小于 A B C G H I.
Proof.
  intros A B C D E F G H I Hlea Hlta.
  split.
  - apply (角度小于等于的传递性 _ _ _ D E F).
    assumption.
    apply 角度小于蕴含角度小于等于; assumption.
  - intro.
    destruct Hlta as [Hlea' HNConga].
    apply HNConga.
    apply 双角度偏序推等角.
    assumption.
    apply (l11_30_等角保持小于等于 A B C D E F); auto.
    apply 角度小于等于推出点不重合 in Hlea.
    分离合取式.
    apply 同角相等; assumption.
Qed.

Lemma lea456789_lta__lta : forall A B C D E F G H I, 角度小于 A B C D E F -> 角度小于等于 D E F G H I ->
   角度小于 A B C G H I.
Proof.
  intros A B C D E F G H I Hlta Hlea.
  split.
  - apply (角度小于等于的传递性 _ _ _ D E F).
    apply 角度小于蕴含角度小于等于; assumption.
    assumption.
  - intro.
    destruct Hlta as [Hlea' HNConga].
    apply HNConga.
    apply 双角度偏序推等角.
    assumption.
    apply (l11_30_等角保持小于等于 D E F G H I); auto; [|apply 等角的对称性; assumption].
    apply 角度小于等于推出点不重合 in Hlea.
    分离合取式.
    apply 同角相等; assumption.
Qed.

Lemma acute_per__lta : forall A B C D E F, 为锐角 A B C -> D <> E -> E <> F -> Per D E F ->
   角度小于 A B C D E F.
Proof.
  intros A B C D E F Hacute HDE HEF HPer.
  intros.
  destruct Hacute as [G [H [I [HPer2 Hlta]]]].
  assert(Hdiff := 角度小于推不重合 A B C G H I Hlta).
  分离合取式.
  apply (等角保持角度小于性质 A B C G H I); try (apply 同角相等); auto.
  apply l11_16_直角相等; auto.
Qed.

Lemma obtuse_per__lta : forall A B C D E F, 为钝角 A B C -> D <> E -> E <> F -> Per D E F ->
   角度小于 D E F A B C.
Proof.
  intros A B C D E F Hobtuse HDE HEF HPer.
  intros.
  destruct Hobtuse as [G [H [I [HPer2 Hlta]]]].
  assert(Hdiff := 角度小于推不重合 G H I A B C Hlta).
  分离合取式.
  apply (等角保持角度小于性质 G H I A B C); try (apply 同角相等); auto.
  apply l11_16_直角相等; auto.
Qed.

Lemma acute_obtuse__lta : forall A B C D E F, 为锐角 A B C -> 为钝角 D E F -> 角度小于 A B C D E F.
Proof.
  intros A B C D E F Hacute Hobtuse.
  destruct Hacute as [G [H [I [HPer Hlta]]]].
  apply (角度小于的传递性 _ _ _ G H I); auto.
  apply 角度小于推不重合 in Hlta.
  分离合取式.
  apply obtuse_per__lta; auto.
Qed.

Lemma lea_in_angle : forall A B C P, 角度小于等于 A B P A B C -> OS A B C P ->
   在角内 P A B C.
Proof.
    intros.
    assert(H1 := H0).
    clear H0.
    assert(H0 : 等角 A B P A B P).
    { assert(~ Col A B P) by (apply (one_side_not_col123 _ _ _ C); Side).
      统计不重合点.
      apply 同角相等; auto.
    }
    unfold 角度小于等于 in H.
    ex_and H T.
    apply (conga_preserves_in_angle A B C T).
      apply 同角相等.
        unfold 等角 in H0.
        分离合取式.
        auto.
      intro.
      subst C.
      unfold OS in H1.
      ex_and H1 X.
      unfold TS in H1.
      分离合取式.
      apply H1.
      Col.
      eapply 角等的传递性; apply 等角的对称性.
        apply H2.
      apply H0.
      apply H.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma acute_中间性平角为钝角 : forall A B C A', Bet A B A' -> A' <> B -> 为锐角 A B C -> 为钝角 A' B C.
Proof.
  intros A B C A' HBet HA'B Hacute.
  assert(Hd := 角为锐角推不重合 A B C Hacute).
  destruct Hd.
  elim(共线的决定性 A B C).
  { intro.
    elim(中间性的决定性 A B C).
    - intro.
      exfalso.
      apply (一角不可能小于自己 A B C).
      apply acute_obtuse__lta; auto.
      apply 中间性平角为钝角; auto.

    - intro.
      apply 中间性平角为钝角; auto.
      apply 中间性的对称性.
      apply (l6_2 A); auto.
      apply not_bet_out; auto.
  }
  intro HNCol1.
  assert(HD := l10_15 A B B C).
  destruct HD as [D []]; Col.
  统计不重合点.
  assert(HNCol2 : ~ Col C B D).
  { intro.
    apply (一角不可能小于自己 A B C).
    apply acute_per__lta; auto.
    apply (直角边共线点也构成直角2 _ _ D); Perp; Col.
  }
  assert(OS B A' C D) by (apply (col_one_side _ A); Side; Col).
  exists A, B, D.
  split; Perp.
  split.
  - exists D.
    split; [|apply 等角的交换性, l11_18_1; Perp].
    apply os2__inangle; auto.
    exists A.
    split.
    { repeat split; Col.
      intro; apply HNCol1; ColR.
      exists B; split; [Col|Between].
    }
    apply invert_two_sides.
    apply 角端点在角内点与顶点连线两侧; Col.
    apply l11_24_在角内的对称性.
    apply lea_in_angle; try (apply 同角相等); Side.
    apply 角度小于蕴含角度小于等于.
    apply acute_per__lta; Perp.

  - intro.
    apply HNCol2.
    assert (Out B D C).
      apply (conga_os__out A'); Side.
      apply (角等的传递性 _ _ _ A B D); auto.
      apply l11_16_直角相等; auto; apply (l8_3_直角边共线点也构成直角1 A); Perp; Col.
    Col.
Qed.

Lemma bet_obtuse__acute : forall A B C A', Bet A B A' -> A' <> B -> 为钝角 A B C -> 为锐角 A' B C.
Proof.
  intros A B C A' HBet HA'B Hobtuse.
  assert(Hd := 角为钝角推不重合 A B C Hobtuse).
  分离合取式.
  elim(共线的决定性 A B C).
  { intro.
    elim(中间性的决定性 A B C).
    - intro.
      apply 外共线零角为锐角.
      apply (l6_2 _ _ A); Between.

    - intro.
      exfalso.
      apply (一角不可能小于自己 A B C).
      apply acute_obtuse__lta; auto.
      apply 外共线零角为锐角.
      apply not_bet_out; auto.
  }
  intro HNCol1.
  assert(HD := l10_15 A B B C).
  destruct HD as [D []]; Col.
  统计不重合点.
  assert(HNCol2 : ~ Col C B D).
  { intro.
    apply (一角不可能小于自己 A B C).
    apply obtuse_per__lta; auto.
    apply (直角边共线点也构成直角2 _ _ D); Perp; Col.
  }
  assert(OS B A' C D) by (apply (col_one_side _ A); Side; Col).
  assert(~ Col A B D) by (apply 成直角三点不共线; Perp).
  exists A'.
  exists B.
  exists D.
  split.
  apply (l8_3_直角边共线点也构成直角1 A); Perp; Col.
  split.
  - exists C.
    split; try (apply 同角相等); auto.
    apply os2__inangle; Side.
    exists A.
    split.
    { repeat split; auto.
      apply (one_side_not_col123 _ _ _ C); Side.
      exists B; split; [Col|Between].
    }
    apply invert_two_sides.
    apply 角端点在角内点与顶点连线两侧; Col.
    apply l11_24_在角内的对称性.
    apply lea_in_angle; try (apply 同角相等); auto.
    apply 角度小于蕴含角度小于等于.
    apply obtuse_per__lta; Perp.

  - intro Habs.
    assert (Out B C D) by (apply (conga_os__out A'); Side).
    apply HNCol2; Col.
Qed.


Lemma inangle_dec : forall A B C P, 在角内 P A B C \/ ~ 在角内 P A B C.
Proof.
  intros A B C P.
  elim(cop_dec A B C P).
  { intro HCop.
    elim(两点重合的决定性 A B).
      intro; subst; right; unfold 在角内; intro; 分离合取式; auto.
    intro.
    elim(两点重合的决定性 C B).
      intro; subst; right; unfold 在角内; intro; 分离合取式; auto.
    intro.
    elim(两点重合的决定性 P B).
      intro; subst; right; unfold 在角内; intro; 分离合取式; auto.
    intro.
    elim(共线的决定性 A B C).
    { intro HColB.
      elim(中间性的决定性 A B C).
      { intro HBBet.
        left.
        repeat split; auto.
        exists B.
        split; auto.
      }
      intro HBNBet.
      elim(out_dec B A P).
      { left.
        repeat split; auto.
        exists A; Between.
      }
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      destruct HUn as [|HoutBXP].
        subst; auto.
      assert(HInter := out2_bet_out A B C X P); auto.
      destruct HInter; auto.
      apply not_bet_out; auto.
    }
    intro HNColB.
    assert(HP' := 构造对称点 P B).
    destruct HP' as [P'].
    统计不重合点.
    elim(two_sides_dec B P A C).
    { intro.
      assert(HUn := 角两侧两点必有一点在角内 A B C P P').
      destruct HUn as [H在角内|H在角内]; Between.
      destruct H在角内 as [_ [_ [_ [X [HXBet HUn]]]]].
      destruct HUn as [HXB|HBout].
        left; repeat split; auto; exists X; split; auto.
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X' [HX'Bet HUn]]]]].
      assert(Col B X' P) by (destruct HUn; subst; Col).
      assert(X = X') by (apply (l6_21_两线交点的唯一性 A C B P); ColR).
      subst X'.
      统计不重合点.
      destruct HUn; auto.
      apply (l6_4_1 P P' B); Between.
      apply (l6_7 _ _ X); auto.
      apply l6_6; auto.
    }
    intro HNts.
    elim(共线的决定性 B A P).
    { intro.
      elim(out_dec B A P).
      { intro.
        left.
        repeat split; auto.
        exists A; Between.
      }
      intro.
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      assert(Col B X P) by (destruct HUn; subst; Col).
      assert(X = A) by (apply (l6_21_两线交点的唯一性 A C B P); Col).
      subst X.
      destruct HUn; auto.
    }
    intro.
    elim(共线的决定性 B C P).
    { intro.
      elim(out_dec B C P).
      { intro.
        left.
        repeat split; auto.
        exists C; Between.
      }
      intro.
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      assert(Col B X P) by (destruct HUn; subst; Col).
      assert(X = C) by (apply (l6_21_两线交点的唯一性 A C B P); Col).
      subst X.
      destruct HUn; auto.
    }
    intro.
    right.
    intro.
    apply HNts.
    apply invert_two_sides.
    apply 角端点在角内点与顶点连线两侧; auto.
  }
  intro HNCop.
  right.
  intro.
  apply HNCop; Cop.
Qed.

Lemma lea_dec : forall A B C D E F, 角度小于等于 A B C D E F \/ ~ 角度小于等于 A B C D E F.
Proof.
  intros A B C D E F.
  elim(两点重合的决定性 A B).
    intro; right; intro Hlea; apply 角度小于等于推出点不重合 in Hlea; 分离合取式; auto.
  intro.
  elim(两点重合的决定性 B C).
    intro; right; intro Hlea; apply 角度小于等于推出点不重合 in Hlea; 分离合取式; auto.
  intro.
  elim(两点重合的决定性 D E).
    intro; right; intro Hlea; apply 角度小于等于推出点不重合 in Hlea; 分离合取式; auto.
  intro.
  elim(两点重合的决定性 E F).
    intro; right; intro Hlea; apply 角度小于等于推出点不重合 in Hlea; 分离合取式; auto.
  intro.
  elim(共线的决定性 A B C).
  { intro.
    elim(out_dec B A C).
      intro; left; apply l11_31_1_任何角小于等于平角_Out表述; auto.
    intro.
    elim(中间性的决定性 D E F).
      intro; left; apply l11_31_1_任何角小于等于平角_Bet表述; auto.
    intro HENBet.
    right.
    intro.
    apply HENBet.
    apply (bet_lea__bet A B C); auto.
    apply not_out_bet; auto.
  }
  intro HNColB.
  elim(共线的决定性 D E F).
  { intro.
    elim(中间性的决定性 D E F).
      intro; left; apply l11_31_1_任何角小于等于平角_Bet表述; auto.
    intro.
    right.
    intro.
    apply HNColB.
    apply 等价共线BAC.
    apply out_col.
    apply (out_lea__out _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro.
  assert(HP := 给定角一边可作出与给定点同侧一点构成等角_非平角 A B C D E F).
  destruct HP as [P []]; Col.
  elim(inangle_dec D E F P).
    intro; left; exists P; auto.
  intro HN在角内.
  right.
  intro.
  apply HN在角内.
  apply lea_in_angle; try (apply 等角的对称性); Side.
  apply (l11_30_等角保持小于等于 A B C D E F); auto; apply 同角相等; auto.
Qed.

Lemma lta_dec : forall A B C D E F, 角度小于 A B C D E F \/ ~ 角度小于 A B C D E F.
Proof.
  intros A B C D E F.
  elim(等角的决定性 A B C D E F).
  { intro.
    right.
    unfold 角度小于.
    intro.
    分离合取式.
    auto.
  }
  intro.
  elim(lea_dec A B C D E F).
  { intro.
    left.
    split; auto.
  }
  intro.
  right.
  unfold 角度小于.
  intro.
  分离合取式.
  auto.
Qed.

Lemma lea_total : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
   角度小于等于 A B C D E F \/ 角度小于等于 D E F A B C.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  elim(共线的决定性 A B C).
  { intro.
    elim(out_dec B A C).
    - intro; left; apply l11_31_1_任何角小于等于平角_Out表述; auto.
    - intro; right; apply l11_31_1_任何角小于等于平角_Bet表述; auto; apply not_out_bet; auto.
  }
  intro.
  elim(共线的决定性 D E F).
  { intro.
    elim(out_dec E D F).
    - intro; right; apply l11_31_1_任何角小于等于平角_Out表述; auto.
    - intro; left; apply l11_31_1_任何角小于等于平角_Bet表述; auto; apply not_out_bet; auto.
  }
  intro.
  elim(lea_dec A B C D E F).
    intro; left; auto.
  intro HNlea.
  right.
  assert(HP := 给定角一边可作出与给定点同侧一点构成等角_非平角 D E F A B C).
  destruct HP as [P []]; Col.
  exists P.
  split; auto.
  apply os2__inangle; Side.
  apply cop_nts__os; Col; Cop.
  - intro.
    apply HNlea.
    apply 等角小于等于自己.
    apply (l11_10 A B P D E F); try (apply out_trivial); try (apply 等角的对称性); auto.
    apply (col_one_side_out _ A); Col; Side.

  - intro.
    apply HNlea.
    apply (l11_30_等角保持小于等于 A B C A B P); try (apply 同角相等); try (apply 等角的对称性); auto.
    exists C.
    split; try (apply 同角相等); auto.
    apply os_ts__inangle; Side.
Qed.

Lemma or_lta2_conga : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 角度小于 A B C D E F \/ 角度小于 D E F A B C \/ 等角 A B C D E F.
Proof.
    intros.
    assert(HH:=lea_total A B C D E F).
    induction HH; auto.
      induction(等角的决定性 A B C D E F).
        right; right.
        assumption.
      left.
      split; assumption.
    induction(等角的决定性 A B C D E F).
      right; right.
      assumption.
    right; left.
    split.
      assumption.
    intro.
    apply H4.
    apply 等角的对称性.
    assumption.
Qed.

Lemma angle_partition : forall A B C, A <> B -> B <> C ->
   为锐角 A B C \/ Per A B C \/ 为钝角 A B C.
Proof.
  intros A B C HAB HBC.
  assert(Hl := 防降维公理_老版本).
  destruct Hl as [A' [B' [D']]].
  assert(~ Col A' B' D') by (unfold Col; auto).
  assert(HC' := l10_15 A' B' B' D').
  destruct HC' as [C' [HC'Right _]]; Col.
  统计不重合点.
  destruct (or_lta2_conga A B C A' B' C') as [|[|]]; auto.
  - left.
    exists A', B', C'.
    repeat (split; Perp).
  - right; right.
    exists A', B', C'.
    repeat (split; Perp).
  - right; left.
    apply (l11_17_等于直角的角是直角 A' B' C'); try (apply 等角的对称性); Perp.
Qed.

Lemma acute_chara : forall A B C A', Bet A B A' -> B <> A' -> (为锐角 A B C <-> 角度小于 A B C A' B C).
Proof.
  intros A B C A' HBet HBA'.
  split.
  - intro Hacute.
    assert(Hdiff := 角为锐角推不重合 A B C Hacute).
    分离合取式.
    apply acute_obtuse__lta; auto.
    apply (acute_中间性平角为钝角 A); auto.

  - intro Hlta.
    assert (Hd := Hlta).
    apply 角度小于推不重合 in Hd.
    分离合取式.
    elim(angle_partition A B C); auto.
    intro Habs.
    exfalso.
    assert(Hlta1 : 角度小于 A B C A B C);
    [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply 同角相等; auto].
    destruct Habs.
    { apply (等角保持角度小于性质 A B C A' B C); try (apply 同角相等); auto.
      apply 等角的对称性.
      apply 等角的交换性.
      apply l11_18_1; Perp.
    }
    apply (角度小于的传递性 _ _ _ A' B C); auto.
    apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); auto.
Qed.

Lemma obtuse_chara : forall A B C A', Bet A B A' -> B <> A' -> (为钝角 A B C <-> 角度小于 A' B C A B C).
Proof.
  intros A B C A' HBet HBA'.
  split.
  - intro Hobtuse.
    assert(Hdiff := 角为钝角推不重合 A B C Hobtuse).
    分离合取式.
    apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); auto.

  - intro Hlta.
    assert (Hd := Hlta).
    apply 角度小于推不重合 in Hd.
    分离合取式.
    elim(angle_partition A B C); auto.
    { intro.
      exfalso.
      assert(Hlta1 : 角度小于 A B C A B C);
      [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply 同角相等; auto].
      apply (角度小于的传递性 _ _ _ A' B C); auto.
      apply acute_obtuse__lta; auto.
      apply (acute_中间性平角为钝角 A); auto.
    }
    intro HUn.
    destruct HUn; auto.
    exfalso.
    assert(Hlta1 : 角度小于 A B C A B C);
    [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply 同角相等; auto].
    apply (等角保持角度小于性质 A' B C A B C); try (apply 同角相等); auto.
    apply 等角的对称性.
    apply 等角的交换性.
    apply l11_18_1; Between; Perp.
Qed.

Lemma conga__acute : forall A B C, 等角 A B C A C B -> 为锐角 A B C.
Proof.
  intros A B C H等角.
  destruct (共线的决定性 A B C).
  { apply 外共线零角为锐角, not_bet_out; trivial.
    intro.
    absurd (B = C).
      apply conga_distinct in H等角; 分离合取式; auto.
    apply 双中间性推出点重合 with A; apply 中间性的对称性; trivial.
    apply (零角的等角是零角 A B C); assumption.
  }
  destruct (由一点往一方向构造等长线段 C B C B) as [C' []].
  apply conga_distinct in H等角; 分离合取式.
  统计不重合点.
  apply 为锐角的对称性, acute_chara with C'; auto.
  destruct (l11_41_三角形两内角小于另一外角 B C A C'); Col.
  apply (等角保持角度小于性质 B C A A B C'); trivial.
    apply 等角的交换性, 等角的对称性; assumption.
    apply 角ABC等于角CBA; auto.
Qed.

Lemma cong__acute : forall A B C, A <> B -> B <> C -> Cong A B A C -> 为锐角 A B C.
Proof.
  intros A B C HAB HBC HCong.
  apply conga__acute.
  统计不重合点.
  destruct (l11_51 A B C A C B) as [_ []]; Cong.
Qed.

Lemma n角度小于蕴含角度小于等于 : forall A B C D E F, ~ 角度小于 A B C D E F -> A <> B -> B <> C -> D <> E -> E <> F ->
   角度小于等于 D E F A B C.
Proof.
  intros A B C D E F HNlta.
  intros.
  elim(等角的决定性 D E F A B C).
    apply 等角小于等于自己.
  intro.
  elim(lea_total D E F A B C); auto.
  intro.
  exfalso.
  apply HNlta.
  split; auto.
  apply 不等角的对称性; assumption.
Qed.

Lemma nlea__lta : forall A B C D E F, ~ 角度小于等于 A B C D E F  -> A <> B -> B <> C -> D <> E -> E <> F ->
   角度小于 D E F A B C.
Proof.
  intros A B C D E F HNlea.
  intros.
  split.
  - elim(lea_total D E F A B C); auto.
    intro; exfalso; auto.
  - intro.
    apply HNlea.
    apply 等角小于等于自己.
    apply 等角的对称性; assumption.
Qed.


(** The following lemmas express the triangle inequality only with predicates from Tarski :
AC <= AB + BC, and AC = AB + BC <-> Bet A B C
 *)

Lemma triangle_strict_inequality : forall A B C D, Bet A B D -> Cong B C B D -> ~ Bet A B C ->
   Lt A C A D.
Proof.
  intros A B C D HBet HCong HNBet.
  elim(共线的决定性 A B C).
  { intro.
    统计不重合点.
    apply not_bet_out in HNBet; Col.
    destruct HNBet as [_ [_ [HBAC|HBCA]]].
    - split.
      { apply (长度小于等于的传递性 _ _ B C).
        apply 长度小于等于的交换性; exists A; split; Between; Cong.
        apply (l5_6_等长保持小于等于关系 D B D A); Cong; exists B; split; Between; Cong.
      }
      intro.
      assert(A = B); auto.
      apply 中间性的对称性 in HBAC.
      apply (中点的唯一性1 C D); split; Cong.
        apply (中间性的外传递性2 _ _ B); auto.
        apply (中间性的外传递性1 _ A); auto.

    - assert(Bet A C D) by (apply (中间性的交换传递性2 _ _ B); Between).
      split.
        exists C; split; Cong.
      intro.
      assert(C = D) by (apply (between_cong A); auto).
      subst D.
      assert(B = C); auto.
      apply (双中间性推出点重合 _ _ A); Between.
  }
  intro HNCol.
  统计不重合点.
  assert(A <> D) by (intro; treat_equalities; auto).
  assert(~ Col A C D) by (intro; apply HNCol; ColR).
  统计不重合点.
  apply 中间性的对称性 in HBet.
  apply l11_44_2_三角形小角对长边; Col.
  assert(等角 C D A D C B).
  { apply (l11_10 C D B D C B); try (apply out_trivial); auto; [|apply l6_6, bet_out; auto].
    apply 等角的交换性.
    apply l11_44_1_三角形底角相等等价于等腰; Cong.
    intro; apply HNCol; ColR.
  }
  split.
  - apply 角度小于等于的交换性.
    exists B.
    repeat (split; auto).
    exists B.
    split; auto.
    right; apply out_trivial; auto.

  - intro.
    assert (Out C A B).
    { apply (conga_os__out D).
        apply (角等的传递性 _ _ _ C D A); auto; apply 等角的对称性, 等角的交换性; auto.
      apply out_one_side; [Col|Out].
    }
    apply HNCol; Col.
Qed.

Lemma triangle_inequality : forall A B C D, Bet A B D -> Cong B C B D -> Le A C A D.
Proof.
  intros A B C D HCong HBet.
  elim(中间性的决定性 A B C).
  - intro.
    elim(两点重合的决定性 A B).
      intro; subst; Le.
    intro.
    assert(C = D).
    apply (点的唯一构造 A B B D); Cong.
    subst; Le.

  - intro.
    assert(Hlt := triangle_strict_inequality A B C D).
    destruct Hlt; auto.
Qed.

Lemma triangle_strict_inequality_2 : forall A B C A' B' C',
   Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> ~ Bet A B C ->
   Lt A C A' C'.
Proof.
  intros A B C A' B' C' HBet H等角 HCongB HNBet.
  destruct (由一点往一方向构造等长线段 A B B C) as [D [HBetD HCongD]].
  apply (等长保持小于关系 A C A D); Cong.
    apply (triangle_strict_inequality _ B); Cong.
  apply (两组连续三点分段等则全体等 _ B _ _ B'); Cong.
  apply 等长的传递性 with B C; trivial.
Qed.

Lemma triangle_inequality_2 : forall A B C A' B' C',
   Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' ->
   Le A C A' C'.
Proof.
  intros A B C A' B' C' HBet H等角 HCongB.
  destruct (由一点往一方向构造等长线段 A B B C) as [D [HBetD HCongD]].
  apply (l5_6_等长保持小于等于关系 A C A D); Cong.
    apply (triangle_inequality _ B); Cong.
  apply (两组连续三点分段等则全体等 _ B _ _ B'); Cong.
  apply 等长的传递性 with B C; trivial.
Qed.


(** The following lemmas express the reverse triangle inequality only with predicates from Tarski :
BC >= |AC - AB|, and BC = |AC - AB| <-> (A = B \/ A = C \/ Out A B C)
 *)

Lemma triangle_strict_reverse_inequality : forall A B C D,
  Out A B D -> Cong A C A D -> ~ Out A B C -> Lt B D B C.
Proof.
  intros A B C D HABD HCong HNout.
  elim(共线的决定性 A B C).
  { intro.
    统计不重合点.
    apply not_out_bet in HNout; Col.
    assert(Bet D A C) by (apply (l6_2 B); auto).
    assert(C <> D) by (intro; treat_equalities; auto).
    split.
    { destruct HABD as [_ [_ [HABD|HADB]]].
      - apply (长度小于等于的传递性 _ _ A D).
          apply 长度小于等于的交换性; exists B; split; Between; Cong.
        apply (l5_6_等长保持小于等于关系 C A C B); Cong.
        exists A; split; Between; Cong.
      - exists D.
        split; Cong.
        apply (中间性的外传递性2 _ _ A); Between.
    }
    intro.
    absurd (A = B); auto.
    apply (中点的唯一性1 D C); split; Cong.
    apply 不重合共线点间距相同则为中点组1; auto; ColR.
  }
  intro HNCol.
  统计不重合点.
  elim(两点重合的决定性 B D).
  { intro.
    subst.
    split; Le.
    intro; treat_equalities; auto.
  }
  intro.
  assert(HNCol2 : ~ Col B C D) by (intro; apply HNCol; ColR).
  assert(HNCol3 : ~ Col A C D) by (intro; apply HNCol; ColR).
  统计不重合点.
  apply l11_44_2_三角形小角对长边; Col.
  assert(等角 A C D A D C) by (apply l11_44_1_三角形底角相等等价于等腰; Cong; Col).
  destruct HABD as [_ [_ [HABD|HADB]]].
  - apply 中间性的对称性 in HABD.
    apply (等角保持角度小于性质 D C B D C A).
      apply 角ABC等于角CBA; auto.
      apply (l11_10 D C A A D C); [apply 等角的左交换性|try (apply out_trivial)..]; auto.
      apply bet_out; auto.
    split.
    { exists B.
      split; [|apply 同角相等; auto].
      repeat split; auto.
      exists B.
      split; auto.
      right; apply out_trivial; auto.
    }
    intro.
    assert (Out C B A).
    { apply (conga_os__out D); trivial.
      apply out_one_side; [Col|Out].
    }
    apply HNCol; Col.

  - assert(HE := 构造对称点 B C).
    destruct HE as [E []].
    统计不重合点.
    apply (bet2_lta__lta A _ _ E); Between.
    assert (OS D C A E).
    { exists B.
        repeat split; Col.
        exists D; Col.
        intro; apply HNCol2; ColR.
        exists C; split; finish.
    }
    apply (等角保持角度小于性质 A C D E C D); try (apply 同角相等); auto.
    split.
    { apply 角度小于等于的交换性.
      exists A.
      split; [|apply 同角相等; auto].
      apply os2__inangle; Side.
      apply (col_one_side _ B); Col.
      apply invert_one_side.
      apply out_one_side; Col.
      apply bet_out; Between.
    }
    intro.
    assert (Out C A E).
      apply (conga_os__out D); [apply 等角的交换性|]; assumption.
    apply HNCol; ColR.
Qed.

Lemma triangle_reverse_inequality : forall A B C D, Out A B D -> Cong A C A D -> Le B D B C.
Proof.
  intros A B C D HABD HCong.
  elim(out_dec A B C); [|apply triangle_strict_reverse_inequality; auto].
  intro.
  统计不重合点.
  assert(C = D) by (apply (l6_11_uniqueness A A C B); Cong; apply l6_6; auto).
  subst; Le.
Qed.

(** This is half of Euclid Book I, Proposition 21:
  if D is inside the triangle ABC then BAC < BDC.
 *)

Lemma os3__lta : forall A B C D, OS A B C D -> OS B C A D -> OS A C B D ->
   角度小于 B A C B D C.
Proof.
  intros A B C D HosC HosA HosB.
  assert(HE : 在角内 D A B C) by (apply os2__inangle; Side).
  destruct HE as [_ [_ [_ [E [HEBet HUn]]]]].
  assert(HNCol : ~ Col A B C) by (apply (one_side_not_col123 _ _ _ D); auto).
  assert_ncols.
  destruct HUn as [|HBout].
    exfalso; subst; Col.
  assert(A <> E) by (intro; subst; Col5).
  assert(C <> E) by (intro; subst; Col5).
  统计不重合点.
  apply (角度小于的传递性 _ _ _ B E C).
  - destruct (l11_41_三角形两内角小于另一外角 E A B C); auto.
      intro; apply HNCol; ColR.
    apply (等角保持角度小于性质 E A B B E C); try (apply 同角相等); auto.
    apply 等角的左交换性, out2__conga.
      apply out_trivial; auto.
      apply l6_6, bet_out; auto.

  - assert(Out E D B).
      apply (col_one_side_out _ A); Col; apply invert_one_side; apply (col_one_side _ C); Col; Side.
    统计不重合点.
    destruct (l11_41_三角形两内角小于另一外角 D E C B); auto.
      intro; apply HNCol; ColR.
      apply out2__bet; auto.
    apply (等角保持角度小于性质 D E C C D B); try (apply 角ABC等于角CBA); auto.
    apply out2__conga.
      apply l6_6; assumption.
      apply out_trivial; auto.
Qed.

(** This is Theorem 18.17 from Martin *)

Lemma bet_le__lt : forall A B C D, Bet A D B -> A <> D -> D <> B -> Le A C B C -> Lt D C B C.
Proof.
  intros A B C D HBet HAD HBD Hle.
  assert(HAB : B <> A) by (intro; treat_equalities; auto).
  apply 长度小于的交换性.
  elim(共线的决定性 A B C).
  { intro.
    elim(中间性的决定性 C D B).
    { intro.
      split.
      exists D; Cong.
      intro.
      apply HBD.
      apply (between_cong C); auto.
    }
    intro HNBet.
    apply not_bet_out in HNBet; try ColR.
    统计不重合点.
    assert(Bet C D A) by (apply (l6_2 B); try (apply l6_6); Between).
    assert(A <> C) by (intro; treat_equalities; auto).
    assert(Hout : Out A C B) by (apply (l6_7 _ _ D); [apply l6_6|]; apply bet_out; Between).
    assert(~ Bet A B C).
    { intro.
      apply HAB.
      apply (between_cong C); Between.
      apply 长度小于等于的反对称性; Le.
    }
    assert(B <> C) by (intro; subst; Between).
    assert (Bet B C A).
      apply out2__bet; [apply not_bet_out; Col; Between|apply l6_6; assumption].
    assert(HC' := 构造对称点 A C).
    destruct HC' as [C'].
    统计不重合点.
    assert(Bet C C' B).
    { apply l6_13_1.
      apply (l6_2 _ _ A); Between.
      apply (l5_6_等长保持小于等于关系 A C B C); Cong.
    }
    apply (长度小于_小于等于_传递性 _ _ C A); [|exists C'; split; Cong].
    split.
    exists D; Cong.
    intro.
    apply HAD.
    symmetry.
    apply (between_cong C); Between.
  }
  intro HNCol.
  统计不重合点.
  apply l11_44_2_三角形小角对长边.
    intro; apply HNCol; ColR.
  apply (lea123456_lta__lta _ _ _ C A B).
  - apply lea_out4__lea with C A C B; try apply out_trivial; auto; [|apply l6_6, bet_out; Between].
    apply l11_44_2_三角形小角对长边_偏序版; Col; Le.

  - assert(~ Col D A C) by (intro; apply HNCol; ColR).
    统计不重合点.
    assert(HInter := l11_41_三角形两内角小于另一外角 D A C B).
    destruct HInter; auto.
    apply (等角保持角度小于性质 D A C C D B); try (apply 同角相等); auto.
    apply (l11_10 D A C C A D); try (apply out_trivial); try (apply 角ABC等于角CBA); auto.
    apply l6_6, bet_out; auto.
Qed.

Lemma cong2__ncol : forall P A B C, A <> B -> B <> C -> A <> C ->
  Cong A P B P -> Cong A P C P -> ~ Col A B C.
Proof.
  assert (H : forall P A B C, A <> B -> B <> C -> Cong A P C P -> Cong B P C P -> ~ Bet A B C).
  { intros P A B C HAB HBC HCong1 HCong2 HBet.
    apply (bet_le__lt A C P B); Le.
  }
  intros P A B C; intros.
  assert (Cong B P C P) by (apply 等长的传递性 with A P; Cong).
  intro HCol; elim HCol; [|intro Hd; elim Hd]; apply (H P); Cong.
Qed.

Lemma cong4_cop2__eq : forall A B C P Q, A <> B -> B <> C -> A <> C ->
  Cong A P B P -> Cong A P C P -> 共面 A B C P ->
  Cong A Q B Q -> Cong A Q C Q -> 共面 A B C Q ->
  P = Q.
Proof.
    intros A B C P Q; intros.
    assert (HNCol : ~ Col A B C) by (apply (cong2__ncol P); auto).
    destruct (两点重合的决定性 P Q); [assumption|].
    exfalso.
    apply HNCol.
    assert (Haux : forall R, Col P Q R -> Cong A R B R /\ Cong A R C R).
      intros R HR; split; apply 等长的交换性, (l4_17 P Q); Cong.
    destruct (中点的存在性 A B) as [D].
    统计不重合点.
    assert (HCol1 : Col P Q D).
    { assert (共面 A B C D) by Cop.
      apply cong3_cop2__col with A B; Cong; apply coplanar_pseudo_trans with A B C; Cop.
    }
    destruct (每组共线三点都有另一共线点 P Q D HCol1) as [R1]; 分离合取式.
    destruct (由一点往一方向构造等长线段 R1 D R1 D) as [R2 []].
    统计不重合点.
    assert (Col P Q R2) by ColR.
    destruct (Haux R1); trivial.
    destruct (Haux R2); trivial.
    assert (Cong A R1 A R2).
    { assert (Per A D R1) by (apply 直角的对称性; exists B; split; Cong).
      apply l10_12 with D D; Cong.
      apply 直角边共线点也构成直角2 with R1; ColR.
    }
    apply cong3_cop2__col with R1 R2; auto; [apply col_cop2__cop with P Q; auto..| |].
      apply 等长的传递性 with A R1; [|apply 等长的传递性 with A R2]; Cong.
      apply 等长的传递性 with A R1; [|apply 等长的传递性 with A R2]; Cong.
Qed.

Lemma t18_18_aux : forall A B C D E F,
  Cong A B D E -> Cong A C D F -> 角度小于 F D E C A B -> ~ Col A B C -> ~ Col D E F -> Le D F D E ->
  Lt E F B C.
Proof.
  intros A B C D E F H等角B H等角C Hlta HNCol1 HNCol2 Hle.
  assert (Hd := Hlta).
  apply 角度小于推不重合 in Hd.
  分离合取式.
  assert(HG0 := 给定角一边可作出与给定点同侧一点构成等角_非平角 C A B F D E).
  destruct HG0 as [G0 []]; Col.
  assert(~ Col F D G0) by (apply (one_side_not_col123 _ _ _ E); auto).
  统计不重合点.
  assert(HG := 由一点往一方向构造等长线段_3 D G0 A B).
  destruct HG as [G []]; auto.
  assert(等角 C A B F D G).
    apply (l11_10 C A B F D G0); try (apply out_trivial); auto; apply l6_6; auto.
  assert(OS F D G E).
  { apply (one_side_transitivity _ _ _ G0); auto.
    apply invert_one_side.
    apply out_one_side; Col.
    apply l6_6; auto.
  }
  assert(HNCol3 : ~ Col F D G) by (apply (one_side_not_col123 _ _ _ E); auto).
  clear dependent G0.

  统计不重合点.
  assert(HSAS := l11_49 C A B F D G).
  destruct HSAS as [HCongBC _]; Cong.
  apply (等长保持小于关系 F E F G); Cong.
  apply (等角保持角度小于性质 _ _ _ _ _ _ F D E F D G) in Hlta; try (apply 同角相等); auto.
  assert(Cong D G D E) by (apply (等长的传递性 _ _ A B); auto).
  clear dependent A.
  clear dependent B.

  assert(~ Col E F G).
  { intro.
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    assert (HSSA := l11_52 E F D G F D).
    destruct HSSA as [_[]]; Cong; Le.
    apply (l11_10 G F D G F D); try (apply out_trivial); try (apply 同角相等); auto.
    apply l6_6, (col_one_side_out _ D); Col.
  }
  assert(~ Col D E G).
  { intro.
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    apply (l11_10 F D G F D G); try (apply out_trivial); try (apply 同角相等); auto.
    apply (col_one_side_out _ F); Col; Side.
  }
  apply l11_44_2_三角形小角对长边; Col.
  assert(H在角内 : 在角内 E F D G) by (apply lea_in_angle; destruct Hlta; auto).
  rename H into HFD.
  destruct H在角内 as [_ [_ [_ [H [HH HUn]]]]].
  destruct HUn.
    exfalso; subst; Col.
  assert(H <> F) by (intro; subst; apply HNCol2; Col).
  assert(H <> G) by (intro; subst; Col5).
  assert(Hlt : Lt D H D E).
  { apply (等长保持小于关系 H D G D); Cong.
    apply (bet_le__lt F); auto.
    apply (l5_6_等长保持小于等于关系 D F D E); Cong.
  }
  destruct Hlt.
  assert(H <> E) by (intro; subst; Cong).
  assert(Bet D H E) by (apply l6_13_1; Le).
  统计不重合点.
  assert(OS E G F D).
  { apply (one_side_transitivity _ _ _ H);
    [apply invert_one_side; apply one_side_symmetry|];
    apply out_one_side; Col;
    apply bet_out; Between.
  }
  apply (角度小于的传递性 _ _ _ D E G).
  - apply(等角保持角度小于性质 F G E D G E); try (apply 同角相等); auto.
      apply l11_44_1_三角形底角相等等价于等腰; Col.
    split.
    { apply 角度小于等于的交换性.
      exists F.
      split; try (apply 同角相等); auto.
      repeat split; auto.
      exists H.
      split; Between.
      right; apply bet_out; Between.
    }
    intro HConga.
    apply 等角的交换性 in HConga.
    assert (Out G F D) by (apply (conga_os__out E); assumption).
    apply HNCol3; Col.

  - apply 角度小于的交换性.
    split.
    { exists D.
      split; [|apply 同角相等; auto].
      repeat split; auto.
      exists H.
      split; Between.
      right; apply bet_out; Between.
    }
    intro HConga.
    assert (Out E D F) by (apply (conga_os__out G); Side).
    apply HNCol2; Col.
Qed.

(** This is Euclid Book I, Proposition 24. *)

Lemma t18_18 : forall A B C D E F, Cong A B D E -> Cong A C D F -> 角度小于 F D E C A B -> Lt E F B C.
Proof.
  intros A B C D E F H等角B H等角C Hlta.
  assert (Hd := Hlta).
  apply 角度小于推不重合 in Hd.
  分离合取式.
  elim(共线的决定性 A B C).
  { intro.
    elim(中间性的决定性 B A C).
    - intro.
      assert(HC' := 由一点往一方向构造等长线段 E D A C).
      destruct HC' as [C' []].
      apply (等长保持小于关系 E F E C'); Cong; [|apply (两组连续三点分段等则全体等 _ D _ _ A); Cong].
      apply (triangle_strict_inequality _ D); auto.
      apply (等长的传递性 _ _ A C); Cong.
      intro.
      destruct Hlta as [_ HNConga].
      apply HNConga.
      apply 成中间性三点组的角相等; Between.

    - intro.
      exfalso.
      apply (一角不可能小于自己 C A B).
      apply (lea123456_lta__lta _ _ _ F D E); auto.
      apply l11_31_1_任何角小于等于平角_Out表述; auto.
      apply not_bet_out; Col; Between.
  }
  intro.
  elim(共线的决定性 D E F).
  { intro.
    elim(中间性的决定性 F D E).
    - intro.
      exfalso.
      apply (一角不可能小于自己 F D E).
      apply (lea456789_lta__lta _ _ _ C A B); auto.
      apply l11_31_1_任何角小于等于平角_Bet表述; auto.

    - intro HNBet.
      apply not_bet_out in HNBet; Col.
      assert(HF' := 由一点往一方向构造等长线段_3 A B A C).
      destruct HF' as [F' []]; auto.
      apply (等长保持小于关系 B F' B C); Cong.
      { apply (triangle_strict_reverse_inequality A); Cong.
        intro.
        destruct Hlta as [_ HNConga].
        apply HNConga.
        apply l11_21_b; auto.
        apply l6_6; auto.
      }
      apply (out_cong_cong A _ _ D); auto.
      apply l6_6; auto.
      apply (等长的传递性 _ _ A C); auto.
  }
  intro.
  elim(长度小于等于的决定性 D F D E); intro; [|apply 长度小于的交换性; apply 角度小于的交换性 in Hlta];
  apply (t18_18_aux A _ _ D); Cong; Col.
Qed.

Lemma t18_19 : forall A B C D E F, A <> B -> A <> C -> Cong A B D E -> Cong A C D F -> Lt E F B C ->
   角度小于 F D E C A B.
Proof.
  intros A B C D E F HAB HAC H等角B H等角C Hlt.
  统计不重合点.
  apply nlea__lta; auto.
  intro Hlea.
  elim(等角的决定性 C A B F D E).
  - intro.
    exfalso.
    destruct Hlt as [Hle HNCong].
    apply HNCong.
    assert(HSAS := l11_49 C A B F D E).
    destruct HSAS; Cong.

  - intro.
    apply (两长度不可能互相小于对方 E F B C).
    split; auto.
    apply (t18_18 D _ _ A); Cong.
    split; auto.
Qed.

Lemma acute_trivial : forall A B, A <> B -> 为锐角 A B A.
Proof.
    intros.
    assert(HH:= 两点不重合则存在不共线的点 A B H).
    ex_and HH P.
    assert(exists C : Tpoint, Per C B A /\ Cong C B A B /\ OS A B C P).
      apply(ex_四点成首末边等长双直角S形则对边等长 A B B P A B H H); Col; exists A.
    ex_and H1 C.
    统计不重合点.
    exists A, B, C.
    split.
      apply 直角的对称性.
      auto.
    split.
      exists A.
      split.
        apply A在角ABC内; auto.
      apply 同角相等; auto.
    intro.
    assert(Out B A C).
      apply(l11_21_a A B A A B C).
        apply out_trivial; auto.
      auto.
    assert(Perp C B B A).
      apply 直角转L形垂直于 in H1; auto.
      apply 垂直于转T形垂直 in H1.
      induction H1.
        apply 垂直推出不重合1 in H1.
        tauto.
      auto.
    apply 垂直的交换性 in H10.
    apply L形垂直推出不共线 in H10.
    apply out_col in H8.
    Col.
Qed.

Lemma acute_not_per : forall A B C, 为锐角 A B C -> ~ Per A B C.
Proof.
    intros.
    unfold 为锐角 in H.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    unfold 角度小于 in H0.
    分离合取式.
    intro.
    apply H1.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B').
      unfold 角度小于等于 in H0.
      ex_and H0 X.
      apply conga_distinct in H3.
      分离合取式.
      repeat split; auto.
      unfold 在角内 in H0.
      分离合取式; auto.
    分离合取式.
    apply(l11_16_直角相等 A B C A' B' C'); auto.
Qed.

Lemma angle_bisector : forall A B C, A <> B -> C <> B ->
  exists P, 在角内 P A B C /\ 等角 P B A P B C.
Proof.
  intros A B C HAB HCB.
  elim (共线的决定性 A B C).
  { intro HCol.
    elim (中间性的决定性 A B C).
    - intro HBet; destruct (两点不重合则存在不共线的点 A B) as [Q HNCol]; trivial.
      destruct (l10_15 A B B Q) as [P [HPerp HOS]]; Col.
      统计不重合点; exists P; split.
        apply 任何点都在平角内; auto.
      apply l11_18_1; Perp.
    - intro HOut; apply not_bet_out in HOut; trivial; 统计不重合点.
      exists C; split.
        repeat split; auto.
       exists C; split; Between.
        right; apply out_trivial; auto.
      apply l11_21_b.
        apply l6_6; trivial.
      apply out_trivial; auto.
  }
  intro HNCol.
  统计不重合点.
  destruct (l6_11_existence B B A C) as [C0 [HOut HCong]]; auto.
  destruct (中点的存在性 A C0) as [P HP].
  exists P.
  统计不重合点.
  assert (HNCol1 : ~ Col A B C0) by (intro; apply HNCol; ColR).
  统计不重合点.
  assert (P <> B) by (intro; subst P; apply HNCol1; Col).
  split.
    apply (l11_25 P A B C0); try (apply out_trivial); auto; [|apply l6_6; trivial].
    repeat split; auto.
    exists P; split; Between.
    right; apply out_trivial; auto.
  destruct (l11_51 B P A B P C0); Cong.
  apply (l11_10 P B A P B C0); try (apply out_trivial); auto; apply l6_6; assumption.
Qed.

Lemma reflectl__conga : forall A B P P', A <> B -> B <> P -> 严格对称 P P' A B -> 等角 A B P A B P'.
Proof.
  intros A B P P' HAB HBP HRefl.
  destruct HRefl as [[A' [HMid HCol]] [HPerp|Heq]]; [|subst; apply 同角相等; auto].
  统计不重合点.
  destruct (两点重合的决定性 A' B).
    subst A'.
    统计不重合点.
    apply l11_16_直角相等; auto; apply L形垂直转直角1;
    [apply 垂线共线点也构成垂直2 with P'|apply 垂线共线点也构成垂直2 with P]; Col; Perp.
  destruct HMid as [HBet HCong].
  destruct (l11_49 B A' P B A' P') as [HCong1 [HConga1 HConga2]]; Cong.
    apply l11_16_直角相等; auto;
    apply L形垂直转直角1, 垂直的左交换性, 垂线共线点也构成垂直1 with A; Col;
    [apply 垂线共线点也构成垂直2 with P'|apply 垂线共线点也构成垂直2 with P]; Col; Perp.
  destruct (中间性的决定性 A' B A) as [HBBet|HBOut].
    apply l11_13 with A' A'; assumption.
  apply not_bet_out in HBOut; Col.
  统计不重合点.
  apply l6_6 in HBOut.
  apply l11_10 with A' P A' P'; trivial; apply out_trivial; auto.
Qed.

Lemma conga_cop_out_reflectl__out : forall A B C P T T',
  ~ Out B A C -> 共面 A B C P -> 等角 P B A P B C -> Out B A T -> 严格对称 T T' B P ->
  Out B C T'.
Proof.
  intros A B C P T T' HNOut HCop HConga HOut HRefl.
  apply conga_distinct in HConga; 分离合取式; clean.
  统计不重合点.
  assert (HConga1 : 等角 P B T P B T') by (apply reflectl__conga; auto; apply is_image_spec_rev, HRefl).
  apply is_image_is_image_spec in HRefl; auto.
  apply conga_distinct in HConga1; 分离合取式; clean.
  apply (conga_os__out P).
  - apply 角等的传递性 with P B A.
    apply 等角的对称性; assumption.
    apply l11_10 with P T P T'; try (apply out_trivial); auto.
  - exists A; split; apply l9_2.
      destruct (conga_cop__or_out_ts P B A C); Cop; contradiction.
    apply out_two_sides_two_sides with T B; Col.
    apply invert_two_sides, l10_14; auto.
    intro; subst T'.
    apply HNOut.
    assert (Col T B P) by (apply l10_8, HRefl).
    assert (Col P B A) by ColR.
    assert (Col P B C) by (apply (共线三点构成的角的等角三点也共线 P B A); assumption).
    apply not_bet_out; try ColR.
    intro HBet.
    apply (成直角三点不共线 P B A); auto.
    apply l11_18_2 with C; assumption.
Qed.

Lemma col_conga_cop_reflectl__col : forall A B C P T T',
  ~ Out B A C -> 共面 A B C P -> 等角 P B A P B C -> Col B A T -> 严格对称 T T' B P ->
  Col B C T'.
Proof.
  intros A B C P T T' HNOut HCop HConga HCol HRefl.
  destruct (两点重合的决定性 B T).
    subst; assert (T = T'); subst; Col.
    apply (l10_6_uniqueness_spec T P T); trivial; apply col__refl; Col.
  destruct (out_dec B A T).
    apply out_col, conga_cop_out_reflectl__out with A P T; assumption.
  destruct (由一点往一方向构造等长线段 A B A B) as [A' [HA'1 HA'2]].
  destruct (由一点往一方向构造等长线段 C B C B) as [C' [HC'1 HC'2]].
  assert (Out B C' T'); try ColR.
  apply conga_distinct in HConga; 分离合取式; 统计不重合点.
  apply conga_cop_out_reflectl__out with A' P T; trivial.
  - intro; apply HNOut.
    apply l6_2 with A'; auto.
    apply 中间性的对称性, l6_2 with C'; try (apply l6_6); Between.
  - destruct (共线的决定性 A B C).
      exists C'; left; split; ColR.
    apply coplanar_pseudo_trans with A B C; Cop.
  - apply 等角的交换性, l11_13 with A C; auto; apply 等角的交换性; assumption.
  - apply l6_2 with A; try (apply 中间性的对称性); auto.
    apply not_out_bet; Col.
Qed.

Lemma conga2_cop2__col : forall A B C P P', ~ Out B A C ->
  等角 P B A P B C -> 等角 P' B A P' B C ->
  共面 A B P P' -> 共面 B C P P' ->
  Col B P P'.
Proof.
  intros A B C P P' HNOut HP HP' HCopA HCopC.
  apply conga_distinct in HP; apply conga_distinct in HP'; 分离合取式; clean.
  destruct (l6_11_existence B B A C) as [C' [HC'1 HC'2]]; auto.
  destruct (l11_49 P B A P B C'); Cong.
    apply l11_10 with P A P C; try apply out_trivial; auto.
  destruct (l11_49 P' B A P' B C'); Cong.
    apply l11_10 with P' A P' C; try apply out_trivial; auto.
  apply cong3_cop2__col with A C'; Cong.
    Cop.
    apply 等价共面CABD, col_cop__cop with C; Col; Cop.
  intro; subst; auto.
Qed.

Lemma conga2_cop2__col_1 : forall A B C P P', ~ Col A B C ->
  等角 P B A P B C -> 等角 P' B A P' B C ->
  共面 A B C P -> 共面 A B C P' ->
  Col B P P'.
Proof.
  intros A B C P P' HNCol HP HP' HCop HCop'.
  apply conga2_cop2__col with A C; trivial; [|apply coplanar_pseudo_trans with A B C; Cop..].
  intro; apply HNCol; Col.
Qed.

Lemma col_conga__conga : forall A B C P P', 等角 P B A P B C -> Col B P P' -> B <> P' ->
  等角 P' B A P' B C.
Proof.
  intros A B C P P' HConga HCol HBP'.
  destruct (中间性的决定性 P B P') as [HBet|HNBet].
    apply l11_13 with P P; auto.
  apply not_bet_out in HNBet; Col.
  apply l6_6 in HNBet.
  apply conga_distinct in HConga; 分离合取式.
  apply l11_10 with P A P C; try (apply out_trivial); auto.
Qed.

Lemma cop_inangle__ex_col_inangle : forall A B C P Q,
  ~ Out B A C -> 在角内 P A B C -> 共面 A B C Q ->
  exists R, 在角内 R A B C /\ P <> R /\ Col P Q R.
Proof.
  intros A B C P Q HNOut HIn HCop.
  assert (h := 在角内推出点不重合 A B C P HIn); 分离合取式.
  assert (A <> C) by (intro; subst; apply HNOut, out_trivial; auto).
  destruct (两点重合的决定性 P Q).
  { subst Q.
    destruct (两点重合的决定性 A P).
      subst P; exists C; split; Col.
      apply C在角ABC内; auto.
    exists A; split; Col; apply A在角ABC内; auto.
  }
  destruct (共线的决定性 B P Q) as [HCol|HNCol1].
  { destruct (由一点往一方向构造等长线段 B P B P) as [R [HR1 HR2]].
    exists R.
    统计不重合点; split; [|split; ColR].
    apply l11_25 with P A C; try (apply out_trivial); auto.
    apply l6_6, bet_out; auto.
  }
  统计不重合点.
  destruct (共线的决定性 A B C) as [HCol|HNCol2].
    exists Q; split; Col.
    apply 任何点都在平角内; auto.
    apply not_out_bet; assumption.
  destruct (共线的决定性 B C P) as [HCol|HNCol3].
  - assert (HNCol3 : ~ Col B A P) by (intro; apply HNCol2; ColR).
    destruct (cop_not_par_same_side B P Q P P A) as [Q0 [HCol1 HOS]]; Col.
      apply 等价共面CDAB, col_cop__cop with C; Cop.
    assert (Hd := os_distincts B P A Q0 HOS); 分离合取式; clean.
    destruct (one_side_dec B A P Q0).
    { assert (HIn' : 在角内 Q0 A B P) by (apply os2__inangle; assumption).
      exists Q0; split; Col.
      apply 在角内的传递性 with P; trivial.
    }
    assert (HR : exists R, Bet P R Q0 /\ Col P Q R /\ Col B A R).
    { destruct (共线的决定性 B A Q0).
        exists Q0; split; Between; Col.
      统计不重合点.
      destruct (cop_nos__ts B A P Q0) as [_ [_ [R [HCol' HBet]]]]; Col; Cop.
      exists R; split; trivial; split; ColR.
    }
    destruct HR as [R [HR1 [HR2 HR3]]].
    assert (P <> R) by (intro; subst; apply HNCol3, HR3).
    exists R; split; auto.
    apply out321__inangle; auto.
    apply col_one_side_out with P; trivial.
    apply one_side_transitivity with Q0; trivial.
    apply one_side_not_col124 in HOS.
    apply invert_one_side, out_one_side; Col.
    apply l6_6, bet_out; auto.
  - destruct (cop_not_par_same_side B P Q P P C) as [Q0 [HCol1 HOS]]; Col.
      apply 等价共面ACDB, coplanar_trans_1 with A; Cop.
    assert (Hd := os_distincts B P C Q0 HOS); 分离合取式; clean.
    destruct (one_side_dec B C P Q0).
    { assert (HIn' : 在角内 Q0 C B P) by (apply os2__inangle; assumption).
      exists Q0; split; Col.
      apply l11_24_在角内的对称性, 在角内的传递性 with P; trivial.
      apply l11_24_在角内的对称性, HIn.
    }
    assert (HR : exists R, Bet P R Q0 /\ Col P Q R /\ Col B C R).
    { destruct (共线的决定性 B C Q0).
        exists Q0; split; Between; Col.
      统计不重合点.
      destruct (cop_nos__ts B C P Q0) as [_ [_ [R [HCol' HBet]]]]; Col; Cop.
      exists R; split; trivial; split; ColR.
    }
    destruct HR as [R [HR1 [HR2 HR3]]].
    assert (P <> R) by (intro; subst; apply HNCol3, HR3).
    exists R; split; auto.
    apply l11_24_在角内的对称性, out321__inangle; auto.
    apply col_one_side_out with P; trivial.
    apply one_side_transitivity with Q0; trivial.
    apply one_side_not_col124 in HOS.
    apply invert_one_side, out_one_side; Col.
    apply l6_6, bet_out; auto.
Qed.

Lemma col_inangle2__out : forall A B C P Q,
  ~ Bet A B C -> 在角内 P A B C -> 在角内 Q A B C -> Col B P Q ->
  Out B P Q.
Proof.
  intros A B C P Q HNBet HP HQ HCol.
  assert (Hd := 在角内推出点不重合 A B C P HP);
  assert (Hd' := 在角内推出点不重合 A B C Q HQ);
  分离合取式; clean.
  destruct (共线的决定性 A B C).
    assert (Out B A C) by (apply not_bet_out; assumption).
    apply l6_7 with A; [apply l6_6|]; apply in_angle_out with C; auto.
  destruct (共线的决定性 B A P) as [HCol1|HNCol1].
    apply l6_7 with A; [apply l6_6|]; apply col_in_angle_out with C; ColR.
  apply col_one_side_out with A; trivial.
  apply one_side_transitivity with C; [|apply one_side_symmetry];
    apply invert_one_side, 角内点和一端点在角另一边同侧; Col.
  intro; apply HNCol1; ColR.
Qed.

Lemma inangle2__lea : forall A B C P Q, 在角内 P A B C -> 在角内 Q A B C ->
  角度小于等于 P B Q A B C.
Proof.
  intros A B C P Q HP HQ.
  assert (HP' := l11_24_在角内的对称性 P A B C HP).
  assert (HQ' := l11_24_在角内的对称性 Q A B C HQ).
  assert (Hd := 在角内推出点不重合 A B C P HP);
  assert (Hd' := 在角内推出点不重合 A B C Q HQ);
  分离合取式; clean.
  destruct (共线的决定性 A B C) as [HCol|HNCol].
  { destruct (中间性的决定性 A B C).
      apply l11_31_1_任何角小于等于平角_Bet表述; auto.
    apply l11_31_1_任何角小于等于平角_Out表述; auto.
    assert (Out B A C) by (apply not_bet_out; assumption).
    apply l6_7 with A; [apply l6_6|]; apply in_angle_out with C; auto.
  }
  destruct (共线的决定性 B P Q) as [HCol1|HNCol1].
    apply l11_31_1_任何角小于等于平角_Out表述; auto; apply col_inangle2__out with A C; auto.
    intro; apply HNCol; Col.
  destruct (共线的决定性 B A P) as [HCol2|HNCol2].
  { assert (Out B A P) by (apply col_in_angle_out with C; auto; intro; apply HNCol; Col).
    exists Q; split; trivial.
    apply out2__conga; [|apply out_trivial]; auto.
  }
  destruct (共线的决定性 B C P) as [HCol3|HNCol3].
  { assert (Out B C P).
      apply col_in_angle_out with A; auto; intro; apply HNCol; Col.
    apply 角度小于等于的右交换性.
    exists Q; split; trivial.
    apply out2__conga; [|apply out_trivial]; auto.
  }
  destruct (共线的决定性 B A Q) as [HCol4|HNCol4].
  { assert (Out B A Q) by (apply col_in_angle_out with C; auto; intro; apply HNCol; Col).
    apply 角度小于等于的左交换性.
    exists P; split; trivial.
    apply out2__conga; [|apply out_trivial]; auto.
  }
  destruct (共线的决定性 B C Q) as [HCol5|HNCol5].
  { assert (Out B C Q).
      apply col_in_angle_out with A; auto; intro; apply HNCol; Col.
    apply 角度小于等于的交换性.
    exists P; split; trivial.
    apply out2__conga; [|apply out_trivial]; auto.
  }
  destruct (cop__one_or_two_sides B P A Q) as [HOS|HTS]; Col.
    apply 等价共面ACBD, coplanar_trans_1 with C; Cop; Col.
  - apply 角度小于等于的传递性 with P B C; [|apply 角度小于等于的交换性]; apply 角内点分角小于等于大角1; trivial.
    apply os2__inangle; apply invert_one_side.
      exists A; split; Side; apply 角端点在角内点与顶点连线两侧; Col.
    apply one_side_transitivity with A; [|apply one_side_symmetry];
    apply 角内点和一端点在角另一边同侧; Col.
  - apply 角度小于等于的传递性 with A B P; [apply 角度小于等于的右交换性|]; apply 角内点分角小于等于大角1; trivial.
    apply os2__inangle; trivial.
    apply invert_one_side, one_side_transitivity with C; [|apply one_side_symmetry];
    apply 角内点和一端点在角另一边同侧; Col.
Qed.

Lemma conga_inangle_per__acute : forall A B C P,
  Per A B C -> 在角内 P A B C -> 等角 P B A P B C ->
  为锐角 A B P.
Proof.
  intros A B C P HPer HP1 HP2.
  assert (Hd := 在角内推出点不重合 A B C P HP1); 分离合取式; clean.
  assert (HNCol : ~ Col A B C) by (apply 成直角三点不共线; auto).
  exists A, B, C; split; trivial.
  split.
    apply 角内点分角小于等于大角1, HP1.
  intro Habs.
  assert (Per A B P) by (apply l11_17_等于直角的角是直角 with A B C, 等角的对称性; trivial).
  apply HNCol, 等价共线BCA, cop_per2__col with P; Cop.
  apply l11_17_等于直角的角是直角 with A B P; trivial.
  apply 等角的交换性, HP2.
Qed.

Lemma conga_inangle2_per__acute : forall A B C P Q, Per A B C ->
  在角内 P A B C -> 等角 P B A P B C -> 在角内 Q A B C ->
  为锐角 P B Q.
Proof.
  intros A B C P Q HPer HP1 HP2 HQ.
  assert (HP' := l11_24_在角内的对称性 P A B C HP1).
  assert (HQ' := l11_24_在角内的对称性 Q A B C HQ).
  assert (Hd := 在角内推出点不重合 A B C P HP1);
  assert (Hd' := 在角内推出点不重合 A B C Q HQ);
  分离合取式; clean.
  assert (HNCol : ~ Col A B C) by (apply 成直角三点不共线; auto).
  assert (H为锐角 : 为锐角 A B P) by (apply conga_inangle_per__acute with C; assumption).
  assert (HNCol1 : ~ Col P B A).
    intro.
    assert (Col P B C) by (apply (共线三点构成的角的等角三点也共线 P B A); assumption).
    apply HNCol; ColR.
  assert (HNCol2 : ~ Col P B C) by (apply (不共线三点构成的角的等角三点也不共线 P B A); assumption).
  assert (~ Bet A B C) by (intro; apply HNCol; Col).
  destruct (共线的决定性 B A Q).
    assert (Out B A Q) by (apply col_in_angle_out with C; Col).
    apply (acute_conga__acute A B P); trivial.
    apply 等角的左交换性, out2__conga; [apply out_trivial|apply l6_6]; auto.
  destruct (共线的决定性 B C Q).
    assert (Out B C Q) by (apply col_in_angle_out with A; Between; Col).
    apply (acute_conga__acute A B P); trivial.
    apply 等角的左交换性, l11_10 with P A P C; try (apply out_trivial); auto.
    apply l6_6; assumption.
  destruct (共线的决定性 B P Q).
    apply 外共线零角为锐角, col_inangle2__out with A C; assumption.
  destruct (cop__one_or_two_sides B P A Q) as [HOS|HTS]; Col.
    apply 等价共面ACBD, coplanar_trans_1 with C; Cop; Col.
  - apply 小于等于锐角之角为锐角 with P B C.
      apply (acute_conga__acute A B P); try (apply 等角的左交换性); assumption.
    exists Q; split; [|apply 同角相等; auto].
    apply os2__inangle; apply invert_one_side.
      exists A; split; Side; apply 角端点在角内点与顶点连线两侧; Col.
    apply one_side_transitivity with A; [|apply one_side_symmetry];
    apply 角内点和一端点在角另一边同侧; Col.
  - apply 小于等于锐角之角为锐角 with A B P; trivial.
    apply 角度小于等于的交换性.
    exists Q; split; [|apply 角ABC等于角CBA; auto].
    apply os2__inangle; trivial.
    apply invert_one_side, one_side_transitivity with C; [|apply one_side_symmetry];
    apply 角内点和一端点在角另一边同侧; Col.
Qed.

Lemma lta_os__ts : forall A O B P, ~ Col A O P -> 角度小于 A O P A O B -> OS O A B P ->
  TS O P A B.
Proof.
intros.
unfold 角度小于 in *.
分离合取式.
unfold 角度小于等于 in *.
ex_and H0 P'.
assert(~Col A O B).
{
  unfold OS in H1.
  ex_and H1 R.
  unfold TS in H1.
  分离合取式; Col.
}
unfold TS.
repeat split; Col.
intro.
induction H5.
assert(TS O A B P).
{
  repeat split; Col.
  exists O.
  split; Col.
}
apply l9_9 in H6.
contradiction.
apply H2.
统计不重合点.
apply out2__conga.
apply out_trivial; auto.
repeat split; auto.
induction H5.
right; Between.
left; auto.
Between.
unfold 在角内 in *.
分离合取式.
ex_and H7 T.
exists T.
split; auto.
induction H8.
treat_equalities; Col.
assert(HCop : 共面 A O P P').
{
  apply coplanar_trans_1 with B; Col.
    Cop.
  exists T.
  left.
  split; Col.
}
assert(HH:= conga_cop__or_out_ts A O P P' HCop H3).
induction HH.
assert(Out O P T) by (apply (l6_7) with P'; finish).
Col.
exfalso.
assert(A <> T).
{
  intro.
  treat_equalities.
  unfold TS in H9.
  分离合取式.
  apply H9.
  Col.
}
assert(OS O A T P').
{
  apply out_one_side.
  left.
  intro.
  apply H4.
  ColR.
  auto.
}
assert(OS A O B T).
{
  apply out_one_side.
  left; Col.
  repeat split; auto.
  intro.
  treat_equalities.
  apply H4; Col.
}
assert(OS O A B P').
{
  apply (one_side_transitivity _ _ _  T); Side.
}
assert(TS O A B P) by (apply(l9_8_2 _ _ P'); Side).
apply l9_9 in H14.
contradiction.
Qed.


Lemma bet__suppa : forall A B C A', A <> B -> B <> C -> B <> A' -> Bet A B A' -> 互为补角 A B C C B A'.
Proof.
intros.
split; auto.
exists A'.
split; trivial.
apply 同角相等; auto.
Qed.

Lemma ex_suppa : forall A B C, A <> B -> B <> C -> exists D E F, 互为补角 A B C D E F.
Proof.
intros.
destruct (由一点往一方向构造等长线段 A B A B) as [A' []].
exists C, B, A'.
apply bet__suppa; auto.
intro; treat_equalities; auto.
Qed.

Lemma suppa_distincts : forall A B C D E F, 互为补角 A B C D E F ->
  A <> B /\ B <> C /\ D <> E /\ E <> F.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H0 A'.
apply conga_distinct in H1; 分离合取式.
repeat split; auto.
Qed.

Lemma suppa_right_comm : forall A B C D E F, 互为补角 A B C D E F -> 互为补角 A B C F E D.
Proof.
unfold 互为补角.
intros; 分离合取式.
split; auto.
ex_and H0 A'.
exists A'.
split; auto.
apply 等角的左交换性, H1.
Qed.

Lemma suppa_left_comm : forall A B C D E F, 互为补角 A B C D E F -> 互为补角 C B A D E F.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H0 A'.
apply conga_distinct in H1.
分离合取式.
split; auto.
destruct (由一点往一方向构造等长线段 C B C B) as [C' []].
exists C'.
split; auto.
apply 角等的传递性 with C B A'; trivial.
统计不重合点.
apply 等角的左交换性, l11_14; Between.
Qed.

Lemma suppa_comm : forall A B C D E F, 互为补角 A B C D E F -> 互为补角 C B A F E D.
Proof.
intros.
apply suppa_left_comm, suppa_right_comm, H.
Qed.

Lemma suppa_sym : forall A B C D E F, 互为补角 A B C D E F -> 互为补角 D E F A B C.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H0 A'.
apply conga_distinct in H1; 分离合取式.
split; auto.
destruct (由一点往一方向构造等长线段 D E D E) as [D' []].
exists D'.
split; auto.
统计不重合点.
apply 等角的右交换性, l11_13 with A' D; Between.
apply 等角的对称性, 等角的右交换性, H1.
Qed.

Lemma conga2_suppa__suppa : forall A B C D E F A' B' C' D' E' F',
  等角 A B C A' B' C' -> 等角 D E F D' E' F' -> 互为补角 A B C D E F ->
  互为补角 A' B' C' D' E' F'.
Proof.
intros.
assert (互为补角 A B C D' E' F').
{
  unfold 互为补角 in *; 分离合取式.
  split; auto.
  ex_and H2 A0.
  exists A0.
  split; trivial.
  apply 角等的传递性 with D E F; [apply 等角的对称性|]; assumption.
}
apply suppa_sym.
apply suppa_sym in H2.
unfold 互为补角 in H2; 分离合取式.
split; auto.
ex_and H3 D0.
exists D0.
split; trivial.
apply 角等的传递性 with A B C; [apply 等角的对称性|]; assumption.
Qed.

Lemma suppa2__conga456 : forall A B C D E F D' E' F',
  互为补角 A B C D E F -> 互为补角 A B C D' E' F' -> 等角 D E F D' E' F'.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H2 A'.
ex_and H1 A''.
apply 角等的传递性 with C B A'; trivial.
apply 角等的传递性 with C B A''; [|apply 等角的对称性, H4].
apply conga_distinct in H3.
apply conga_distinct in H4.
分离合取式.
apply out2__conga.
  apply out_trivial; auto.
  apply l6_2 with A; Between.
Qed.

Lemma suppa2__conga123 : forall A B C D E F A' B' C',
  互为补角 A B C D E F -> 互为补角 A' B' C' D E F -> 等角 A B C A' B' C'.
Proof.
intros.
apply (suppa2__conga456 D E F); apply suppa_sym; assumption.
Qed.

Lemma bet_out__suppa : forall A B C D E F, A <> B -> B <> C ->
  Bet A B C -> Out E D F -> 互为补角 A B C D E F.
Proof.
intros.
split; auto.
exists C.
split; auto.
apply l11_21_b; trivial.
apply out_trivial; auto.
Qed.

Lemma bet_suppa__out : forall A B C D E F,
  Bet A B C -> 互为补角 A B C D E F -> Out E D F.
Proof.
intros.
assert (Hd := H0).
apply suppa_distincts in Hd; 分离合取式.
apply (l11_21_a C B C).
  apply out_trivial; auto.
apply (suppa2__conga456 A B C); trivial.
split; auto.
exists C.
split; trivial.
apply 同角相等; auto.
Qed.

Lemma out_suppa__bet : forall A B C D E F,
  Out B A C -> 互为补角 A B C D E F -> Bet D E F.
Proof.
intros.
destruct (由一点往一方向构造等长线段 A B A B) as [B' []].
apply (零角的等角是零角 A B B'); trivial.
apply (suppa2__conga456 A B C); trivial.
统计不重合点.
apply suppa_sym, bet_out__suppa; auto.
Qed.

Lemma per_suppa__per : forall A B C D E F,
  Per A B C -> 互为补角 A B C D E F -> Per D E F.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H1 A'.
apply (l11_17_等于直角的角是直角 C B A'); [|apply 等角的对称性, H2].
apply conga_distinct in H2; 分离合取式.
apply 直角边共线点也构成直角2 with A; Perp; Col.
Qed.

Lemma per2__suppa : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
  Per A B C -> Per D E F -> 互为补角 A B C D E F.
Proof.
intros.
destruct (ex_suppa A B C) as [D' [E' [F']]]; auto.
apply (conga2_suppa__suppa A B C D' E' F'); try apply 同角相等; auto.
assert (Hd := H5).
apply suppa_distincts in Hd; 分离合取式.
apply l11_16_直角相等; auto.
apply (per_suppa__per A B C); assumption.
Qed.

Lemma suppa__per : forall A B C, 互为补角 A B C A B C -> Per A B C.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H0 A'.
apply 直角的对称性, l11_18_2 with A'; trivial.
apply 等角的左交换性, H1.
Qed.

Lemma acute_suppa__obtuse : forall A B C D E F,
  为锐角 A B C -> 互为补角 A B C D E F -> 为钝角 D E F.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H1 A'.
apply (conga_obtuse__obtuse C B A'); [|apply 等角的对称性, H2].
apply conga_distinct in H2; 分离合取式.
apply 为钝角的对称性, (acute_中间性平角为钝角 A); auto.
Qed.

Lemma obtuse_suppa__acute : forall A B C D E F,
  为钝角 A B C -> 互为补角 A B C D E F -> 为锐角 D E F.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H1 A'.
apply (acute_conga__acute C B A'); [|apply 等角的对称性, H2].
apply conga_distinct in H2; 分离合取式.
apply 为锐角的对称性, (bet_obtuse__acute A); auto.
Qed.

Lemma lea_suppa2__lea : forall A B C D E F A' B' C' D' E' F',
  互为补角 A B C A' B' C' -> 互为补角 D E F D' E' F' -> 角度小于等于 A B C D E F ->
  角度小于等于 D' E' F' A' B' C'.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H3 A0.
ex_and H2 D0.
apply (l11_30_等角保持小于等于 F E D0 C B A0); [|apply 等角的对称性; assumption..].
apply conga_distinct in H4.
apply conga_distinct in H5.
分离合取式.
apply 角度小于等于的交换性, l11_36_双补角组中的角度偏序 with D A; Between.
Qed.

Lemma lta_suppa2__lta : forall A B C D E F A' B' C' D' E' F',
  互为补角 A B C A' B' C' -> 互为补角 D E F D' E' F' -> 角度小于 A B C D E F ->
  角度小于 D' E' F' A' B' C'.
Proof.
unfold 互为补角.
intros; 分离合取式.
ex_and H3 A0.
ex_and H2 D0.
apply (等角保持角度小于性质 F E D0 C B A0); [apply 等角的对称性; assumption..|].
apply conga_distinct in H4.
apply conga_distinct in H5.
分离合取式.
apply 角度小于的交换性, bet2_lta__lta with A D; Between.
Qed.

Lemma suppa_dec : forall A B C D E F, 互为补角 A B C D E F \/ ~ 互为补角 A B C D E F.
Proof.
intros.
induction (两点重合的决定性 A B).
  right; intros []; auto.
induction (两点重合的决定性 B C).
  right; intro Habs; apply suppa_distincts in Habs; 分离合取式; auto.
destruct (ex_suppa A B C) as [D' [E' [F']]]; auto.
induction (等角的决定性 D' E' F' D E F).
  left; apply (conga2_suppa__suppa A B C D' E' F'); try apply 同角相等; auto.
  right; intro; apply H2, (suppa2__conga456 A B C); assumption.
Qed.

End T11_2.

Ltac not_exist_hyp4 A B C D E F G H := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H].

Ltac not_exist_hyp5 A B C D E F G H I J := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H | not_exist_hyp_comm I J].

Ltac not_exist_hyp6 A B C D E F G H I J K L := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H | not_exist_hyp_comm I J | not_exist_hyp_comm K L].

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

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 角等推AB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= 角等推CB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= 角等推DE不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= 角等推FE不重合 A B C A' B' C' H);clean_reap_hyps

      | H:(在角内 ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := 在角内推出点不重合 A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于等于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于等于推出点不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于推不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为锐角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为锐角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为钝角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为钝角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:互为补角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(垂直平面于 ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; 统计不重合点; Col_refl tpoint col.

Hint Resolve 同角相等 等角的对称性 三角形全等推角等1 角ABC等于角CBA 角ABA等于角CDC
             等角的右交换性 等角的左交换性 等角的交换性 成中间性三点组的角相等 l11_16_直角相等 : conga.

Ltac 等角 := auto 3 with conga.

Hint Resolve l11_31_1_任何角小于等于平角_Out表述 l11_31_1_任何角小于等于平角_Bet表述 角度小于蕴含角度小于等于 角度小于等于的交换性 角度小于等于的右交换性 角度小于等于的左交换性 角度小于的交换性
             角度小于的右交换性 角度小于的左交换性 双角度偏序推等角 零角小于等于任何角 角内点分角小于等于大角1 角内点分角小于等于大角2
             等角小于等于自己 等角小于等于自己_交换 任何角小于等于自己 acute_per__lta obtuse_per__lta acute_obtuse__lta : lea.

Ltac Lea := auto 3 with lea.

Hint Resolve l11_24_在角内的对称性 out321__inangle out341__inangle A在角ABC内 C在角ABC内 任何点都在平角内
             ts2__inangle os_ts__inangle os2__inangle : side.

Section T11_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma acute_one_side_aux : forall P A O B,
 OS O A P B -> 为锐角 A O P -> Perp O A B O ->
 OS O B A P.
Proof.
intros P A O B HOS.
intros.
unfold 为锐角 in H.
ex_and H A'.
ex_and H1 B'.
ex_and H C'.

assert(Per A O B).
{
  apply L形垂直转垂直于 in H0.
  apply 垂直于的交换性 in H0.
  apply L形垂直于转直角 in H0.
  assumption.
}
assert(等角 A' B' C' A O B).
{
  统计不重合点.
  apply l11_16_直角相等; auto.
}
assert(角度小于 A O P A O B).
{
  apply(等角保持角度小于性质 A O P A' B' C' A O P A O B); auto.
  统计不重合点.
  apply 同角相等; auto.
}

assert(~Col P O B).
{
  intro.
  assert(Per A O P).
  {
    统计不重合点.
    apply (直角边共线点也构成直角2 A O B P); Col.
  }
  unfold 角度小于 in H4.
  分离合取式.
  apply H7.
  统计不重合点.
  apply(l11_16_直角相等); auto.
}

assert(NC:~Col A O P).
{
  unfold OS in HOS.
  ex_and HOS R.
  unfold TS in H6.
  分离合取式.
  Col.
}

assert(TS O B A P \/ OS O B A P).
{
  apply(cop__one_or_two_sides O B A P); Cop.
  apply L形垂直推出不共线 in H0; Col.
}
induction H6.
unfold TS in H6.
分离合取式.
ex_and H8 T.

assert(O <> T).
{
  intro.
  treat_equalities.
  assert(角度小于等于 A O B A O P).
  {
    统计不重合点.
    apply(l11_31_1_任何角小于等于平角_Bet表述 A O B A O P); auto.
  }
  assert(~角度小于 A O P A O B).
  {
    apply 两角成偏序关系则不可能成反全序关系.
    assumption.
  }
  contradiction.
}

assert(在角内 T A O P).
{
  unfold 在角内.
  统计不重合点.
  repeat split; auto.
  exists T.
  split; auto.
  right.
  finish.
}


assert(OS O A T P).
{
  apply invert_one_side.
  apply out_one_side.
  right; Col.
  统计不重合点.
  repeat split; auto.
  apply L形垂直推出不共线 in H0.
  intro;  treat_equalities.
  apply H0; Col.
}

assert(OS O A T B).
{
  apply (one_side_transitivity _ _ _ P); auto.
}

destruct(l9_19 O A T B O); Col.
apply H14 in H13.
分离合取式.
assert(在角内 B A O P).
{
  统计不重合点.
  apply(l11_25 T A O P A P B H11); auto;
  try(apply out_trivial; auto).
  apply l6_6; auto.
}

apply 角内点分角小于等于大角1 in H17.

apply 两角成偏序关系则不可能成反全序关系 in H17.
contradiction.
assumption.
Qed.

Lemma acute_one_side_aux0 : forall P A O B, Col A O P -> 为锐角 A O P -> Perp O A B O -> OS O B A P.

Proof.
intros.
assert(角度小于 A O P A O B).
{
  统计不重合点.
  apply(acute_per__lta A O P A O B H0); auto.
  apply L形垂直转垂直于 in H1.
  apply 垂直于的交换性 in H1.
  apply L形垂直于转直角 in H1.
  assumption.
}

assert(Out O A P).
{
  统计不重合点.
  induction H.
  assert(角度小于等于 A O B A O P).
  {
    apply l11_31_1_任何角小于等于平角_Bet表述; auto.
  }
  apply 两角成偏序关系则不可能成反全序关系 in H3.
  contradiction.
  repeat split; auto.
  induction H.
  right; Between.
  left; Between.
}

apply(out_one_side O B A P); auto.
left.
apply L形垂直推出不共线 in H1.
Col.
Qed.

Lemma acute_cop_perp__one_side :
  forall P A O B, 为锐角 A O P -> Perp O A B O -> 共面 A B O P -> OS O B A P.

Proof.
intros.
induction(共线的决定性 A O P).
apply(acute_one_side_aux0); auto.
assert(~Col A O B).
{
  apply L形垂直推出不共线 in H0.
  Col.
}
assert(TS O A P B \/ OS O A P B).
{
  apply(cop__one_or_two_sides O A P B); Col.
  Cop.
}

induction H4.
assert(HC:=构造对称点 B O).
ex_and HC Bs.
unfold 中点 in *.
分离合取式.
assert(TS O A Bs B).
{
  repeat split; Col.
  intro.
  apply H3.
  ColR.
  exists O.
  split; [Col|Between].
}
assert(OS O A P Bs).
{
  apply(l9_8_1 _ _ _ _ B); auto.
}
assert(Perp O A Bs O ).
{
  apply 垂直的对称性.
  apply 垂直的交换性.
  apply (垂线共线点也构成垂直1 _ B); Perp.
  intro.
  treat_equalities.
  apply H3; Col.
  Col.
}
assert(OS O Bs A P).
{
  apply(acute_one_side_aux P A O Bs); auto.
}
apply(col_one_side _ Bs); Col.
intro.
treat_equalities.
apply H3; Col.

apply(acute_one_side_aux P A O B); auto.
Qed.

Lemma acute__not_obtuse : forall A B C, 为锐角 A B C -> ~ 为钝角 A B C.
Proof.
intros A B C HA HO.
apply (一角不可能小于自己 A B C), acute_obtuse__lta; assumption.
Qed.

End T11_3.