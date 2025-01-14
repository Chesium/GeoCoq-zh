Require Export GeoCoq.Tarski_dev.Ch05_bet_le.

Ltac eCol := eauto with col.

Section T6_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma bet_out : forall A B C, B <> A -> Bet A B C -> Out A B C.
Proof.
    intros.
    unfold Out.
    repeat split; auto.
    intro; treat_equalities; auto.
Qed.

Lemma bet_out_1 : forall A B C, B <> A -> Bet C B A -> Out A B C.
Proof.
    intros.
    apply bet_out; Between.
Qed.

Lemma out_dec : forall P A B, Out P A B \/ ~ Out P A B.
Proof.
    intros.
    unfold Out.
    elim (中间性的决定性 P A B);intro; elim (中间性的决定性 P B A);intro; elim (两点重合的决定性 A P);intro; elim (两点重合的决定性 B P);intro; tauto.
Qed.

Lemma out_diff1 : forall A B C, Out A B C -> B <> A.
Proof.
    intros.
    unfold Out in H.
    分离合取式.
    assumption.
Qed.

Lemma out_diff2 : forall A B C, Out A B C -> C <> A.
Proof.
    intros.
    unfold Out in H.
    分离合取式.
    assumption.
Qed.

Lemma out_distinct : forall A B C, Out A B C -> B <> A /\ C <> A.
Proof.
    intros.
    split.
      eapply out_diff1;eauto.
    eapply out_diff2;eauto.
Qed.

Lemma out_col : forall A B C, Out A B C -> Col A B C.
Proof.
    intros.
    unfold Col.
    unfold Out in H.
    分离合取式.
    induction H1;Between.
Qed.

Lemma l6_2 : forall A B C P,  A<>P -> B<>P -> C<>P -> Bet A P C -> (Bet B P C <-> Out P A B).
Proof.
    intros.
    unfold Out.
    split.
      intros.
      repeat split; try assumption; eapply l5_2;eBetween.
    intro; 分离合取式; induction H5; eBetween.
Qed.

Lemma bet_out__bet : forall A B C P, Bet A P C -> Out P A B -> Bet B P C.
Proof.
    intros A B C P HBet HOut.
    destruct (两点重合的决定性 C P).
      subst; Between.
    apply (l6_2 A); trivial; destruct HOut as [HPA [HPB]]; auto.
Qed.

Lemma l6_3_1 : forall A B P, Out P A B -> (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C).
Proof.
    unfold Out.
    intros.
    分离合取式.
    repeat split; try assumption.
    induction H1.
      assert(exists C, Bet A P C /\ P <> C) by (apply 构造满足中间性的不重合点).
      ex_and H2 C.
      exists C.
      repeat split; eBetween.
    assert(exists C, Bet B P C /\ P <> C) by (apply 构造满足中间性的不重合点).
    ex_and H2 C.
    exists C.
    repeat split;eBetween.
Qed.

Lemma l6_3_2 : forall A B P,
  (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C) -> Out P A B.
Proof.
    intros.
    分离合取式.
    ex_and H1 C.
    unfold Out.
    repeat split; try assumption; eapply l5_2; eBetween.
Qed.

Lemma l6_4_1 : forall A B P, Out P A B -> Col A P B /\ ~ Bet A P B.
Proof.
    unfold Out.
    intros.
    分离合取式.
    unfold Col.
    induction H1; split.
      Between.
      intro; apply H; eapply 双中间性推出点重合;eauto.
      right; left; assumption.
    intro; apply H0; eapply 双中间性推出点重合; eBetween.
Qed.

Lemma l6_4_2 : forall A B P, Col A P B /\ ~ Bet A P B -> Out P A B.
Proof.
    unfold Col.
    intros.
    分离合取式.
    unfold Out.
    induction H.
      contradiction.
    induction (两点重合的决定性 A P).
      subst P; intuition.
    induction (两点重合的决定性 B P).
      subst P; intuition.
    induction H; repeat split; Between.
Qed.

(** out reflexivity. l6_5 *)

Lemma out_trivial : forall P A, A<>P -> Out P A A.
Proof.
    intros.
    unfold Out.
    repeat split; Between.
Qed.

(** out symmetry. *)

Lemma l6_6 : forall P A B, Out P A B -> Out P B A.
Proof.
    unfold Out.
    intuition.
Qed.

(** out transitivity. *)

Lemma l6_7 : forall P A B C, Out P A B -> Out P B C -> Out P A C.
Proof.
    unfold Out.
    intros.
    分离合取式.
    repeat split; try assumption.
    induction H4; induction H2.
      left; eapply 中间性的交换传递性2; eauto.
      eapply l5_3; eauto.
      eapply (l5_1 P B); auto.
    right; eBetween.
Qed.

Lemma bet_out_out_bet : forall A B C A' C',
 Bet A B C -> Out B A A' -> Out B C C' -> Bet A' B C'.
Proof.
    intros.
    unfold Out in *.
    分离合取式.
    induction H5; induction H3.
      assert(Bet A' B C) by (apply 中间性的外传递性1 with A; Between).
      apply 中间性的外传递性2 with C; auto.
      assert(Bet A' B C) by (apply 中间性的外传递性1 with A; Between).
      apply 中间性的内传递性1 with C; assumption.
      assert(Bet A' B C) by (apply 中间性的交换传递性1 with A; Between).
      apply 中间性的外传递性2 with C; auto.
    assert(Bet A' B C) by (apply 中间性的交换传递性1 with A; Between).
    eapply 中间性的内传递性1 with C; assumption.
Qed.

Lemma out2_bet_out : forall A B C X P,
 Out B A C -> Out B X P -> Bet A X C -> Out B A P /\ Out B C P.
Proof.
    intros.
    unfold Out in *.
    分离合取式.
    induction H5; induction H3.
      repeat split; try assumption.
        left; eapply 中间性的交换传递性2 with X; try assumption.
        apply 中间性的内传递性1 with C; assumption.
      apply l5_1 with X; try auto.
      apply 中间性的内传递性2 with A; assumption.
      repeat split; try assumption.
        apply l5_3 with X; try assumption.
        apply 中间性的内传递性1 with C; assumption.
      right; apply 中间性的交换传递性2 with X; try assumption.
      apply 中间性的内传递性2 with A; assumption.
      repeat split; try assumption.
        apply l5_1 with X; try auto.
        apply 中间性的内传递性2 with C; Between.
      left; apply 中间性的交换传递性2 with X; try assumption.
      apply 中间性的内传递性1 with A; Between.
    repeat split; try assumption.
      right; apply 中间性的交换传递性2 with X; try assumption.
      apply 中间性的内传递性2 with C; Between.
    apply l5_3 with X; try assumption.
    apply 中间性的内传递性1 with A; Between.
Qed.

Lemma l6_11_uniqueness : forall A B C R X Y,
  Out A X R -> Cong A X B C ->
  Out A Y R -> Cong A Y B C ->
  X=Y.
Proof.
    unfold Out.
    intros.
    分离合取式.
    assert (Cong A X A Y) by CongR.
    induction H6; induction H4.
      apply l4_19 with A R; try assumption.
      apply l4_3 with A A; Between; Cong.
      assert (Bet A X Y) by eBetween.
      eapply between_cong; eauto.
      assert (Bet A Y X) by eBetween.
      apply sym_equal; apply between_cong with A; Cong.
    assert (Bet A X Y \/ Bet A Y X) by (eapply l5_1; eauto).
    induction H8.
      apply between_cong with A; assumption.
    apply sym_equal; apply between_cong with A; Cong.
Qed.

Lemma l6_11_existence : forall A B C R,
  R<>A -> B<>C -> exists X, Out A X R /\ Cong A X B C.
Proof.
    intros.
    assert (exists X : Tpoint, (Bet A R X \/ Bet A X R) /\ Cong A X B C) by (apply (由一点往一方向构造等长线段_2);assumption).
    ex_and H1 X.
    exists X.
    unfold Out;repeat split; try intro;treat_equalities;intuition.
Qed.

Lemma 由一点往一方向构造等长线段_3 : forall A B X Y, A <> B -> X <> Y -> exists C, Out A B C /\ Cong A C X Y.
Proof.
    intros.
    destruct (l6_11_existence A X Y B) as [C [HC1 HC2]]; auto.
    apply l6_6 in HC1.
    exists C; auto.
Qed.

Lemma l6_13_1 : forall P A B, Out P A B -> Le
 P A P B -> Bet P A B.
Proof.
    unfold Out.
    intros.
    分离合取式.
    induction H2; try assumption.
    unfold Le
 in H0.
    ex_and H0 Y.
    assert(Y = A).
      apply (l6_11_uniqueness P P A B); Between; Cong.
        unfold Out; repeat split; auto.
        intro; treat_equalities; auto.
      unfold Out; repeat split; auto.
    subst Y; assumption.
Qed.

Lemma l6_13_2 : forall P A B, Out P A B -> Bet P A B -> Le
 P A P B.
Proof.
    intros.
    unfold Le.
    exists A.
    split; Cong.
Qed.

Lemma 共线的传递性1 : forall P Q S X, P<>Q -> Col S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    destruct (两点重合的决定性 S P).
      subst; Col.
    assert((Bet P S X \/ Bet P X S) -> (Bet P S X \/ Bet S X P)) by (intro; induction H3; Between).
    unfold Col.
    induction H0;induction H1.
      right; apply H3; eapply (l5_2 Q P); Between.
      induction H1; left; eBetween.
      induction H0; left; eBetween.
    induction H0; induction H1.
      right; apply H3; eapply l5_1; eauto.
      right; right; eBetween.
      right; left; eBetween.
    right; apply H3; eapply l5_3; eBetween.
Qed.

Lemma 共线的传递性2 : forall P Q A B,
  P<>Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof.
    intros.
    induction (两点重合的决定性 A P).
      subst; unfold Col; Between.
    assert (T:=共线的传递性1 P Q A B).
    apply 等价共线BCA; apply T; Col.
Qed.

Lemma 共线的传递性3 : forall P Q A B,
 P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof.
    intros.
    apply (共线的传递性2 Q P A B);Col.
Qed.

(** Unicity of intersection *)

Lemma l6_21_两线交点的唯一性 : forall A B C D P Q,
  ~ Col A B C -> C<>D -> Col A B P -> Col A B Q -> Col C D P -> Col C D Q -> P=Q.
Proof.
    intros.
    elim (两点重合的决定性 P Q); intro; try assumption.
    cut False.
      intro; intuition.
    apply 不共线则不重合 in H.
    分离合取式.
    assert (Col C P Q) by (apply 共线的传递性2 with D; Col).
    assert (Col Q B C).
      induction (两点重合的决定性 Q A).
        subst; apply 共线的传递性2 with P; Col.
      apply 共线的传递性2 with P; Col; apply 等价共线BCA, 共线的传递性2 with A; Col.
    assert (Col A B C).
      induction (两点重合的决定性 Q A).
        subst Q; assumption.
      induction (两点重合的决定性 Q B).
        subst; apply 等价共线CAB; apply 共线的传递性2 with P; Col.
      apply 等价共线CAB; apply 共线的传递性2 with Q; Col.
    contradiction.
Qed.
(* 无用？ *)
Lemma col2__eq : forall A B X Y,
  Col A X Y -> Col B X Y -> ~ Col A X B ->
  X = Y.
Proof.
    intros.
    apply l6_21_两线交点的唯一性 with A X B X; Col.
    intro; subst; Col.
Qed.

End T6_1.

Hint Resolve 共线的传递性2 共线的传递性3 out_col : col.

Section T6_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** This is l6_25 of Tarski *)
Lemma 两点不重合则存在不共线的点 : forall A B,
 A<>B -> exists C, ~ Col A B C.
Proof.
    intros.
    assert (T:=防降维公理_老版本).
    induction T.
    induction H0.
    induction H0.
    induction (共线的决定性 A B x).
      induction(共线的决定性 A B x0).
        induction(共线的决定性 A B x1).
          induction (两点重合的决定性 A x).
            assert (~(Col x x0 x1)) by (unfold Col; auto).
            treat_equalities; eCol.
          assert (Col A x x0)  by eCol.
          assert (Col A x x1)  by eCol.
          assert (Col A x0 x1) by eCol.
          assert (Col x x0 x1) by eCol.
          contradiction.
        exists x1; assumption.
      exists x0; assumption.
    exists x; assumption.
Qed.

(*
Lemma t2_8 : forall A B C D E : Tpoint,
 Bet A B C -> Bet D B E -> Cong A B D B -> Cong B C B E -> Cong A E C D.
Proof.
    intros.
    induction (两点重合的决定性 A B); try (treat_equalities; Cong).
    assert (Cong A B D B -> Cong B C B E -> Cong A D D A -> Cong B D B A -> Bet A B C -> Bet D B E -> A <> B -> Cong C D E A).
      apply 五线段公理_等价SAS.
    apply 等长的对称性.
    apply 等长的右交换性.
    apply H4; Cong; Between.
Qed.
*)

Lemma 共线的传递性4 : forall X Y A B C,
 X <> Y ->
 Col X Y A -> Col X Y B -> Col X Y C ->
 Col A B C.
Proof.
    intros.
    assert (Col X A B) by (apply 共线的传递性2 with Y; assumption).
    induction(两点重合的决定性 C X).
      subst X; apply 等价共线BCA; assumption.
    apply 等价共线BCA.
    apply 共线的传递性2 with X; try assumption.
      apply 等价共线CAB.
      apply 共线的传递性2 with Y; assumption.
    apply 等价共线CAB.
    apply 共线的传递性2 with Y; assumption.
Qed.

Lemma 共线的传递性5 : forall A B C X Y, A <> B -> Col X Y A -> Col X Y B -> Col A B C -> Col X Y C.
Proof.
    intros.
    destruct (两点重合的决定性 X Y).
      subst; Col.
    apply (共线的传递性4 A B); auto; apply 等价共线BCA.
      apply 共线的传递性2 with Y; Col.
      apply (共线的传递性3 X); Col.
Qed.

Lemma out2__bet : forall A B C, Out A B C -> Out C A B -> Bet A B C.
Proof.
    intros A B C Hout1 Hout2.
    apply l6_4_1 in Hout2.
    destruct Hout2 as [_ Hout2].
    destruct Hout1 as [_ [_ [|]]].
    assumption.
    exfalso.
    apply Hout2.
    assumption.
Qed.

Lemma bet2_le2__le1346 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le
 A B A' B' -> Le
 B C B' C' ->
  Le
 A C A' C'.
Proof.
  intros A B C A' B' C' HBet HBet' HleAB HleBC.

  elim(两点重合的决定性 A B).
  { intro.
    subst B.
    apply (长度小于等于的传递性 _ _ B' C'); auto.
    apply 长度小于等于的交换性.
    exists B'.
    split; Between; Cong.
  }
  intro.
  elim(两点重合的决定性 B C).
  { intro.
    subst C.
    apply (长度小于等于的传递性 _ _ A' B'); auto.
    exists B'; Cong.
  }
  intro.

  assert(A' <> B') by (intro; subst B'; assert(A = B); auto; apply (AB小于等于CC推出A与B重合 _ _ A'); auto).
  assert(B' <> C') by (intro; subst C'; assert(B = C); auto; apply (AB小于等于CC推出A与B重合 _ _ B'); auto).
  destruct HleAB as [B0 []].
  assert(A' <> B0) by (intro; subst B0; assert(A = B); auto; apply (等长的反向同一性 A'); Cong).
  assert(HC0 := 由一点往一方向构造等长线段 A' B0 B C).
  destruct HC0 as [C0 []].
  assert(B0 <> C0) by (intro; subst C0; assert(B = C); auto; apply (等长的反向同一性 B0); auto).
  exists C0.
  split; [|apply (两组连续三点分段等则全体等 _ B _ _ B0); Cong].
  apply (中间性的外传递性1 _ B0); auto.
  assert(Bet B0 B' C') by (apply 中间性的对称性; apply (中间性的内传递性1 _ _ _ A'); Between).
  apply l6_13_1.
  - elim(两点重合的决定性 B0 B').
    { intro.
      subst.
      apply (l6_2 _ _ A'); Between.
    }
    intro.
    apply (l6_7 _ _ B').
    apply (l6_2 _ _ A'); Between.
    apply bet_out; auto.
  - apply (长度小于等于的传递性 _ _ B' C').
      apply (l5_6_等长保持小于等于关系 B C B' C'); Cong.
      apply 长度小于等于的交换性.
      exists B'.
      split; Between; Cong.
Qed.

Lemma bet2_le2__le2356 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' ->
  Le A B A' B' -> Le A' C' A C -> Le B' C' B C.
Proof.
  intros A B C A' B' C' HBet HBet' HLe1 HLe2.
  elim(两点重合的决定性 A B).
  { intro; treat_equalities.
    apply (长度小于等于的传递性 _ _ A' C'); auto.
    destruct (l5_12_a A' B' C'); auto.
  }
  intro.
  assert (A<>C) by (intro; treat_equalities; auto).
  destruct (l5_5_1 A B A' B' HLe1) as [B0 [HBet1 HCong1]].
  assert (A<>B0) by (intro; treat_equalities; auto).
  destruct HLe2 as [C0 [HBet2 HCong2]].
    assert (A<>C0) by (intro; treat_equalities; auto).
  assert (Bet A B0 C0).
  { apply l6_13_1.
      apply (l6_7 _ _ B); [|apply (l6_7 _ _ C)]; [apply l6_6| |apply l6_6]; apply bet_out; auto.
    apply (l5_6_等长保持小于等于关系 A' B' A' C'); Cong.
    destruct (l5_12_a A' B' C'); auto.
  }
  apply (l5_6_等长保持小于等于关系 B0 C0 B C); Cong; [apply (长度小于等于的传递性 _ _ B C0)|].
    destruct (l5_12_a B B0 C0); eBetween.
    destruct (l5_12_a B C0 C); eBetween.
    apply 等长的交换性; apply (l4_3 _ _ A _ _ A'); Between; Cong.
Qed.

Lemma bet2_le2__le1245 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' ->
  Le B C B' C' -> Le A' C' A C -> Le A' B' A B.
Proof.
  intros A B C A' B' C'; intros.
  apply 长度小于等于的交换性.
  apply (bet2_le2__le2356 C _ _ C'); Le; Between.
Qed.

Lemma cong_preserves_bet : forall B A' A0 E D' D0,
  Bet B A' A0 -> Cong B A' E D' -> Cong B A0 E D0 -> Out E D' D0 ->
  Bet E D' D0.
Proof.
    intros.
    unfold Out in H2.
    分离合取式.
    induction H4.
      assumption.
    assert (Le
 E D0 E D').
      eapply l5_5_2.
      exists D'.
      split.
        assumption.
      Cong.
    assert(Le
 E D' E D0).
      apply (l5_6_等长保持小于等于关系 B A' B A0); trivial.
      apply l5_5_2.
      exists A0.
      split.
        assumption.
      Cong.
    assert(Cong E D' E D0).
      apply 长度小于等于的反对称性.
        assumption.
      assumption.
    assert(D0 = D').
      eapply between_cong.
        apply H4.
      Cong.
    subst D'.
    Between.
Qed.

Lemma out_cong_cong : forall B A A0 E D D0,
 Out B A A0 -> Out E D D0 ->
 Cong B A E D -> Cong B A0 E D0 ->
 Cong A A0 D D0.
Proof.
    intros.
    unfold Out in H.
    分离合取式.
    induction H4.
      assert (Bet E D D0).
        apply (cong_preserves_bet B A A0); assumption.
      apply 等长的交换性.
      eapply l4_3.
        apply 中间性的对称性.
        apply H4.
        apply 中间性的对称性.
        apply H5.
        Cong.
      Cong.
    assert (Bet E D0 D).
      apply (cong_preserves_bet B A0 A); trivial.
      apply l6_6.
      assumption.
    eapply l4_3;eBetween;Cong.
Qed.

Lemma not_out_bet : forall A B C, Col A B C -> ~ Out B A C -> Bet A B C.
Proof.
    intros.
    unfold Out in H0.
    induction (两点重合的决定性 A B).
      subst.
      Between.
    induction (两点重合的决定性 B C).
      subst.
      Between.
    unfold Col in *.
    decompose [or] H;clear H.
      assumption.
      exfalso.
      apply H0.
      intuition.
    exfalso.
    apply H0.
    intuition.
Qed.

Lemma or_bet_out : forall A B C, Bet A B C \/ Out B A C \/ ~Col A B C.
Proof.
    intros.
    destruct (共线的决定性 A B C); auto.
    destruct (out_dec B A C); auto.
    left; apply not_out_bet; trivial.
Qed.

Lemma not_bet_out : forall A B C,
 Col A B C -> ~Bet A B C -> Out B A C.
Proof.
    intros.
    destruct (or_bet_out A B C) as [HBet|[HOut|HNCol]]; trivial; contradiction.
Qed.

Lemma not_bet_and_out :
 forall A B C,
 ~ (Bet A B C /\ Out B A C).
Proof.
    intros.
    intro.
    分离合取式.
    unfold Out in H0.
    分离合取式.
    induction H2.
      assert ( A = B).
        eapply 双中间性推出点重合.
          apply H.
        assumption.
      contradiction.
    assert(C = B).
      eapply 双中间性推出点重合.
        apply 中间性的对称性.
        apply H.
      assumption.
    contradiction.
Qed.

Lemma out_to_bet :
 forall A B C A' B' C',
  Col A' B' C' ->
 (Out B A C <-> Out B' A' C') ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    induction(out_dec B A C).
      unfold Out in H2.
      分离合取式.
      induction H4.
        assert( A = B).
          eapply 双中间性推出点重合.
            apply H1.
          assumption.
        contradiction.
      assert(C = B).
        apply(中间性的对称性) in H4.
        eapply 双中间性推出点重合.
          apply 中间性的对称性.
          apply H1.
        apply 中间性的对称性.
        assumption.
      contradiction.
    destruct H0.
    assert (~Out B' A' C').
      intro.
      apply H2.
      apply H3.
      assumption.
    apply not_out_bet.
      assumption.
    assumption.
Qed.

Lemma col_out2_col  : forall A B C AA CC, Col A B C -> Out B A AA -> Out B C CC -> Col AA B CC.
Proof.
    intros.
    induction H.
      assert (Bet AA B CC).
        eapply bet_out_out_bet.
          apply H.
          assumption.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert(Out B AA CC).
        eapply l6_7.
          eapply l6_6.
          apply H0.
        apply l6_6.
        eapply l6_7.
          apply l6_6.
          apply H1.
        apply bet_out.
          unfold Out in *.
          分离合取式.
          assumption.
          unfold Out in *.
          分离合取式.
          assumption.
      apply 等价共线BAC.
      apply out_col.
      assumption.
    assert(Out B AA CC).
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H1.
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H0.
      apply bet_out.
        unfold Out in *.
        分离合取式.
        assumption.
        unfold Out in *.
        分离合取式.
      apply 中间性的对称性.
      assumption.
    apply 等价共线BAC.
    apply out_col.
    assumption.
Qed.

Lemma bet2_out_out : forall A B C B' C', B <> A -> B' <> A -> Out A C C' -> Bet A B C -> Bet A B' C' -> Out A B B'.
Proof.
    intros.
    induction(两点重合的决定性 B' C').
      subst C'.
      unfold Out in *.
      分离合取式.
      repeat split; try assumption.
      induction H5.
        left.
        eapply 中间性的交换传递性2.
          apply H2.
        assumption.
      eapply l5_3.
        apply H2.
      assumption.
    unfold Out in *.
    分离合取式.
    repeat split.
      assumption.
      assumption.
    induction H6.
      assert(Bet A B C').
        eapply 中间性的交换传递性2.
          apply H2.
        assumption.
      eapply l5_3.
        apply H7.
      assumption.
    assert(Bet B' C' C).
      eapply 中间性的交换传递性1.
        apply H3.
      assumption.
    assert(Bet A B' C).
      eapply 中间性的外传递性2.
        apply H3.
        assumption.
      assumption.
    eapply l5_3.
      apply H2.
    assumption.
Qed.

Lemma bet2__out : forall A B C B', A <> B -> A <> B' -> Bet A B C -> Bet A B' C -> Out A B B'.
Proof.
    intros.
    apply bet2_out_out with C C; auto.
    apply 中间性_AB不等推AC不等 in H1; auto.
    apply out_trivial; auto.
Qed.

Lemma out_bet_out_1 : forall A B C P,
 Out P A C -> Bet A B C -> Out P A B.
Proof.
    intros.
    induction (两点重合的决定性 B P).
      subst P.
      apply False_ind.
      apply (not_bet_and_out A B C).
      split; assumption.
    unfold Out in *.
    分离合取式.
    repeat split.
      assumption.
      assumption.
    induction H3.
      left.
      eapply 中间性的内传递性1.
        apply H3.
      assumption.
    right.
    eapply 中间性的内传递性2.
      apply H3.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma out_bet_out_2 : forall A B C P,
 Out P A C -> Bet A B C -> Out P B C.
Proof.
    intros.
    apply l6_6.
    eapply out_bet_out_1.
      apply l6_6.
      apply H.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma out_bet__out : forall A B P Q,
 Bet P Q A -> Out Q A B -> Out P A B.
Proof.
    intros A B P Q HBet Hout.
    destruct Hout as [HAQ [HBQ [HQAB|HQBA]]]; [|apply l6_6];
    apply bet_out; eBetween; intro; treat_equalities; auto.
Qed.

Lemma segment_reverse : forall A B C, Bet A B C -> exists B', Bet A B' C /\ Cong C B' A B.
Proof.
  intros.
  destruct (两点重合的决定性 A B).
    subst B; exists C; finish.
  destruct (由一点往一方向构造等长线段_3 C A A B) as [B' []]; auto.
    intro; treat_equalities; auto.
  exists B'; split; trivial.
  apply 中间性的对称性, (cong_preserves_bet A B C); Cong.
  apply l6_6; assumption.
Qed.

Lemma 任两点都有不重合的共线点 : forall A B, exists C, A <> C /\ B <> C /\ Col A B C.
Proof.
    intros.
    assert (exists C, Bet A B C /\ B <> C).
      apply 构造满足中间性的不重合点.
    ex_and H C.
    exists C.
    split.
      intro.
      induction (两点重合的决定性 A B).
        subst B.
        subst C.
        intuition.
      treat_equalities.
      auto.
    assert_cols.
    auto.
Qed.

Lemma diff_bet_ex3 : forall A B C,
 Bet A B C ->
 exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      induction (两点重合的决定性 B C).
        assert (exists D, Bet B C D /\ C <> D).
          apply 构造满足中间性的不重合点.
        ex_and H2 D.
        exists D.
        repeat split.
          subst C.
          subst A.
          assumption.
          subst A.
          subst C.
          assumption.
          assumption.
        unfold Col.
        left.
        subst A.
        subst C.
        assumption.
      assert (exists D, Bet B C D /\ C <> D).
        apply 构造满足中间性的不重合点.
      ex_and H2 D.
      exists D.
      repeat split.
        intro.
        subst D.
        apply 中间性的对称性 in H.
        apply H1.
        eapply 双中间性推出点重合.
          apply H2.
        apply H.
        intro.
        subst D.
        subst A.
        apply 中间性的同一律 in H2.
        apply H3.
        subst B.
        reflexivity.
        assumption.
      unfold Col.
      left.
      eapply 中间性的外传递性2.
        apply H.
        apply H2.
      assumption.
    induction (两点重合的决定性 B C).
      subst C.
      cut(exists D : Tpoint, A <> D /\ B <> D /\ Col A B D).
        intro.
        ex_and H1 D.
        exists D.
        repeat split.
          assumption.
          assumption.
          assumption.
        assumption.
      apply 任两点都有不重合的共线点.
    assert (exists D, Bet B C D /\ C <> D).
      apply 构造满足中间性的不重合点.
    ex_and H2 D.
    exists D.
    repeat split.
      intro.
      subst D.
      assert (B = C).
        eapply 双中间性推出点重合.
          apply H2.
        apply 中间性的对称性.
        assumption.
      apply H1.
      assumption.
      intro.
      subst D.
      apply 中间性的同一律 in H2.
      subst C.
      apply H1.
      reflexivity.
      assumption.
    unfold Col.
    left.
    eapply 中间性的外传递性2.
      apply H.
      assumption.
    assumption.
Qed.

Lemma 每组共线三点都有另一共线点 : forall A B C,
 Col A B C -> exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    assert(cas1 := diff_bet_ex3 A B C).
    assert(cas2 := diff_bet_ex3 B C A).
    assert(cas3 := diff_bet_ex3 C A B).
    unfold Col in H.
    induction H.
      apply (diff_bet_ex3 A B C).
      assumption.
    induction H.
      assert (HH:=H).
      induction (两点重合的决定性 B C).
        subst C.
        assert (exists C, A <> C /\ B <> C /\ Col A B C).
          apply (任两点都有不重合的共线点).
        ex_and H0 D.
        exists D.
        repeat split; assumption.
      apply cas2 in HH.
      ex_and HH D.
      exists D.
      repeat split; try assumption.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H0.
        assumption.
      unfold Col.
      left.
      assumption.
    induction (两点重合的决定性 A C).
      subst C.
      assert (exists C, A <> C /\ B <> C /\ Col A B C).
        apply (任两点都有不重合的共线点).
      ex_and H0 D.
      exists D.
      repeat split; assumption.
    assert (HH:=H).
    apply cas3 in HH.
    ex_and HH D.
    exists D.
    repeat split; try assumption.
    apply 等价共线ACB.
    eapply 共线的传递性2.
      apply H0.
      apply 等价共线BAC.
      assumption.
    unfold Col.
    right;right.
    apply 中间性的对称性.
    assumption.
Qed.

Lemma Out_cases : forall A B C, Out A B C \/ Out A C B -> Out A B C.
Proof.
    intros.
    induction H.
      assumption.
    apply l6_6.
    assumption.
Qed.

End T6_2.

Hint Resolve bet_out bet_out_1 out_trivial l6_6 : out.

Ltac Out := auto 4 with out.