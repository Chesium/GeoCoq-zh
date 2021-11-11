Require Export GeoCoq.Tarski_dev.Ch06_out_lines.
Require Export GeoCoq.Tarski_dev.Tactics.ColR.

Ltac not_exist_hyp_comm A B := not_exist_hyp (A<>B);not_exist_hyp (B<>A).

Ltac not_exist_hyp2 A B C D := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D].
Ltac not_exist_hyp3 A B C D E F := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F].

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
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于推出不重合 A B C D H);clean_reap_hyps

      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; 统计不重合点; Col_refl tpoint col.

Section T7_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 中点的决定性 :
 forall I A B, 中点 I A B \/ ~ 中点 I A B.
Proof.
    intros.
    unfold 中点.
    elim (中间性的决定性 A I B);intro; elim (等长的决定性 A I I B);intro; tauto.
Qed.

Lemma A是AB中点则A与B重合 : forall A B, 中点 A A B -> A = B.
Proof.
    intros.
    unfold 中点 in H.
    分离合取式.
    treat_equalities;reflexivity.
Qed.

Lemma A是BA中点则A与B重合 : forall A B, 中点 A B A -> A=B.
Proof.
    intros.
    unfold 中点 in *.
    分离合取式.
    apply 等长的同一性 in H0.
    auto.
Qed.

Lemma M是AB中点则M是BA中点 : forall M A B, 中点 M A B -> 中点 M B A.
Proof.
    unfold 中点.
    intuition.
Qed.

Lemma M是AA中点则M与A重合 : forall M A, 中点 M A A -> M=A.
Proof.
    unfold 中点.
    intros;分离合取式;treat_equalities;reflexivity.
Qed.


Lemma A是AA中点 : forall A, 中点 A A A.
Proof.
    unfold 中点.
    intros;repeat split;Between;Cong.
Qed.

(** This corresponds to l7_8 in Tarski's book. *)

Lemma 构造对称点 : forall P A, exists P', 中点 A P P'.
Proof.
    unfold 中点.
    intros.
    prolong P A E P A.
    exists E.
    split;Cong;Between.
Qed.

Lemma 中点组的唯一性1 : forall A P P1 P2, 中点 P A P1 -> 中点 P A P2 -> P1=P2.
Proof.
    unfold 中点.
    intros.
    分离合取式.
    elim (两点重合的决定性 A P); intros.
      treat_equalities;auto.
    apply (点的唯一构造 A P A P);Cong.
Qed.

Lemma 中点组的唯一性2 : forall P Q A X, 中点 A P X -> 中点 A Q X -> P=Q.
Proof.
    unfold 中点.
    intros.
    分离合取式.
    induction (两点重合的决定性 A X).
      treat_equalities;reflexivity.
    apply (点的唯一构造 X A X A);Cong;Between.
Qed.

Lemma 中点组的唯一性3 : forall P Q A X, 中点 A P X -> 中点 A X Q -> P=Q.
Proof.
intros; apply 中点组的唯一性2 with A X; unfold 中点 in *; split; 分离合取式; Cong; Between.
Qed.

Lemma l7_13_同中点组两侧等长 : forall A P Q P' Q',  中点 A P' P -> 中点 A Q' Q -> Cong P Q P' Q'.
Proof.
    unfold 中点.
    intros.
    分离合取式.
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
        apply 中间性蕴含共线1;auto.
      eapply (两组连续三点分段等则全体等 X A X' Y' A Y);Between.
    assert (A <> X).
      eapply 中间性_AB不等推AC不等.
        apply H14.
      auto.
    assert (Cong X' Y' Y X) by eauto using l4_16_五线段形式推论.
    assert (Cong A X A X') by (apply 等长的传递性 with A Y; Cong).
    assert (内五线段形式 Y Q A X Y' Q' A X') by (unfold 内五线段形式, 五线段形式 in *;分离合取式;repeat split;Between; Cong).
    assert (Cong Q X Q' X') by eauto using l4_2.
    assert (内五线段形式 X P A Q X' P' A Q') by (unfold 内五线段形式;repeat split;Between;Cong).
    eauto using l4_2.
Qed.

Lemma l7_15 : forall P Q R P' Q' R' A,
 中点 A P P' -> 中点 A Q Q' -> 中点 A R R' -> Bet P Q R -> Bet P' Q' R'.
Proof.
    intros.
    分离合取式.
    eapply l4_6.
      apply H2.
    unfold 三角形全等.
    repeat split.
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H.
      apply M是AB中点则M是BA中点.
      assumption.
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H.
      apply M是AB中点则M是BA中点.
      assumption.
    eapply l7_13_同中点组两侧等长.
      apply M是AB中点则M是BA中点.
      apply H0.
    apply M是AB中点则M是BA中点.
    assumption.
Qed.


Lemma l7_16 : forall P Q R S P' Q' R' S' A,
  中点 A P P' -> 中点 A Q Q' ->
  中点 A R R' -> 中点 A S S' ->
  Cong P Q R S -> Cong P' Q' R' S'.
Proof.
    intros.
    assert (Cong P Q P' Q').
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H.
      apply M是AB中点则M是BA中点.
      apply H0.
    assert (Cong R S R' S').
      eapply l7_13_同中点组两侧等长.
        apply M是AB中点则M是BA中点.
        apply H1.
      apply M是AB中点则M是BA中点.
      apply H2.
    apply 等长的传递性 with P Q; Cong.
    apply 等长的传递性 with R S; Cong.
Qed.


Lemma 对称保持中点 :
   forall A B C D E F Z,
 中点 Z A D -> 中点 Z B E ->
 中点 Z C F -> 中点 B A C -> 中点 E D F.
Proof.
    intros.
    unfold 中点.
    unfold 中点 in H2.
    分离合取式.
    split.
      eapply l7_15;eauto.
    eapply l7_16;eauto.
Qed.

End T7_1.

Hint Resolve l7_13_同中点组两侧等长 : cong.
Hint Resolve M是AB中点则M是BA中点 A是AA中点 : midpoint.

Ltac 中点 := auto with midpoint.

Section T7_2.

Context {Tn:无维度中性塔斯基公理系统}.
Context {TnEQD:无维度中性塔斯基公理系统_带两点重合决定性 Tn}.

Lemma 中点的各排列情况 :
  forall A B C,
  中点 A B C \/ 中点 A C B ->
  中点 A B C.
Proof.
    intros.
    decompose [or] H; 中点.
Qed.

Lemma 中点的等价排列 :
  forall A B C,
  中点 A B C ->
  中点 A B C /\ 中点 A C B.
Proof.
    unfold 中点.
    intros.
    分离合取式.
    repeat split; Between; Cong.
Qed.

Lemma 中点的唯一性1 : forall P P' A B, 中点 A P P' -> 中点 B P P' -> A=B.
Proof.
    intros.
    assert (Cong P B P' B).
      unfold 中点 in *.
      分离合取式.
      Cong.
    assert (exists B', 中点 A B B') by (apply 构造对称点).
    induction H2.
    assert (Cong P' B P x) by eauto with midpoint cong.
    assert (Cong P B P x) by (apply 等长的传递性 with P' B; Cong).
    assert (Cong P B P' x) by eauto with midpoint cong.
    assert (Cong P' B P' x) by (apply 等长的传递性 with P x; Cong; apply 等长的传递性 with P B; Cong).
    assert (Bet P B P') by (unfold 中点 in *;分离合取式;assumption).
    assert (B=x) by (apply (l4_19 P P' B x);Between).
    subst x.
    apply M是AA中点则M与A重合.
    assumption.
Qed.

Lemma 中点的唯一性2 : forall P P' A B, 中点 A P P' -> 中点 B P' P -> A=B.
Proof.
    intros.
    apply 中点的唯一性1 with P P'; 中点.
Qed.

Lemma 共线点间距相同要么重合要么中点 : forall M A B,
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

Lemma 不重合共线点间距相同则为中点组1 : forall M A B, A<>B ->
  Col A M B -> Cong M A M B -> 中点 M A B.
Proof.
   intros.
   induction (共线点间距相同要么重合要么中点 M A B H0 H1);intuition.
Qed.

Lemma 不重合共线点间距相同则为中点组2 : forall A B C,
 A <> C -> Col A B C -> Cong A B B C ->
 中点 B A C.
Proof.
    intros.
    apply 共线点间距相同要么重合要么中点 in H0.
      intuition subst.
    Cong.
Qed.

Lemma 四点对边等长则对角线交点平分对角线 : forall A B C D P,
  ~ Col A B C -> B<>D ->
  Cong A B C D -> Cong B C D A ->
  Col A P C -> Col B P D ->
  中点 P A C /\ 中点 P B D.
Proof.
    intros.
    统计不重合点.
    assert (exists P', 三角形全等 B D P D B P').
      eapply l4_14_退化三角形有其全等形.
        Col.
      Cong.
    induction H9.
    assert (Col D B x) by
      (apply 全等于退化的三角形 with B D P;Col).
    assert (五线段形式 B D P A D B x C).
      unfold 五线段形式.
      unfold 三角形全等 in *.
      分离合取式.
      repeat split; Cong; Col.
    assert (五线段形式 B D P C D B x A).
      unfold 五线段形式.
      unfold 三角形全等 in *.
      分离合取式.
      repeat split; Col; Cong.
    assert (Cong P A x C) by (eauto using l4_16_五线段形式推论).
    assert (Cong P C x A) by (eauto using l4_16_五线段形式推论).
    assert (三角形全等 A P C C x A) by (unfold 三角形全等;repeat split; Cong).
    assert (Col C x A) by (eauto using 全等于退化的三角形).
    assert (P=x).
      unfold 五线段形式 in *.
      分离合取式.
      apply (l6_21_两线交点的唯一性 A C B D); Col.
    subst x.
    unfold 三角形全等 in *;分离合取式.
    split;apply 不重合共线点间距相同则为中点组1;Col;Cong.
Qed.

Lemma M是AB中点则M是BA中点2_aux : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   中点 M1 A1 B1 -> 中点 M2 A2 B2 ->
   Le C A1 C A2 ->
   Bet M1 C M2.
Proof.
    intros.
    induction (两点重合的决定性 A2 C).
      subst C.
      apply AB小于等于CC推出A与B重合 in H5.
      subst A2.
      apply 等长的反向同一性 in H1.
      subst B1.
      apply 等长的反向同一性 in H2.
      subst B2.
      apply M是AA中点则M与A重合 in H4.
      subst A1.
      apply ABB中间性.
    assert (exists A, 中点 C A2 A).
      apply 构造对称点.
    induction H7.
    assert (exists B, 中点 C B2 B).
      apply 构造对称点.
    induction H8.
    assert (exists M, 中点 C M2 M).
      apply 构造对称点.
    induction H9.
    assert(中点 x1 x x0).
      unfold 中点.
      split.
        eapply l7_15.
          apply H7.
          apply H9.
          apply H8.
        unfold 中点 in H4.
        分离合取式.
        assumption.
      eapply l7_16.
        apply H7.
        apply H9.
        apply H9.
        apply H8.
      unfold 中点 in H4.
      分离合取式.
      assumption.
    assert (Le C A1 C x).
      eapply l5_6_等长保持小于等于关系.
      repeat split.
        apply H5.
        apply 等长的自反性.
      unfold 中点 in H7.
      分离合取式.
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
        apply AB小于等于CC推出A与B重合 in H11.
        apply H12.
        subst A1.
        reflexivity.
      eapply l5_2.
        apply H6.
        apply 中间性的对称性.
        assumption; intro.
      unfold 中点 in H7.
      分离合取式.
      assumption.
    (* assert (M1=x).
    eauto with 中点.
    *)
    assert (Le C B1 C x0).
      eapply l5_6_等长保持小于等于关系.
        apply H11.
        assumption.
      unfold 中点 in *.
      分离合取式.
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
        apply AB小于等于CC推出A与B重合 in H13.
        subst B1.
        apply ABB中间性.
      induction (两点重合的决定性 B2 C).
        subst B2.
        apply 等长的对称性 in H2.
        eapply 等长的反向同一性 in H2.
        subst A2.
        apply AB小于等于CC推出A与B重合 in H5.
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
        分离合取式.
        assumption.
      assumption.
    assert (exists Q, Bet x1 Q C /\ Bet A1 Q B1).
      eapply l3_17_三中间性推交点存在性.
        apply 中间性的对称性.
        apply H12.
        apply 中间性的对称性.
        apply H14.
      unfold 中点 in H10.
      分离合取式.
      assumption.
    ex_and H15 Q.
    assert (内五线段形式 x A1 C x1 x0 B1 C x1).
      unfold 内五线段形式.
      unfold 中点 in *.
      分离合取式.
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
      eapply 中点的唯一性1.
        apply H20.
      assumption.
    subst Q.
    eapply 中间性的交换传递性1.
      apply H15.
    unfold 中点 in H9.
    分离合取式.
    apply 中间性的对称性.
    assumption.
Qed.

(** This is Krippen lemma , proved by Gupta in its PhD in 1965 as Theorem 3.45 *)

Lemma M是AB中点则M是BA中点2 : forall A1 A2 B1 B2 C M1 M2,
   Bet A1 C A2 -> Bet B1 C B2 ->
   Cong C A1 C B1 -> Cong C A2 C B2 ->
   中点 M1 A1 B1 -> 中点 M2 A2 B2 ->
   Bet M1 C M2.
Proof.
    intros.
    assert (Le C A1 C A2 \/ Le C A2 C A1).
      eapply 长度小于等于的决定性.
    induction H5.
      eapply M是AB中点则M是BA中点2_aux.
        apply H.
        apply H0.
        apply H1.
        apply H2.
        assumption.
        assumption.
      assumption.
    apply 中间性的对称性.
    eapply M是AB中点则M是BA中点2_aux with A2 A1 B2 B1; finish.
Qed.

Lemma 中间性蕴含共线2 : forall A B C D, Bet A B D -> Bet A C D -> Col A B C.
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

Lemma 一点与两点等距则该两点存在中点 : forall A B C,
  Cong C A C B ->
  exists X, 中点 X A B.
Proof.
    intros.
    induction(共线的决定性 A B C).
      assert(A = B \/ 中点 C A B).
        apply 共线点间距相同要么重合要么中点.
          unfold Col in *.
          intuition.
        assumption.
      induction H1.
        subst B.
        exists A.
        apply A是AA中点.
      exists C.
      assumption.
    assert (exists P, Bet C A P /\ A<>P).
      apply 构造满足中间性的不重合点.
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
        分离合取式.
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
        分离合取式.
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
      分离合取式.
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
      分离合取式.
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
      分离合取式.
      subst R.
      clean_duplicated_hyps.
      assert (Col B A C).
        apply 共线的传递性2 with X; Col.
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
      apply 等价共线BAC.
      assumption.
    eapply (l6_21_两线交点的唯一性 A Q B P R R' ).
      intro.
      unfold Col in H23.
      induction H23.
        assert(Bet A B C).
          eapply 中间性的外传递性1.
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
        eapply 中间性的交换传递性1.
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

Lemma 严格中点组推论1 : forall I A B,
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

Lemma 严格中点组推论2 : forall I A B,
 I<>A ->
 中点 I A B ->
 A<>B /\ I<>B.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold 中点 in *;分离合取式.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply 严格中点组推论1 in H0.
      intuition.
    intuition.
Qed.


Lemma 严格中点组推论3 : forall I A B,
 I<>B ->
 中点 I A B ->
 A<>B /\ I<>A.
Proof.
    intros.
    assert (A<>B).
      intro.
      unfold 中点 in *;分离合取式.
      treat_equalities.
      intuition.
    split.
      assumption.
    apply 严格中点组推论1 in H0.
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

Lemma 中点蕴含共线 : forall A M B, 中点 M A B -> Col M A B.
Proof.
    intros.
    unfold Col.
    right;right.
    apply midpoint_bet.
    apply M是AB中点则M是BA中点.
    assumption.
Qed.

Lemma 中点蕴含等长 : forall A B C, 中点 B A C -> Cong A B B C.
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
      apply 严格中点组推论1 in H0; 分离合取式; auto.
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

Lemma 严格中点组换排列则否 : forall I A B,
  A<>B ->
  中点 I A B ->
~ 中点 B A I.
Proof.
    intros.
    assert (I<>B).
      apply 严格中点组推论1 in H0.
        tauto.
      assumption.
    apply midpoint_bet in H0.
    intro.
    apply midpoint_bet in H2.
    assert (I=B).
      apply 中间性的对称性 in H0.
      apply 中间性的对称性 in H2.
      eapply 双中间性推出点重合.
        apply H2.
      apply H0.
    intuition.
Qed.

Lemma 不重合的对称性 : forall (A B : Tpoint), A<>B -> B<>A.
Proof.
    intuition.
Qed.

Lemma 两中点组全段等长则前半段等长 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Cong A B A' B' -> Cong A M A' M'.
Proof.
    intros.
    unfold 中点 in *.
    分离合取式.
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
      分离合取式.
      eapply 等长的传递性.
        apply 等长的对称性.
        apply H5.
      eapply 等长的传递性.
        apply H3.
      assumption.
    assert(M'=M'').
      eapply 中点的唯一性1; unfold 中点; split.
        apply H0.
        apply H2.
        apply H4.
      unfold 中点 in H6.
      分离合取式.
      assumption.
    subst M''.
    unfold 三角形全等 in H5.
    分离合取式.
    assumption.
Qed.

Lemma 两中点组全段等长则后半段等长 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Cong A B A' B' -> Cong B M B' M'.
Proof.
    intros.
    apply 两中点组全段等长则前半段等长 with A A'.
      中点.
      中点.
    Cong.
Qed.

Lemma 两中点组半段等长则全段等长 : forall A M B A' M' B',
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

Lemma 严格中点组半段小于全段 : forall A M B,
 A <> B -> 中点 M A B ->
 Lt A M A B.
Proof.
    intros A M B HAB HM.
    destruct (严格中点组推论1 M A B HAB HM) as [HMA HMB].
    destruct HM.
    split.
      exists M; Cong.
    intro.
    apply HMB, between_cong with A; auto.
Qed.

Lemma 两中点组半段偏序则全段偏序 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Le A M A' M' -> Le A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    destruct HM.
    destruct HM'.
    apply (bet2_le2__le1346 _ M _ _ M'); auto.
    apply (l5_6_等长保持小于等于关系 A M A' M'); auto.
Qed.

Lemma 两中点组全段偏序则半段偏序 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Le A B A' B' -> Le A M A' M'.
Proof.
    intros A M B A' M' B' HM HM' Hle.
    elim(长度小于等于的决定性 A M A' M'); auto.
    intro.
    assert(Le A' B' A B) by (apply (两中点组半段偏序则全段偏序 _ M' _ _ M); auto).
    apply 等长则小于等于.
    apply (两中点组全段等长则前半段等长 _ _ B _ _ B'); auto.
    apply 长度小于等于的反对称性; auto.
Qed.

Lemma 两中点组半段全序则全段全序 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Lt A M A' M' -> Lt A B A' B'.
Proof.
    intros A M B A' M' B' HM HM' [HLe HNcong].
    split.
      apply 两中点组半段偏序则全段偏序 with M M'; trivial.
    intro.
    apply HNcong, 两中点组全段等长则前半段等长 with B B'; trivial.
Qed.

Lemma 两中点组全段全序则半段全序 : forall A M B A' M' B',
 中点 M A B -> 中点 M' A' B' ->
 Lt A B A' B' -> Lt A M A' M'.
Proof.
    intros A M B A' M' B' HM HM' [HLe HNcong].
    split.
      apply 两中点组全段偏序则半段偏序 with B B'; trivial.
    intro.
    apply HNcong, 两中点组半段等长则全段等长 with M M'; trivial.
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
    分离合取式.
    unfold Out.
    repeat split.
      intro.
      subst B'.
      assert (A = B).
        eapply 中点组的唯一性1.
          apply M是AB中点则M是BA中点.
          apply H0.
        apply M是AB中点则M是BA中点.
        assumption.
      auto.
      intro.
      subst C'.
      assert (A = C).
        eapply 中点组的唯一性1.
          apply M是AB中点则M是BA中点.
          apply H0.
        apply M是AB中点则M是BA中点.
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
eapply 中间性的交换传递性1.
apply 中间性的对称性.
apply H1.
assumption.
apply 等长的伪自反性.
Cong.
assert(D = D1 \/ 中点 C D D1).
eapply 共线点间距相同要么重合要么中点.
apply 中间性蕴含共线1 in H1.
apply 中间性蕴含共线1 in H2.

induction (两点重合的决定性 A B).
subst B.
apply 等长的对称性 in H0.
apply 等长的同一性 in H0.
subst D.
Col.
eapply (共线的传递性4 A B); Col.

CongR.

induction H7.
subst D1.
left.
eapply 中间性的交换传递性1.
apply 中间性的对称性.
apply H1.
assumption.

assert(Cong B A C D2).
eapply (两组连续三点分段等则全体等 B C A C B D2).
Between.
eapply 中间性的交换传递性1.
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
apply A是AB中点则A与B重合 in H7.
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
eapply (中间性的外传递性2).
apply H11.
assumption.
auto.
unfold 中点 in H7.
分离合取式.
eapply 等长的传递性.
apply 等长的对称性.
apply 等长的交换性.
apply H8.
eapply 等长的传递性.
apply H0.
Cong.
assert(D = D2).
eapply 中点组的唯一性1.
apply M是AB中点则M是BA中点.
apply H7.
apply M是AB中点则M是BA中点.
assumption.
subst D2.
right.
eapply 中间性的交换传递性1.
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
分离合取式.
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
分离合取式.
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
apply 中间性蕴含共线1 in H0.
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
apply 中间性蕴含共线1 in H0.
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
分离合取式.
apply(bet2_le2__le O o A B a b); auto.
intro.

induction(两点重合的决定性 O A).
treat_equalities.
unfold Lt in H1.
分离合取式.
apply AB小于等于CC推出A与B重合 in H0.
treat_equalities.
apply H1.
apply 等长的平凡同一性.

induction(两点重合的决定性 O B).
treat_equalities.
unfold Lt in H2.
分离合取式.
apply AB小于等于CC推出A与B重合 in H0.
treat_equalities.
apply H2.
apply 等长的平凡同一性.

unfold Lt in *.
分离合取式.

unfold Le in H1.
ex_and H1 a'.
unfold Le in H2.
ex_and H2 b'.

assert(Bet a' O b').
  apply 中间性的内传递性1 with B.
    apply 中间性的交换传递性1 with A.
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
  apply 共线点间距相同要么重合要么中点.
  Col.
  Cong.
}
induction H1.
treat_equalities.
contradiction.
unfold 中点 in *.
分离合取式.
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
  apply 共线点间距相同要么重合要么中点.
  Col.
  Cong.
}
induction H2.
treat_equalities.
contradiction.
unfold 中点 in *.
分离合取式.
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
  apply(双中间性推出点重合 _ _ b').
    apply 中间性的交换传递性2 with O.
      Between.
      apply 中间性的内传递性1 with B.
        assumption.
      assumption.
  assumption.
}
treat_equalities; tauto.
assert(b' = B).
{
  apply(双中间性推出点重合 _ _ a').
  Between.
  apply 中间性的交换传递性2 with O.
    Between.
  apply 中间性的内传递性1 with A.
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
分离合取式.
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
分离合取式.
apply H6.

apply(l4_3_1 a o b A O B H H0 ); Cong.
Qed.

End T7_2.

Hint Resolve midpoint_bet : between.
Hint Resolve 中点蕴含共线 : col.
Hint Resolve 中点蕴含等长 : cong.
Hint Resolve midpoint_out midpoint_out_1 : out.