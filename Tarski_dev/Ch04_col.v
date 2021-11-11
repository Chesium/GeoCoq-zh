Require Export GeoCoq.Tarski_dev.Ch04_cong_bet.

Section T4_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 等价共线BCA : forall A B C,Col A B C -> Col B C A.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma 等价共线CAB : forall A B C, Col A B C -> Col C A B.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma 等价共线CBA : forall A B C, Col A B C -> Col C B A.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma 等价共线BAC : forall A B C, Col A B C -> Col B A C.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma 等价共线ACB : forall A B C, Col A B C -> Col A C B.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

End T4_1.

Hint Resolve 中间性蕴含共线1 等价共线BCA 等价共线CAB
等价共线CBA 等价共线BAC 等价共线ACB : col.

Ltac Col := auto 3 with col.
Ltac Col5 := auto with col.

Section T4_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 共线否定排列BCA :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col B C A.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma 共线否定排列CAB :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col C A B.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma 共线否定排列CBA :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col C B A.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma 共线否定排列BAC :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col B A C.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma 共线否定排列ACB :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col A C B.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

End T4_2.

Hint Resolve 共线否定排列BCA 共线否定排列CAB
共线否定排列CBA 共线否定排列BAC 共线否定排列ACB : col.

Section T4_3.

Context `{Tn:无维度中性塔斯基公理系统}.

(** This lemma is used by tactics for trying several permutations. *)
Lemma 共线的各排列情况 :
 forall A B C,
 Col A B C \/ Col A C B \/ Col B A C \/
 Col B C A \/ Col C A B \/ Col C B A ->
 Col A B C.
Proof.
    intros.
    decompose [or] H; Col.
Qed.

Lemma 共线的等价排列 :
 forall A B C,
 Col A B C ->
 Col A B C /\ Col A C B /\ Col B A C /\
 Col B C A /\ Col C A B /\ Col C B A.
Proof.
    intros.
    repeat split; Col.
Qed.

Lemma AAB型共线 : forall A B, Col A A B.
Proof.
    unfold Col.
    intros.
    Between.
Qed.

Lemma ABB型共线 : forall A B, Col A B B.
Proof.
    unfold Col.
    intros.
    Between.
Qed.

Lemma ABA型共线 : forall A B, Col A B A.
Proof.
    unfold Col.
    intros.
    right;Between.
Qed.

End T4_3.

Hint Immediate AAB型共线 ABB型共线 ABA型共线: col.

Section T4_4.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 全等于退化的三角形 : forall A B C A' B' C',
 Col A B C -> 三角形全等 A B C A' B' C' -> Col A' B' C'.
Proof.
    unfold Col.
    intros.
    decompose [or] H;
      eauto 6  using l4_6 with cong3.
Qed.

Lemma l4_14_退化三角形有其全等形 : forall A B C A' B',
  Col A B C -> Cong A B A' B' -> exists C', 三角形全等 A B C A' B' C'.
Proof.
    unfold Col.
    intros.
    intuition.
      prolong A' B' C' B C.
      exists C'.
      assert (Cong A C A' C') by (eapply 两组连续三点分段等则全体等;eCong).
      unfold 三角形全等;intuition.
      assert (exists C', Bet A' C' B' /\ 三角形全等 A C B A' C' B') by (eapply l4_5;Between).
      ex_and H1 C'.
      exists C'.
      auto with cong3.
    prolong B' A' C' A C.
    exists C'.
    assert (Cong B C B' C') by (eapply 两组连续三点分段等则全体等;eBetween;Cong).
    unfold 三角形全等;intuition.
Qed.

Lemma l4_16_五线段形式推论 : forall A B C D A' B' C' D',
   五线段形式 A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    unfold 五线段形式.
    unfold Col.
    intros.
    decompose [or and] H; clear H.
      assert (Bet A' B' C') by (eapply l4_6;eauto).
      unfold 三角形全等 in *; 分离合取式.
      assert(外五线段形式 A B C D A' B' C' D') by (unfold 外五线段形式;repeat split; assumption).
      eapply 五线段公理_等价SAS_with_def; eauto.
      assert(Bet B' C' A') by (apply (l4_6 B C A B' C' A'); Cong;auto with cong3).
      apply (l4_2 B C A D B' C' A' D').
      unfold 内五线段形式; unfold 三角形全等 in *; 分离合取式; repeat split;Between;Cong.
    assert (Bet C' A' B') by (eapply (l4_6 C A B C' A' B'); auto with cong3).
    eapply (五线段公理_等价SAS_with_def B A C D B' A'); unfold 外五线段形式; unfold 三角形全等 in *; 分离合取式; repeat split; Between; Cong.
Qed.

Lemma l4_17 : forall A B C P Q,
  A<>B -> Col A B C -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q.
Proof.
    intros.
    assert (五线段形式 A B C P A B C Q) by (unfold 五线段形式; unfold 三角形全等;repeat split; Cong).
    eapply l4_16_五线段形式推论; eauto.
Qed.

Lemma l4_18 : forall A B C C',
  A<>B -> Col A B C -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof.
    intros.
    apply 等长的同一性 with C.
    apply (l4_17 A B); Cong.
Qed.

Lemma l4_19 : forall A B C C',
 Bet A C B -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      treat_equalities; reflexivity.
    apply (l4_18 A B); Cong.
    auto using 中间性蕴含共线1 with col.
Qed.

Lemma 不共线则不重合 : forall A B C ,
 ~ Col A B C ->
 ~ Col A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
    intros.
    repeat split;(auto;intro); subst; apply H; Col.
Qed.

Lemma 共线否定的各排列情况 :
 forall A B C,
 ~ Col A B C \/ ~ Col A C B \/ ~ Col B A C \/
 ~ Col B C A \/ ~ Col C A B \/ ~ Col C B A ->
 ~ Col A B C.
Proof.
    intros.
    decompose [or] H; Col.
Qed.

Lemma 共线否定的等价排列 :
 forall A B C,
 ~ Col A B C ->
 ~ Col A B C /\ ~ Col A C B /\ ~ Col B A C /\
 ~ Col B C A /\ ~ Col C A B /\ ~ Col C B A.
Proof.
    intros.
    repeat split; Col.
Qed.

Lemma col_cong_3_cong_3_eq : forall A B C A' B' C1 C2,
  A <> B -> Col A B C -> 三角形全等 A B C A' B' C1 -> 三角形全等 A B C A' B' C2 -> C1 = C2.
Proof.
intros A B C A' B' C1 C2 HAB HCol HCong1 HCong2.
apply l4_18 with A' B'; try apply 全等于退化的三角形 with A B C; Col;
unfold 三角形全等 in *; 分离合取式.
  intro; treat_equalities; intuition.
  apply 等长的传递性 with A C; Cong.
  apply 等长的传递性 with B C; Cong.
Qed.

End T4_4.
