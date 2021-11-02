Require Export GeoCoq.Tarski_dev.Definitions.
Require Export GeoCoq.Tactics.finish.

Ltac prolong A B x C D :=
 assert (sg:= 由一点往一方向构造等长线段 A B C D);
 ex_and sg x.

Section T1_1.

Context `{Tn:无维度中性塔斯基公理系统}.
(* 等长的自反性 *)
Lemma 等长的自反性 : forall A B,
 Cong A B A B.
Proof.
    intros.
    apply (等长的内传递性 B A A B); apply 等长的伪自反性.
Qed.
(* 等长的对称性 *)
Lemma 等长的对称性 : forall A B C D : Tpoint,
 Cong A B C D -> Cong C D A B.
Proof.
    intros.
    eapply 等长的内传递性.
      apply H.
    apply 等长的自反性.
Qed.

Lemma 等长的传递性 : forall A B C D E F : Tpoint,
 Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
    intros.
    eapply 等长的内传递性; eauto using 等长的对称性.
Qed.

Lemma 等长的左交换性 : forall A B C D,
 Cong A B C D -> Cong B A C D.
Proof.
    intros.
    eapply 等长的内传递性.
      apply 等长的对称性.
      apply 等长的伪自反性.
    assumption.
Qed.

Lemma 等长的右交换性 : forall A B C D,
 Cong A B C D -> Cong A B D C.
Proof.
    intros.
    apply 等长的对称性.
    apply 等长的对称性 in H.
    apply 等长的左交换性.
    assumption.
Qed.

Lemma 等价等长CDBA : forall A B C D,
 Cong A B C D -> Cong C D B A.
Proof.
    auto using 等长的对称性, 等长的右交换性.
Qed.

Lemma 等价等长DCAB : forall A B C D,
 Cong A B C D -> Cong D C A B.
Proof.
    auto using 等长的对称性, 等长的右交换性.
Qed.

Lemma 等价等长DCBA : forall A B C D,
 Cong A B C D -> Cong D C B A.
Proof.
    auto using 等长的对称性, 等长的右交换性.
Qed.


Lemma 等长的平凡同一性 : forall A B : Tpoint,
 Cong A A B B.
Proof.
    intros.
    destruct (由一点往一方向构造等长线段 B A B B) as [E [HBet HCong]].
    assert(A=E)
      by (eapply 等长的同一性;apply HCong).
    subst.
    assumption.
Qed.


Lemma 等长的反向同一性 : forall A C D,
 Cong A A C D -> C=D.
Proof.
    intros.
    apply 等长的对称性 in H.
    eapply 等长的同一性.
    apply H.
Qed.

Lemma 等长的交换性 : forall A B C D,
 Cong A B C D -> Cong B A D C.
Proof.
    intros.
    apply 等长的左交换性.
    apply 等长的右交换性.
    assumption.
Qed.

End T1_1.

Hint Resolve 等长的交换性 等价等长CDBA 等价等长DCAB 等价等长DCBA 等长的平凡同一性
             等长的左交换性 等长的右交换性
             等长的传递性 等长的对称性 等长的自反性 : cong.

Ltac Cong := auto 4 with cong.
Ltac eCong := eauto with cong.

Section T1_2.

Context `{Tn:无维度中性塔斯基公理系统}.

(* We pre-compute some trivial lemmas to have more efficient automatic proofs. *)

Lemma 等价等长否定BACD : forall A B C D, ~ Cong A B C D -> ~ Cong B A C D.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定ABDC : forall A B C D, ~ Cong A B C D -> ~ Cong A B D C.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定BADC : forall A B C D, ~ Cong A B C D -> ~ Cong B A D C.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定CDAB : forall A B C D, ~ Cong A B C D -> ~ Cong C D A B.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定DCAB : forall A B C D, ~ Cong A B C D -> ~ Cong D C A B.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定CDBA : forall A B C D, ~ Cong A B C D -> ~ Cong C D B A.
Proof.
auto with cong.
Qed.

Lemma 等价等长否定DCBA : forall A B C D, ~ Cong A B C D -> ~ Cong D C B A.
Proof.
auto with cong.
Qed.

End T1_2.

Hint Resolve 等价等长否定BACD 等价等长否定ABDC 等价等长否定BADC
             等价等长否定CDAB 等价等长否定DCAB 等价等长否定CDBA 等价等长否定DCBA : cong.

Section T1_3.


Context `{Tn:无维度中性塔斯基公理系统}.

Lemma 五线段公理_等价SAS_with_def : forall A B C D A' B' C' D',
 外五线段形式 A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    unfold 外五线段形式.
    intros;spliter.
    apply (五线段公理_等价SAS A A' B B'); assumption.
Qed.

Lemma 与不同点等长之点不同 : forall A B C D : Tpoint,
 A <> B -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst.
    apply H.
    eauto using 等长的同一性.
Qed.

Lemma 与不同点等长之点不同_2 : forall A B C D ,
 B <> A -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using 等长的同一性, 等长的对称性.
Qed.

Lemma 与不同点等长之点不同_3 : forall A B C D ,
 C <> D -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    eauto using 等长的同一性, 等长的对称性.
Qed.

Lemma 与不同点等长之点不同_4 : forall A B C D ,
 D <> C -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using 等长的同一性, 等长的对称性.
Qed.

Lemma 三角形全等的对称性 : forall A B C A' B' C',
 三角形全等 A B C A' B' C' -> 三角形全等 A' B' C' A B C.
Proof.
    unfold 三角形全等.
    intuition.
Qed.

Lemma 三角形全等的BAC交换性 : forall A B C A' B' C',
  三角形全等 A B C A' B' C' -> 三角形全等 B A C B' A' C'.
Proof.
    unfold 三角形全等.
    intuition.
Qed.

Lemma 三角形全等的ACB交换性 : forall A B C A' B' C',
 三角形全等 A B C A' B' C' -> 三角形全等 A C B A' C' B'.
Proof.
    unfold 三角形全等.
    intuition.
Qed.

Lemma 三角形全等的传递性 : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 三角形全等 A0 B0 C0 A1 B1 C1 -> 三角形全等 A1 B1 C1 A2 B2 C2 -> 三角形全等 A0 B0 C0 A2 B2 C2.
Proof.
    unfold 三角形全等.
    intros.
    spliter.
    repeat split; eapply 等长的传递性; eCong.
Qed.

End T1_3.

Hint Resolve 三角形全等的对称性 : cong.
Hint Resolve 三角形全等的BAC交换性 三角形全等的ACB交换性 三角形全等的传递性 : cong3.
Hint Unfold 三角形全等 : cong3.

Section T1_4.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 两点重合的决定性 : forall A B : Tpoint, A=B \/ ~ A=B.
Proof. exact 两点要么重合要么不重合. Qed.

Lemma distinct : forall P Q R : Tpoint, P <> Q -> (R <> P \/ R <> Q).
Proof.
    intros.
    induction (两点重合的决定性 R P).
      subst R.
      right.
      assumption.
    left.
    assumption.
Qed.

Lemma 两组连续三点分段等则全体等 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    induction (两点重合的决定性 A B).
      subst B.
      assert (A' = B') by
     (apply (等长的同一性 A' B' A); Cong).
      subst; Cong.
    apply 等长的交换性; apply (五线段公理_等价SAS A A' B B' C C' A A'); Cong.
Qed.

Lemma bet_cong3 : forall A B C A' B',  Bet A B C -> Cong A B A' B' -> exists C', 三角形全等 A B C A' B' C'.
Proof.
    intros.
    assert (exists x, Bet A' B' x /\ Cong B' x B C) by (apply 由一点往一方向构造等长线段).
    ex_and H1 x.
    assert (Cong A C A' x).
      eapply 两组连续三点分段等则全体等.
        apply H.
        apply H1.
        assumption.
      Cong.
    exists x;unfold 三角形全等; repeat split;Cong.
Qed.

Lemma 点的唯一构造 : forall Q A B C X Y,
 Q <> A -> Bet Q A X -> Cong A X B C -> Bet Q A Y -> Cong A Y B C -> X=Y.
Proof.
    intros.
    assert (Cong A X A Y) by (apply 等长的传递性 with B C; Cong).
    assert (Cong Q X Q Y) by (apply (两组连续三点分段等则全体等 Q A X Q A Y);Cong).
    assert(外五线段形式 Q A X Y Q A X X) by (unfold 外五线段形式;repeat split;Cong).
    apply 五线段公理_等价SAS_with_def in H6; try assumption.
    apply 等长的同一性 with X; Cong.
Qed.

Lemma 等长的各排列情况 :
 forall A B C D,
 Cong A B C D \/ Cong A B D C \/ Cong B A C D \/ Cong B A D C \/
 Cong C D A B \/ Cong C D B A \/ Cong D C A B \/ Cong D C B A ->
 Cong A B C D.
Proof.
    intros.
    decompose [or] H;clear H; Cong.
Qed.

Lemma 等长的等价排列 :
 forall A B C D,
 Cong A B C D ->
 Cong A B C D /\ Cong A B D C /\ Cong B A C D /\ Cong B A D C /\
 Cong C D A B /\ Cong C D B A /\ Cong D C A B /\ Cong D C B A.
Proof.
    intros.
    repeat split; Cong.
Qed.

End T1_4.