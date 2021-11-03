Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.

Section Gupta_inspired_variant_of_无维度中性塔斯基公理系统_to_无维度中性塔斯基公理系统.

Context `{ITnEQD:Gupta_inspired_variant_of_无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma g2_1 : forall A B, CongG A B A B.
Proof.
intros A B.
apply 等长的内传递性G with B A;
apply 等长的伪自反性G; auto.
Qed.

Lemma g2_2 : forall A B C D,
  CongG A B C D -> CongG C D A B.
Proof.
intros A B C D HCong.
apply 等长的内传递性G with C D; auto; apply g2_1.
Qed.

Lemma 等长的内传递性T : forall A B C D E F,
  CongG A B C D -> CongG A B E F -> CongG C D E F.
Proof.
intros A B C D E F HCong1 HCong2.
apply 等长的内传递性G with A B; apply g2_2; auto.
Qed.

Lemma g2_3 : forall A B C D,
  CongG A B C D -> CongG B A C D.
Proof.
Proof.
intros A B C D HCong.
apply 等长的内传递性T with A B; auto.
apply 等长的伪自反性G.
Qed.

Lemma g2_4 : forall A B C D,
  CongG A B C D -> CongG A B D C.
Proof. intros A B C D HCong; apply g2_2; apply g2_3; apply g2_2; auto. Qed.

Lemma g2_5 : forall A B C D,
  CongG A B C D -> (A = B <-> C = D).
Proof.
intros A B C D HCong.
split; intro H; rewrite H in HCong;
[apply g2_2 in HCong|]; apply 等长的同一性G in HCong; auto.
Qed.

Lemma g2_6 : forall A B,
  BetG A B B /\ CongG B B A A.
Proof.
intros A B; destruct (由一点往一方向构造等长线段G A B A A) as [C [HBet HCong]].
assert (B = C) by (apply g2_5 with A A; auto).
rewrite H in *; auto.
Qed.

Lemma g2_7 : forall A B C A' B' C',
  CongG A B A' B' -> CongG B C B' C' ->
  BetG A B C -> BetG A' B' C' ->
  CongG A C A' C'.
Proof.
intros A B C A' B' C' HCong1 HCong2 HBet1 HBet2.
elim (两点要么重合要么不重合G A B); intro HDiff1; [rewrite HDiff1 in *; clear HDiff1|].

  {
  assert (HEq : A' = B') by (apply g2_5 with B B; try apply g2_2; auto).
  rewrite HEq; auto.
  }

  {
  elim (g2_6 A' A); intro HBet3; intro HCong3.
  apply g2_3; apply g2_4; apply 五线段公理_等价SASG with A A' B B'; auto.
  apply g2_3; apply g2_4; auto.
  }
Qed.

Lemma g2_8 : forall A B C D,
  BetG A B C -> BetG A B D -> CongG B C B D -> A <> B -> C = D.
Proof.
intros A B C D HBet1 HBet2 HCong HDiff.
assert (HEq : CongG C C C D).
  {
  apply 五线段公理_等价SASG with A A B B; auto; try apply g2_1.
  apply g2_7 with B B; auto; apply g2_1.
  }
apply g2_5 with C C; auto; apply g2_2; auto.
Qed.

Lemma g2_9 : forall A B C, BetG A B A -> BetG C A B.
Proof.
intros A B C HBet.
apply bet_inner_transitivityG with A; auto; apply g2_6.
Qed.

Lemma g2_10 : forall A B C, BetG A B A -> BetG C B A.
Proof. intros A B C HBet; do 2 apply g2_9; auto. Qed.

Lemma g2_11 : forall A B C,
  BetG A B A -> A <> B ->
  exists D, BetG C D C /\ BetG D C D /\ C <> D.
Proof.
intros A B C HBet1 HDiff1.
destruct (由一点往一方向构造等长线段G C C A B) as [D [HBet2 HCong1]].
assert (HDiff2 : C <> D)
  by (intro; apply g2_5 in HCong1; apply HDiff1; apply HCong1; auto).
destruct (由一点往一方向构造等长线段G C D B A) as [E [HBet3 HCong2]].
assert (HCong3 : CongG C E A A) by (apply g2_7 with D B; auto).
assert (HEq : C = E) by (apply g2_5 in HCong3; apply HCong3; auto).
rewrite HEq in *; clear HEq; exists D; do 2 (split; auto); apply g2_9; auto.
Qed.

Lemma g2_12 : forall A B C, BetG A B A -> BetG A B C.
Proof. intros A B C HBet; apply bet_symmetryG; apply g2_10; auto. Qed.

Lemma g2_13 : forall A B C, BetG A B A -> A <> B -> BetG C B C.
Proof.
intros A B C HBet1 HDiff.
destruct (由一点往一方向构造等长线段G C B B C) as [D [HBet2 HCong1]].
assert (HEq : C = D) by (apply g2_8 with A B; try apply g2_2; try apply g2_12; auto).
rewrite HEq in *; auto.
Qed.

Lemma g2_14 : forall A B C D, BetG A B A -> A <> B -> BetG C D C /\ BetG D C D.
Proof.
intros A B C D HBet1 HDiff1.
split.

  {
  destruct (g2_11 A B D) as [E [HBet2 [HBet3 HDiff2]]]; auto.
  apply g2_13 with E; auto.
  }

  {
  destruct (g2_11 A B C) as [E [HBet2 [HBet3 HDiff2]]]; auto.
  apply g2_13 with E; auto.
  }
Qed.

Lemma g2_15 : forall A B C D E, BetG A B A -> A <> B -> BetG C D E.
Proof.
intros A B C D E HBet HDiff.
apply g2_9. destruct (g2_14 A B D E) as [HBet1 HBet2]; auto.
Qed.

Lemma g2_16 : forall A B C D E, ~ BetG C D E -> BetG A B A -> A = B.
Proof.
intros A B C D E HNBet HBet.
elim (两点要么重合要么不重合G A B); intro HDiff; auto.
exfalso; apply HNBet; apply g2_15 with A B; auto.
Qed.

Lemma 中间性的同一律T : forall A B, BetG A B A -> A = B.
Proof.
intros A B; apply g2_16 with GPA GPB GPC; intro HNBet; apply 防降维公理G; left; auto.
Qed.

Lemma 等长的平凡同一性T : forall A B, CongG A A B B.
Proof. intros A B; destruct (g2_6 B A); auto. Qed.

Lemma 两组连续三点分段等则全体等T : forall A B C A' B' C',
  BetG A B C -> BetG A' B' C' ->
  CongG A B A' B' -> CongG B C B' C' ->
  CongG A C A' C'.
Proof.
intros A B C A' B' C' HBet1 HBet2 HCong1 HCong2.
elim (两点要么重合要么不重合G A B); intro HDiff; [rewrite HDiff in *; clear HDiff|].

  {
  assert (HEq : A' = B') by (apply g2_5 with B B; try apply g2_2; auto).
  rewrite HEq in *; auto.
  }

  {
  apply g2_3; apply g2_4; apply 五线段公理_等价SASG with A A' B B'; auto;
  try apply 等长的平凡同一性T; apply g2_3; apply g2_4; auto.
  }
Qed.

Lemma 点的唯一构造T : forall Q A B C X Y,
  Q <> A -> BetG Q A X -> CongG A X B C -> BetG Q A Y -> CongG A Y B C -> X = Y.
Proof.
intros Q A B C X Y HDiff HBet1 HCong1 HBet2 HCong2.
assert (HCong3 : CongG A X A Y) by (apply 等长的内传递性G with B C; auto).
assert (HCong4 : CongG Q X Q Y) by (apply 两组连续三点分段等则全体等T with A A; auto; apply g2_1).
assert (HCong5 : CongG X X X Y)
  by (apply 五线段公理_等价SASG with Q Q A A; auto; apply g2_1).
apply g2_5 with X X; try apply g2_2; auto.
Qed.

Lemma ABB中间性T : forall A B, BetG A B B.
Proof. intros A B; destruct (g2_6 A B); auto. Qed.

Lemma 中间性的决定性G : forall A B C, BetG A B C \/ ~ BetG A B C.
Proof.
intros A B C.
destruct (由一点往一方向构造等长线段G A B B C) as [D [HBet1 HCong]].
elim (两点要么重合要么不重合G C D); intro HDiff1; [rewrite HDiff1 in *; auto|].
elim (两点要么重合要么不重合G A B); intro HDiff2;
[rewrite HDiff2 in *; left; apply bet_symmetryG; apply ABB中间性T|].
right; intro HBet2; apply HDiff1; apply 点的唯一构造T with A B B C;
auto; apply g2_1.
Qed.

Definition ColG A B C := BetG A B C \/ BetG B C A \/ BetG C A B.

Lemma 共线的决定性G : forall A B C, ColG A B C \/ ~ ColG A B C.
Proof.
intros A B C; unfold ColG; induction (中间性的决定性G A B C); induction (中间性的决定性G B C A);
induction (中间性的决定性G C A B); tauto.
Qed.

Lemma 帕施公理T : forall A B C P Q,
  BetG A P C -> BetG B Q C ->
  exists x, BetG P x B /\ BetG Q x A.
Proof.
intros A B C P Q HBet1 HBet2.
elim (两点要么重合要么不重合G A P); intro HDiff1;
[rewrite HDiff1 in *; exists P; split;
 [apply bet_symmetryG|]; apply ABB中间性T|].
elim (两点要么重合要么不重合G P C); intro HDiff2;
[rewrite HDiff2 in *; exists Q; split; apply bet_symmetryG;
 try apply ABB中间性T; auto|].
elim (两点要么重合要么不重合G B Q); intro HDiff3;
[rewrite HDiff3 in *; exists Q; split;
 [|apply bet_symmetryG]; apply ABB中间性T|].
elim (两点要么重合要么不重合G Q C); intro HDiff4;
[rewrite HDiff4 in *; exists P; split; apply bet_symmetryG;
 try apply ABB中间性T; auto|].
elim (共线的决定性G A B C); intro HCol; [|apply 帕施公理G with C; auto].
do 2 (try (elim HCol; clear HCol; intro HCol)); rename HCol into HBet3.

  {
  exists B; split; [apply ABB中间性T|].
  apply bet_symmetryG; apply bet_inner_transitivityG with C; auto.
  }

  {
  exists C; split.

    {
    apply bet_symmetryG; apply bet_inner_transitivityG with A;
    auto; apply bet_symmetryG; auto.
    }

    {
    apply bet_symmetryG; apply bet_inner_transitivityG with B;
    apply bet_symmetryG; auto.
    }
  }

  {
  exists A; split; [|apply ABB中间性T].
  apply bet_symmetryG; apply bet_inner_transitivityG with C;
  auto; apply bet_symmetryG; auto.
  }
Qed.

Global Instance GI_to_T : 无维度中性塔斯基公理系统.
Proof.
exact
(Build_无维度中性塔斯基公理系统 TpointG BetG CongG
   等长的伪自反性G 等长的内传递性T 等长的同一性G
   由一点往一方向构造等长线段G 五线段公理_等价SASG
   中间性的同一律T 帕施公理T
   GPA GPB GPC
   防降维公理G).
Defined.

Global Instance GI_to_T_PED :
  无维度中性塔斯基公理系统_带两点重合决定性 GI_to_T.
Proof. split; exact 两点要么重合要么不重合G. Defined.

End Gupta_inspired_variant_of_无维度中性塔斯基公理系统_to_无维度中性塔斯基公理系统.

Section Gupta_inspired_variant_of_Tarski_2D_to_Tarski_2D.

Context `{IT2D:Gupta_inspired_variant_of_Tarski_2D}.

Lemma 防升维公理T : forall A B C P Q,
  P <> Q -> CongG A P A Q -> CongG B P B Q -> CongG C P C Q ->
  (BetG A B C \/ BetG B C A \/ BetG C A B).
Proof.
intros A B C P Q HPQ HCong1 HCong2 HCong3.
elim (两点要么重合要么不重合G A B); intro HAB; try (rewrite HAB in *; clear HAB);
elim (两点要么重合要么不重合G A C); intro HAC; try (rewrite HAC in *; clear HAC);
elim (两点要么重合要么不重合G B C); intro HBC; try (rewrite HBC in *; clear HBC).

  {
  left; apply ABB中间性T.
  }

  {
  right; right; apply ABB中间性T.
  }

  {
  left; apply ABB中间性T.
  }

  {
  right; right; apply ABB中间性T.
  }

  {
  left; apply ABB中间性T.
  }

  {
  right; left; apply ABB中间性T.
  }

  {
  left; apply ABB中间性T.
  }

  {
  apply 防升维公理G with P Q; auto.
  }
Qed.

Global Instance GI2D_to_T2D : Tarski_2D GI_to_T_PED.
Proof. split; exact 防升维公理T. Defined.

End Gupta_inspired_variant_of_Tarski_2D_to_Tarski_2D.

Section Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何_to_塔斯基公理系统_欧几里得几何.

Context `{ITE:Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何}.


Lemma euclidT : forall A B C D T,
  Bet A D T -> Bet B D C -> A <> D ->
  exists X, exists Y, Bet A B X /\ Bet A C Y /\ Bet X T Y.
Proof.
assert (H := GI_to_T_PED).
intros A B C D T HBet1 HBet2 HDiff1.
elim (两点重合的决定性 B D); intro HDiff2;
[treat_equalities; exists T, C; Between|].
elim (两点重合的决定性 D C); intro HDiff3;
[treat_equalities; exists B, T; Between|].
elim (共线的决定性 A B C); intro HCol; [|apply euclidG with D; auto].
clear HDiff2; clear HDiff3.
do 2 (try (elim HCol; clear HCol; intro HCol)); rename HCol into HBet3.

  {
  elim (两点重合的决定性 A B); intro HDiff2;
  [treat_equalities; exists T; exists C; Between|].
  elim (l5_2 A B C T); eBetween; intro HBet4.

    {
    elim (两点重合的决定性 B C); intro HDiff3;
    [treat_equalities; exists T; exists T; Between|].
    exists B; exists T; do 2 (split; Between); eBetween.
    }

    {
    elim (两点重合的决定性 B T); intro HDiff3;
    [treat_equalities; exists B; exists C; Between|].
    exists B; exists C; Between.
    }
  }

  {
  elim (两点重合的决定性 A C); intro HDiff2;
  [treat_equalities; exists B; exists T; Between|].
  elim (l5_2 A C B T); eBetween; intro HBet4.

    {
    elim (两点重合的决定性 B C); intro HDiff3;
    [treat_equalities; exists T; exists T; Between|].
    exists T; exists C; repeat (split; Between); eBetween.
    }

    {
    exists B; exists C; Between.
    }
  }

  {
  elim (l5_3 B A D C); Between; intro HBet4.

    {
    elim (两点重合的决定性 A B); intro HDiff2;
    [treat_equalities; exists T; exists C; Between|].
    elim (l5_2 B A C T); eBetween; intro HBet5.

      {
      exists B; exists T; Between.
      }

      {
      exists B; exists C; do 2 (split; Between).
      apply 中间性的外传递性1 with A; eBetween.
      intro; treat_equalities; intuition.
      }
    }

    {
    elim (l5_2 A D B T); Between; intro HBet5.

      {
      elim (两点重合的决定性 B D); intro HDiff2;
      [treat_equalities; exists T; exists C; Between|].
      exists T; exists C; do 2 (try split; Between); eBetween.
      }

      {
      exists B; exists C; do 2 (split; Between).
      apply 中间性的外传递性2 with A; eBetween;
      try (intro; treat_equalities; intuition).
      }
    }
  }
Qed.

Global Instance GI_euclidean_to_T_euclidean :
  塔斯基公理系统_欧几里得几何 GI_to_T_PED.
Proof. split; exact euclidT. Defined.

End Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何_to_塔斯基公理系统_欧几里得几何.