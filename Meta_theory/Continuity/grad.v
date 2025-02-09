Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.
Require Import Relations.

Section Grad.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma grad__bet : forall A B C, Grad A B C -> Bet A B C.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; [Between|eBetween].
Qed.

Lemma grad__col : forall A B C, Grad A B C -> Col A B C.
Proof.
  intros; apply 中间性蕴含共线1, grad__bet; assumption.
Qed.

Lemma grad_neq__neq13 : forall A B C, Grad A B C -> A <> B -> A <> C.
Proof.
  intros A B C HG HAB Heq.
  subst C.
  apply HAB.
  apply 中间性的同一律, grad__bet; trivial.
Qed.

Lemma grad_neq__neq12 : forall A B C, Grad A B C -> A <> C -> A <> B.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; intros; intro; treat_equalities.
    auto.
  apply H0; auto.
Qed.

Lemma grad112__eq : forall A B, Grad A A B -> A = B.
Proof.
  intros A B HG.
  assert (HA' : exists A', A' = A /\ Grad A A' B) by (exists A; auto).
  destruct HA' as [A' [Heq HG']].
  clear HG.
  revert Heq.
  elim HG'; auto.
  clear HG' A B A'.
  intros; treat_equalities; auto.
Qed.

Lemma grad121__eq : forall A B, Grad A B A -> A = B.
Proof.
  intros A B HG.
  apply 中间性的同一律, grad__bet; trivial.
Qed.

Lemma grad__le : forall A B C, Grad A B C -> Le A B A C.
Proof.
  intros.
  apply grad__bet in H.
  exists B; split; Cong.
Qed.

Lemma bet_cong2_grad__grad2 : forall A B C D E F,
  Grad A B C -> Bet D E F -> Cong A B D E -> Cong B C E F -> 在同样的线性刻度上 A B C D E F.
Proof.
  intros A B C D E F HGrad.
  destruct (两点重合的决定性 D E).
  { intros; treat_equalities.
    apply grad112__eq in HGrad.
    treat_equalities; apply 双重线性刻度_初始化.
  }
  revert F.
  induction HGrad.
    intros; treat_equalities; apply 双重线性刻度_初始化.
  intros F' HBet HCong1 HCong2.
  destruct (由一点往一方向构造等长线段 D E B C) as [F []].
  destruct (两点重合的决定性 E F).
    treat_equalities; apply 双重线性刻度_步进 with B E; trivial; [apply 双重线性刻度_初始化|CongR].
  assert (Bet B C C').
    apply grad__bet in HGrad; apply 中间性的交换传递性1 with A; assumption.
  assert (Bet E F F').
  { apply cong_preserves_bet with B C C'; Cong.
    统计不重合点.
    apply l6_2 with D; Between.
  }
  apply 双重线性刻度_步进 with C F; Cong.
    apply 中间性的外传递性1 with E; trivial.
  apply 等长的传递性 with A B; Cong.
  apply 等长的传递性 with C C'; trivial.
  apply l4_3_1 with B E; Cong.
Qed.

Lemma grad2__grad123 : forall A B C D E F, 在同样的线性刻度上 A B C D E F -> Grad A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply 线性刻度_初始化.
    apply (线性刻度_步进 _ _ C); auto.
Qed.

Lemma grad2__grad456 : forall A B C D E F, 在同样的线性刻度上 A B C D E F -> Grad D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply 线性刻度_初始化.
    apply (线性刻度_步进 _ _ F); auto.
Qed.

Lemma grad_sum : forall A B C D E,
  Grad A B C -> Grad A B D -> Bet A C E -> Cong A D C E ->
  Grad A B E.
Proof.
  intros A B C D E HGC HGD.
  elim (两点重合的决定性 A B).
  { intros; subst B.
    assert(A = C) by (apply grad112__eq; trivial).
    assert(A = D) by (apply grad112__eq; trivial).
    treat_equalities; trivial.
  }
  intro HAB.
  revert E.
  induction HGD.
    intro E; apply 线性刻度_步进; trivial.
  rename C0 into D; rename C' into D'.
  intros E' HBet' HCong'.
  destruct(由一点往一方向构造等长线段 A C A D) as [E [HBet HCong]].
  assert (HBet1 : Bet A B C) by (apply grad__bet; trivial).
  assert (HBet2 : Bet A B D) by (apply grad__bet; trivial).
  assert(HBet3 : Bet C E E').
  { apply l6_13_1.
      统计不重合点; apply l6_2 with A; Between.
    apply (l5_6_等长保持小于等于关系 A D A D'); Cong.
    apply bet__le1213; trivial.
  }
  apply 线性刻度_步进 with E; auto with cong; eBetween.
  apply 等长的传递性 with D D'; auto.
  apply l4_3_1 with A C; Cong.
Qed.

Lemma gradexp__grad : forall A B C, 在对数刻度上 A B C -> Grad A B C.
Proof.
  induction 1.
    apply 线性刻度_初始化.
  apply grad_sum with C C; auto.
Qed.

Lemma gradexp_le__reach : forall A B C D B',
  在对数刻度上 A B B' -> Le C D A B' ->
  Reach A B C D.
Proof.
  intros A B C D B' HGE HLe.
  exists B'; split; trivial.
  apply gradexp__grad; trivial.
Qed.

Lemma grad__ex_gradexp_le : forall A B C,
  Grad A B C ->
  exists D, 在对数刻度上 A B D /\ Le A C A D.
Proof.
  intros A B C.
  induction 1.
    exists B; split; Le; apply 对数刻度_初始化.
  destruct IHGrad as [D [HGE HLe]].
  destruct (由一点往一方向构造等长线段 A D A D) as [D' [HBet HCong]].
  exists D'; split.
    apply 对数刻度_步进 with D; Cong.
  apply bet2_le2__le1346 with C D; Le.
  apply gradexp__grad, grad__bet in HGE.
  apply l5_6_等长保持小于等于关系 with A B A D; Cong; Le.
Qed.

Lemma reach__ex_gradexp_le : forall A B C D, Reach A B C D ->
  exists B', 在对数刻度上 A B B' /\ Le C D A B'.
Proof.
  intros A B C D HR.
  destruct HR as [B0 [HG HLe]].
  destruct (grad__ex_gradexp_le A B B0 HG) as [B' [HG2 HLe2]].
  exists B'; split; trivial.
  apply 长度小于等于的传递性 with A B0; trivial.
Qed.

Lemma gradexp2__gradexp123 : forall A B C D E F,
  在同样的对数刻度上 A B C D E F ->
  在对数刻度上 A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply 对数刻度_初始化.
  apply (对数刻度_步进 _ _ C); auto.
Qed.

Lemma gradexp2__gradexp456 : forall A B C D E F,
  在同样的对数刻度上 A B C D E F ->
  在对数刻度上 D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply 对数刻度_初始化.
  apply (对数刻度_步进 _ _ F); auto.
Qed.


Inductive 在对数刻度上Inv : Tpoint -> Tpoint -> Tpoint -> Prop :=
    gradexpinv_init : forall A B, 在对数刻度上Inv A B B
  | gradexpinv_stab : forall A B B' C, Bet A B' B -> Cong A B' B' B -> 在对数刻度上Inv A B C ->
                    在对数刻度上Inv A B' C.

Lemma gradexp_clos_trans : forall A B C, 在对数刻度上 A B C <->
  clos_refl_trans_n1 Tpoint (fun X Y => 中点 X A Y) B C.
Proof.
  intros; split; induction 1; try constructor.
    apply Relation_Operators.rtn1_trans with C; [split|]; assumption.
    apply 对数刻度_步进 with y; Between; Cong.
Qed.

Lemma gradexpinv_clos_trans : forall A B C, 在对数刻度上Inv A B C <->
  clos_refl_trans_1n Tpoint (fun X Y => 中点 X A Y) B C.
Proof.
  intros; split; induction 1; try constructor.
    apply Relation_Operators.rt1n_trans with B; [split|]; assumption.
    apply gradexpinv_stab with y; Between; Cong.
Qed.

Lemma gradexp__gradexpinv : forall A B C, 在对数刻度上 A B C <-> 在对数刻度上Inv A B C.
Proof.
  intros.
  rewrite gradexp_clos_trans, gradexpinv_clos_trans.
  rewrite <- clos_rt_rt1n_iff, <- clos_rt_rtn1_iff.
  reflexivity.
Qed.

(** D is the last graduation of AB before or equal to C, and E the first graduation after C *)
Lemma reach__grad_min : forall A B C, A <> B -> Bet A B C -> Reach A B A C ->
  exists D E, Bet A D C /\ Grad A B D /\ E <> C /\ Bet A C E /\ Bet A D E /\ Cong A B D E.
Proof.
  intros A B C HAB HBet HReach.
  destruct HReach as [D [HD1 HD2]].
  apply l6_13_1 in HD2;
    [|apply l6_7 with B; [apply l6_6|]; apply bet_out; auto; apply grad__bet, HD1].
  revert dependent C.
  induction HD1.
    intros; assert (B = C) by (apply 双中间性推出点重合 with A; Between); subst C.
    destruct (由一点往一方向构造等长线段 A B A B) as [C []].
    统计不重合点.
    exists B, C; repeat split; Between; Cong; constructor.
  intros; destruct (l5_3 A C0 C C'); trivial.
    apply IHHD1; assumption.
  destruct (两点重合的决定性 C' C0).
  - subst C0.
    destruct (由一点往一方向构造等长线段 A C' A B) as [C'' []].
    统计不重合点.
    exists C', C''; repeat split; Cong.
    apply 线性刻度_步进 with C; assumption.
  - exists C, C'; repeat split; assumption.
Qed.

Lemma reach__ex_gradexp_lt : forall A B P Q, A <> B -> Reach P Q A B ->
  exists C, 在对数刻度上 A C B /\ Lt A C P Q.
Proof.
  intros A B P Q HAB HReach.
  apply reach__ex_gradexp_le in HReach.
  destruct HReach as [R [HR1 HR2]].
  generalize dependent B.
  induction HR1; rename A0 into P, B into Q; intros.
  { destruct (中点的存在性 A B) as [C []].
    exists C; split.
      rewrite gradexp__gradexpinv.
      apply gradexpinv_stab with B; auto; constructor.
    apply 长度小于_小于等于_传递性 with A B; trivial.
    split; Le.
    intro; assert (C = B) by (apply (between_cong A); assumption).
    treat_equalities; auto.
  }
  rename C into R, C' into R'.
  destruct (中点的存在性 A B) as [M HM].
  统计不重合点.
  destruct (IHHR1 M) as [C []]; auto.
    apply 两中点组全段偏序则半段偏序 with B R'; [|split|]; trivial.
  exists C; split; trivial.
  destruct HM.
  apply 对数刻度_步进 with M; trivial.
Qed.

End Grad.

Hint Resolve grad__bet : between.
Hint Resolve grad__col : col.
Hint Resolve grad__le : le.