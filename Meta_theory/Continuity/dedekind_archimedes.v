Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Ch07_midpoint.

Section Dedekind_archimedes.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma archimedes_aux : (forall A B C, Out A B C -> Reach A B A C) -> archimedes_axiom.
Proof.
  intros Haux A B C D HAB.
  destruct (两点重合的决定性 C D).
    subst; exists B.
    split; Le.
    apply 线性刻度_初始化.
  destruct (由一点往一方向构造等长线段_3 A B C D) as [E [HOut HCong]]; auto.
  destruct (Haux A B E HOut) as [B' [HGrad HLe]]; trivial.
  exists B'.
  split; trivial.
  apply 长度小于等于的传递性 with A E; Le.
Qed.

Lemma dedekind_variant__archimedes : (forall A B C D, Reach A B C D \/ ~ Reach A B C D) ->
  dedekind_variant -> archimedes_axiom.
Proof.
  intros Hdec dedekind.
  apply archimedes_aux.
  intros A B C HOut.
  destruct (Hdec A B A C) as [|HNReach]; trivial.
  exfalso.
  assert (HX : exists X, forall P Q, (P = A \/ Out A B P /\ Reach A B A P) ->
                                       (Out A B Q /\ ~ Reach A B A Q) -> Bet P X Q).
  { apply dedekind with A C.
    - left; split.
    - split; assumption.
    - intros P HP.
      assert (Out A B P); [|destruct (Hdec A B A P); auto].
      apply l6_7 with C; Out.
    - intros P Q [HP|[HP1 HP2]] [HQ1 HQ2].
        subst; destruct HQ1 as [_ []]; split; Between.
      split; [|intro; subst; apply HQ2, HP2].
      assert (HOut' : Out A P Q) by (apply l6_7 with B; Out).
      destruct (HOut') as [_ [_ [|Habs]]]; trivial.
      exfalso.
      apply HQ2.
      destruct HP2 as [B' [HGrad HLe]].
      exists B'; split; trivial.
      apply 长度小于等于的传递性 with A P; Le.
  }
  destruct HX as [X HX].
  统计不重合点.
  assert (HGrad := 线性刻度_初始化 A B).
  assert (HBet : Bet B X C) by (apply HX; [right|]; split; Out; exists B; split; Le).
  assert (Out A B X) by (apply out_bet_out_1 with C; auto).
  destruct HOut as [_ [_ [HBet2|HBet2]]]; [|exfalso; apply HNReach; exists B; split; Le].
  absurd (~ Reach A B A X).

  - intro HAbs.
    assert (X <> B) by (intro; apply HAbs; exists B; subst; split; Le).
    destruct (长度小于等于的决定性 X A A B) as [HLe|HLe].
      apply HAbs; exists B; split; Le.
    assert (Bet A B X) by (apply l6_13_1; Le).
    destruct HLe as [X0 [HBet1 HCong]].
    absurd (~ Reach A B A X0).
    { intro HNReach0.
      assert (HXOut : Out X X0 B).
        apply l6_7 with A; [|apply l6_6]; apply bet_out; Between.
        intro; treat_equalities; auto.
      destruct (长度小于等于的决定性 X B X X0) as [HLe|HLe].
      - apply HNReach0; exists B; split; trivial.
        exists X0; split; Cong.
        apply 中间性的内传递性1 with X; Between.
        apply 中间性的对称性, l6_13_1; trivial.
        apply l6_6; trivial.
      - absurd (X = X0).
          统计不重合点; auto.
        apply 双中间性推出点重合 with B.
          apply l6_13_1; trivial.
        apply 中间性的对称性, HX; [right|]; split; trivial.
          apply out_trivial; auto.
          exists B; split; Le.
        apply l6_7 with X; trivial.
        apply l6_6, bet_out; Between.
        intro; subst X0; apply HNReach0.
        exists B; split; Le.
    }
    intro HReach.
    destruct HReach as [B' [HGrad' HLe]].
    destruct (由一点往一方向构造等长线段 A B' A B) as [B1' [HBet' HCong']].
    apply HAbs; exists B1'; split.
      apply 线性刻度_步进 with B'; Cong.
    apply bet2_le2__le1346 with X0 B'; Le; Between.
    apply 等长则小于等于, 等长的传递性 with A B; Cong.

  - intro HReach.
    destruct (由一点往一方向构造等长线段_3 X C A B) as [X1 [HOut' HCong]]; auto.
      intro; subst; contradiction.
    assert (HBet1 : Bet A X X1).
      apply 中间性的对称性, bet_out__bet with C; eBetween.
    apply (not_bet_and_out X1 X C).
    split; [|apply l6_6; trivial].
    apply HX; [right|]; split; trivial; [| |apply bet_out; auto].
      统计不重合点; apply l6_7 with X; Out.
    destruct HReach as [B' [HGrad' HLe]].
    destruct (由一点往一方向构造等长线段 A B' A B) as [B1' [HBet' HCong']].
    exists B1'; split.
      apply 线性刻度_步进 with B'; Cong.
    apply bet2_le2__le1346 with X B'; Le.
    apply 等长则小于等于, 等长的传递性 with A B; Cong.
Qed.

(*
Lemma dedekind__archimedes : (forall A B C D, ~ ~ Reach A B C D -> Reach A B C D) ->
  dedekind_s_axiom -> archimedes_axiom.
Proof.
  intros Hstab dedekind.
  apply archimedes_aux.
  intros A B C HOut.
  apply Hstab.
  intro HNReach.
  assert (HX : exists X, forall P Q, (Out A B P /\ ~ ~ Reach A B A P) ->
                                       (Out A B Q /\ ~ Reach A B A Q) -> Bet P X Q).
  { apply dedekind.
    exists A.
    intros X Y [HXOut HX] [HYOut HY].
    assert (HOut' : Out A X Y) by (apply l6_7 with B; [apply l6_6|]; trivial).
    destruct (HOut') as [_ [_ [|Habs]]]; trivial.
    exfalso.
    apply HX; clear HX.
    intro HX.
    apply HY.
    destruct HX as [B' [HGrad HLe]].
    exists B'; split; trivial.
    apply 长度小于等于的传递性 with A X; Le.
  }
  destruct HX as [X HX].
  统计不重合点.
  assert (HGrad := 线性刻度_初始化 A B).
  assert (HBet : Bet B X C).
  { apply HX; split; trivial.
      apply out_trivial; auto.
    intro HAbs; apply HAbs.
    exists B; split; Le.
  }
  assert (Out A B X) by (apply out_bet_out_1 with C; auto).
  destruct HOut as [_ [_ [HBet2|HBet2]]]; [|exfalso; apply HNReach; exists B; split; Le].
  absurd (~ Reach A B A X).

  - intro HAbs.
    destruct (两点重合的决定性 X B).
      subst; apply HAbs; exists B; split; Le.
    destruct (长度小于等于的决定性 X A A B) as [HLe|HLe].
      apply HAbs; exists B; split; Le.
    assert (Bet A B X) by (apply l6_13_1; Le).
    destruct HLe as [X0 [HBet1 HCong]].
    absurd (~ Reach A B A X0).
    { intro HNReach0.
      assert (HXOut : Out X X0 B).
        apply l6_7 with A; [|apply l6_6]; apply bet_out; Between.
        intro; treat_equalities; auto.
      destruct (长度小于等于的决定性 X B X X0) as [HLe|HLe].
      - apply HNReach0; exists B; split; trivial.
        exists X0; split; Cong.
        apply 中间性的内传递性1 with X; Between.
        apply 中间性的对称性, l6_13_1; trivial.
        apply l6_6; trivial.
      - absurd (X = X0).
          统计不重合点; auto.
        apply 双中间性推出点重合 with B.
          apply l6_13_1; trivial.
        apply 中间性的对称性, HX; split; trivial.
          apply out_trivial; auto.
          intro HN; apply HN; exists B; split; Le.
        apply l6_7 with X; trivial.
        apply l6_6, bet_out; Between.
        intro; subst X0; apply HNReach0.
        exists B; split; Le.
    }
    intro HReach.
    destruct HReach as [B' [HGrad' HLe]].
    destruct (由一点往一方向构造等长线段 A B' A B) as [B1' [HBet' HCong']].
    apply HAbs; exists B1'; split.
      apply 线性刻度_步进 with B'; Cong.
    apply bet2_le2__le1346 with X0 B'; Le; Between.
    apply 等长则小于等于, 等长的传递性 with A B; Cong.

  - intro HReach.
    destruct (由一点往一方向构造等长线段_3 X C A B) as [X1 [HOut' HCong]]; auto.
      intro; subst; contradiction.
    assert (HBet1 : Bet A X X1).
      apply 中间性的对称性, bet_out__bet with C; eBetween.
    apply (not_bet_and_out X1 X C).
    split; [|apply l6_6; trivial].
    apply HX; split; trivial; [| |apply bet_out; auto].
    { apply l6_7 with X; trivial.
      统计不重合点; apply bet_out; auto.
    }
    destruct HReach as [B' [HGrad' HLe]].
    destruct (由一点往一方向构造等长线段 A B' A B) as [B1' [HBet' HCong']].
    intro HAbs; apply HAbs.
    exists B1'; split.
      apply 线性刻度_步进 with B'; Cong.
    apply bet2_le2__le1346 with X B'; Le.
    apply 等长则小于等于, 等长的传递性 with A B; Cong.
Qed.
*)

End Dedekind_archimedes.