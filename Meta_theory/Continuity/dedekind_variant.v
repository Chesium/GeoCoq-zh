Require Export GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Ch06_out_lines.

Require Import Classical.

Section Dedekind_variant.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma dedekind_equiv : dedekind_s_axiom <-> dedekind_variant.
Proof.
  split; intros dede Alpha Beta.
    intros A C HA HC Hdij Hcut.
    apply dede.
    exists A.
    intros; apply Hcut; assumption.
  intros [A Hcut].
  destruct (classic (Beta A)) as [|HNA].
    exists A; intros X Y HX HY; assert (Bet A X A) by (apply Hcut; assumption); treat_equalities; Between.
  destruct (classic (exists C, Beta C)) as [[C HC]|HN];
    [|exists A; intros X Y HX HY; exfalso; apply HN; exists Y; apply HY].
  destruct (classic (exists P, Alpha P /\ Beta P)) as [[P []]|HNconj].
    exists P; intros; apply (中间性的交换传递性1 A); auto.
  destruct (classic (exists X, Alpha X /\ X <> A)) as [HAlpha|HN];
    [|exists A; intros X Y HX HY;
      destruct (两点重合的决定性 X A); [subst; Between|exfalso; apply HN; exists X; split; assumption]].
  pose (Alpha' := fun X' => X' = A \/ exists X, Alpha X /\ Bet A X' X).
  pose (Beta' := fun Y' => Out A Y' C /\ ~ exists X, Alpha X /\ Bet A Y' X).
  cut (exists B, forall X Y, Alpha' X -> Beta' Y -> Bet X B Y).
  { intros [B HB].
    exists B.
    intros X Y HX HY.
    apply HB.
      right; exists X; split; Between.
    clear X HX.
    split.
      destruct HAlpha as [X [HX HXA]].
      apply l6_7 with X; Out.
    intros [X [HX HAYX]].
    apply HNconj; exists Y.
    assert (Bet A X Y) by auto.
    treat_equalities; split; assumption.
  }
  apply (dede Alpha' Beta' A C).
  - left; reflexivity.
  - split.
      apply out_trivial; intro; subst; auto.
    intros [X [HX HACX]].
    apply HNconj; exists C.
    assert (C = X) by (apply (双中间性推出点重合2 A); auto).
    subst; split; assumption.
  - intros P HP.
    destruct (classic (exists X : Tpoint, Alpha X /\ Bet A P X)); [left; right|right; split]; auto.
  - intros X' Y' HX' [HY' HN].
    destruct (两点重合的决定性 X' A).
      subst; split; [Between|destruct HY'; auto].
    destruct HX' as [|[X [HX HAX'X]]]; [contradiction|].
    assert (HOut : Out A X' Y').
      assert (Bet A X C) by (apply Hcut; assumption).
      assert (A <> X) by (apply 中间性_BA不等推AC不等 with X'; assumption).
      apply l6_7 with X; [|apply l6_7 with C]; Out.
    assert (HOut' : Out Y' A X').
      apply not_bet_out; Col.
      intro; apply HN; exists X; split; [|apply 中间性的交换传递性2 with X']; assumption.
    split.
      apply out2__bet; assumption.
    destruct HOut' as [_ []]; auto.
Qed.

End Dedekind_variant.
