Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.first_order.
Require Import GeoCoq.Meta_theory.Continuity.first_order_dedekind_circle_circle.
Require Import GeoCoq.Meta_theory.Continuity.elementary_continuity_props.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.

Section 塔斯基公理系统_带连续性_to_TRC.

Context `{TC:塔斯基公理系统_带连续性}.

Instance TC_to_TRC : 塔斯基公理系统_尺规作图 TnEQD.
Proof.
  split.
  apply circle_circle_bis__circle_circle_axiom, circle_circle__circle_circle_bis, fod__circle_circle, dedekind__fod.
  unfold dedekind_s_axiom.
  exact continuity.
Defined.

End 塔斯基公理系统_带连续性_to_TRC.