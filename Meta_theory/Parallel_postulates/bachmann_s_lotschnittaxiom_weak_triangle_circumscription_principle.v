Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch11_angles.

Section bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle :
  bachmann_s_lotschnittaxiom -> weak_triangle_circumscription_principle.
Proof.
rewrite bachmann_s_lotschnittaxiom_aux.
intros HP A B C A1 A2 B1 B2 HNC HPer.
intros HPerpB1 HPerpB2 HCop1 HCop2 HCop3 HCop4.
destruct (中垂线蕴含垂直 _ _ _ _ HPerpB1) as [A3 [HA [_ [HCol1 [HCol2 _]]]]].
destruct (中垂线蕴含垂直 _ _ _ _ HPerpB2) as [B3 [HB [_ [HCol3 [HCol4 _]]]]].
统计不重合点.
destruct (HP B C A C A1 A2 B1 B2 C A3 B3) as [I [? ?]];
  [..|exists I; split; auto]; Col; Perp; [| |CopR..].
- assert (HC' := HPerpB1).
  destruct HC' as [[[C' [HMid HCol]] _] _].
  intro; treat_equalities; 统计不重合点.
  assert (C = C'); [|treat_equalities; auto].
  elim (垂直推出不共线 _ _ _ _ (中垂线蕴含垂直 _ _ _ _ HPerpB1)); intro HNC';
  [apply l6_21_两线交点的唯一性 with A1 A2 B C|apply l6_21_两线交点的唯一性 with A1 A2 C B]; Col.

- assert (HC' := HPerpB2).
  destruct HC' as [[[C' [HMid HCol]] _] _].
  intro; treat_equalities; 统计不重合点.
  assert (C = C'); [|treat_equalities; auto].
  elim (垂直推出不共线 _ _ _ _ (中垂线蕴含垂直 _ _ _ _ HPerpB2)); intro HNC';
  [apply l6_21_两线交点的唯一性 with B1 B2 A C|apply l6_21_两线交点的唯一性 with B1 B2 C A]; Col.
Qed.

End bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.