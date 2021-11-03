Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate :
  bachmann_s_lotschnittaxiom -> weak_inverse_projection_postulate.
Proof.
rewrite bachmann_s_lotschnittaxiom_aux.
intros lotschnitt A B C D E F P Q H为锐角 HPer HSuma HOut HPQ HPerP HCop.
suma.assert_diffs.
assert (HNCol : ~ Col A B C).
{ intro HCol.
  apply (成直角三点不共线 D E F); auto.
  apply (col2_suma__col A B C A B C); assumption.
}
assert (HNCol1 : ~ Col B C P) by (intro; apply HNCol; ColR).
destruct (l10_6_existence_spec B C P) as [P' HP']; trivial.
assert (HP'1 : 对称 P P' B C) by (apply is_image_is_image_spec; auto).
assert (HNCol2 : ~ Col B C P') by (apply osym_not_col with P; trivial).
destruct (l10_6_existence_spec B C Q) as [Q' HQ']; trivial.
assert (HQ'1 : 对称 Q Q' B C) by (apply is_image_is_image_spec; auto).
assert_diffs.
assert (P' <> Q').
 intro; subst Q'; assert (P = Q) by (apply (l10_2_uniqueness B C P'); assumption); auto.
assert (H等角 : 等角 C B P' A B C).
  apply l11_10 with C P' P C; Out.
  apply conga_sym, conga_left_comm, reflectl__conga; auto.
  apply is_image_spec_rev, HP'.
assert (HTS : TS B C P P').
  repeat split; Col; destruct HP' as [[X [HX1 HX2]] _]; exists X; split; [Col|Between].
apply l6_6 in HOut.
assert (共面 P' C A B) by (apply col2_cop__cop with P B; Col; Cop).
assert (共面 B P P' Q) by CopR.
assert (HPer1 : Per A B P').
{ apply l11_17 with D E F; trivial.
  apply (suma2__conga A B C A B C); trivial.
  apply conga3_suma__suma with A B C C B P' A B P'; 等角.
  exists P'; repeat (split; try (apply conga_refl; auto)); [|Cop].
  apply l9_9, l9_5 with P B; Col.
}
assert (HNCol3 : ~ Col A B P') by (apply 成直角三点不共线; auto).
assert (HNCol4 : ~ Col B P' P) by (intro; apply HNCol3; ColR).
assert (HPerp1 : Perp A B B P') by (apply 直角转L形垂直; auto).
assert (HPerp2 : Perp A B P Q) by (apply 垂直的左交换性, 垂线共线点也构成垂直1 with P; Col; apply 直角转L形垂直; auto).
assert (HPerp3 : Perp B P' P' Q').
  apply 直角转L形垂直; auto; apply image_spec_preserves_per with B P Q B C; trivial; apply col__refl; Col.
assert (HNCol5 : ~ Col P' P Q).
  apply (par_not_col B P'); Col.
  apply par_not_col_strict with P; Col.
  apply l12_9 with A B; Perp; CopR.
assert (HI := HPerp2); destruct HI as [I [_ [_ [HCol1 [HCol2 _]]]]].
destruct (lotschnitt A B B P' P Q P' Q' B P P') as [Y [HY1 HY2]]; Col; Cop.
  {
  elim (共线的决定性 B C Q); intro; [|CopR].
  assert (Q = Q'); [|treat_equalities; Cop].
  apply col_image_spec__eq with B C; Col.
  }

exists Y; split; trivial.
apply col_one_side_out with A.
  apply 等价共线BCA, intersection_with_image_gen with P Q P' Q'; Col.
apply invert_one_side, one_side_transitivity with P'.
- apply cop_nts__os; Col; Cop.
  apply (conga_sams_nos__nts A B C A B C P'); 和角.
  apply l9_9, l9_5 with P B; Col.
- apply l12_6, par_strict_col_par_strict with Q'; Col.
    intro; subst; apply HNCol5; Col.
  apply par_not_col_strict with P'; Col.
  apply l12_9 with B P'; Perp; Cop.
  elim (共线的决定性 B C Q); intro; [|CopR].
  assert (Q = Q'); [|treat_equalities; CopR].
  apply col_image_spec__eq with B C; Col.
Qed.

End bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.