Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.completeness.
Require Import GeoCoq.Meta_theory.Continuity.dedekind_completeness.
Require Import GeoCoq.Meta_theory.Continuity.archimedes_cantor_dedekind.

Section Cantor_completeness.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma cantor__completeness : (archimedes_axiom \/ ~ archimedes_axiom) -> cantor_s_axiom ->
  line_completeness.
Proof.
  intros [archi|anarchy] cantor.
    apply dedekind_variant__completeness, (archimedes_cantor__dedekind_variant archi cantor).
    apply (not_archimedes__line_completeness anarchy).
Qed.

End Cantor_completeness.
