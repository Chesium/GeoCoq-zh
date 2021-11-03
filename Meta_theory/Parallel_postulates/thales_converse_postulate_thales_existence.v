Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch10_line_reflexivity.

Section thales_converse_postulate_thales_existence.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma thales_converse_postulate__thales_existence : thales_converse_postulate -> existential_thales_postulate.
Proof.
  intro thales.
  destruct 防降维公理_老版本 as [C [A [B0]]].
  assert(HNCol : ~ Col C A B0) by (unfold Col; assumption).
  destruct (l10_15 C A C B0) as [B []]; Col.
  assert(~ Col C A B) by (apply (one_side_not_col123 _ _ _ B0); Side).
  assert(Per A C B) by Perp.
  destruct (中点的存在性 A B) as [M].
  exists A, B, C, M.
  repeat (split; Col).
  apply (thales _ B); assumption.
Qed.

End thales_converse_postulate_thales_existence.