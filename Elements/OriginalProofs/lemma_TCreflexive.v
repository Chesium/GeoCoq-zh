Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_TCreflexive :
   forall A B C,
   Triangle A B C ->
   三角形全等 A B C A B C.
Proof.
intros.
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (Cong A C A C) by (conclude cn_congruencereflexive).
assert (三角形全等 A B C A B C) by (conclude_def 三角形全等 ).
close.
Qed.

End Euclid.