Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesflip : 
   forall A B C D E F, 
   等角 A B C D E F ->
   等角 C B A F E D.
Proof.
intros.
assert (nCol D E F) by (conclude lemma_equalanglesNC).
assert (等角 D E F A B C) by (conclude lemma_equalanglessymmetric).
assert (nCol A B C) by (conclude lemma_equalanglesNC).
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (等角 C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (等角 C B A D E F) by (conclude lemma_equalanglestransitive).
assert (等角 D E F F E D) by (conclude lemma_ABCequalsCBA).
assert (等角 C B A F E D) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


