Require Export GeoCoq.Elements.OriginalProofs.proposition_24.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy2.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_25 : 
   forall A B C D E F, 
   Triangle A B C -> Triangle D E F -> Cong A B D E -> Cong A C D F -> Lt E F B C ->
   角度小于 E D F B A C.
Proof.
intros.
assert (Cong D E A B) by (conclude lemma_congruencesymmetric).
assert (Cong D F A C) by (conclude lemma_congruencesymmetric).
assert (~ 角度小于 B A C E D F).
 {
 intro.
 assert (Lt B C E F) by (conclude proposition_24).
 assert (~ Lt E F B C) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (nCol D E F) by (conclude_def Triangle ).
assert (~ Col E D F).
 {
 intro.
 assert (Col D E F) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ 等角 E D F B A C).
 {
 intro.
 assert (等角 B A C E D F) by (conclude lemma_equalanglessymmetric).
 assert (Cong B C E F) by (conclude proposition_04).
 assert (Cong E F B C) by (conclude lemma_congruencesymmetric).
 assert (Lt B C B C) by (conclude lemma_lessthancongruence2).
 assert (~ Lt B C B C) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (角度小于 E D F B A C) by (conclude lemma_angletrichotomy2).
close.
Qed.

End Euclid.
