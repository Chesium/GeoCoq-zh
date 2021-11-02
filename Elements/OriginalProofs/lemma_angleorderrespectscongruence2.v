Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence2 : 
   forall A B C D E F a b c, 
   角度小于 A B C D E F -> 等角 a b c A B C ->
   角度小于 a b c D E F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists P Q R, (BetS P Q R /\ Out E D P /\ Out E F R /\ 等角 A B C D E Q)) by (conclude_def 角度小于 );destruct Tf as [P[Q[R]]];spliter.
assert (等角 a b c D E Q) by (conclude lemma_equalanglestransitive).
assert (角度小于 a b c D E F) by (conclude_def 角度小于 ).
close.
Qed.

End Euclid.


