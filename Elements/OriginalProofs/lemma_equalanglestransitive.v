Require Export GeoCoq.Elements.OriginalProofs.lemma_angledistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_layoff.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalangleshelper.
Require Export GeoCoq.Elements.OriginalProofs.proposition_04.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglestransitive : 
   forall A B C D E F P Q R, 
   等角 A B C D E F -> 等角 D E F P Q R ->
   等角 A B C P Q R.
Proof.
intros.
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq D E) by (forward_using lemma_angledistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (neq E F) by (forward_using lemma_angledistinct).
assert (neq B C) by (forward_using lemma_angledistinct).
assert (neq P Q) by (forward_using lemma_angledistinct).
assert (neq Q P) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists U, (Out E D U /\ Cong E U B A)) by (conclude lemma_layoff);destruct Tf as [U];分离合取式.
let Tf:=fresh in
assert (Tf:exists V, (Out E F V /\ Cong E V B C)) by (conclude lemma_layoff);destruct Tf as [V];分离合取式.
assert (neq E U) by (conclude lemma_raystrict).
assert (neq E V) by (conclude lemma_raystrict).
assert (等角 P Q R D E F) by (conclude lemma_equalanglessymmetric).
assert (neq Q R) by (forward_using lemma_angledistinct).
let Tf:=fresh in
assert (Tf:exists u, (Out Q P u /\ Cong Q u E U)) by (conclude lemma_layoff);destruct Tf as [u];分离合取式.
let Tf:=fresh in
assert (Tf:exists v, (Out Q R v /\ Cong Q v E V)) by (conclude lemma_layoff);destruct Tf as [v];分离合取式.
assert (nCol A B C) by (conclude_def 等角 ).
assert (等角 A B C U E V) by (conclude lemma_equalangleshelper).
assert (Cong B A E U) by (conclude lemma_congruencesymmetric).
assert (Cong B C E V) by (conclude lemma_congruencesymmetric).
assert ((Cong A C U V /\ 等角 B A C E U V /\ 等角 B C A E V U)) by (conclude proposition_04).
assert (Cong E U Q u) by (conclude lemma_congruencesymmetric).
assert (Cong E V Q v) by (conclude lemma_congruencesymmetric).
assert (等角 D E F u Q v) by (conclude lemma_equalangleshelper).
assert (等角 u Q v D E F) by (conclude lemma_equalanglessymmetric).
assert (等角 u Q v U E V) by (conclude lemma_equalangleshelper).
assert (等角 U E V u Q v) by (conclude lemma_equalanglessymmetric).
assert ((Cong U V u v /\ 等角 E U V Q u v /\ 等角 E V U Q v u)) by (conclude proposition_04).
assert (Cong A C u v) by (conclude lemma_congruencetransitive).
assert (Cong B A Q u) by (conclude lemma_congruencetransitive).
assert (Cong B C Q v) by (conclude lemma_congruencetransitive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B C C) by (conclude lemma_ray4).
assert (等角 A B C P Q R) by (conclude_def 等角 ).
close.
Qed.

End Euclid.


