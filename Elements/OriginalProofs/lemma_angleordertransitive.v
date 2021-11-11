Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossbar.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleordertransitive : 
   forall A B C D E F P Q R, 
   角度小于 A B C D E F -> 角度小于 D E F P Q R ->
   角度小于 A B C P Q R.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists U V W, (BetS U W V /\ Out Q P U /\ Out Q R V /\ 等角 D E F P Q W)) by (conclude_def 角度小于 );destruct Tf as [U[V[W]]];分离合取式.
assert (等角 P Q W D E F) by (conclude lemma_equalanglessymmetric).
assert (neq D E) by (forward_using lemma_angledistinct).
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (neq E F) by (forward_using lemma_angledistinct).
assert (neq Q U) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists G, (Out E D G /\ Cong E G Q U)) by (conclude lemma_layoff);destruct Tf as [G];分离合取式.
assert (neq Q W) by (forward_using lemma_angledistinct).
let Tf:=fresh in
assert (Tf:exists J, (Out E F J /\ Cong E J Q W)) by (conclude lemma_layoff);destruct Tf as [J];分离合取式.
assert (nCol D E F) by (conclude lemma_equalanglesNC).
assert (等角 D E F D E F) by (conclude lemma_equalanglesreflexive).
assert (等角 D E F G E J) by (conclude lemma_equalangleshelper).
assert (等角 G E J D E F) by (conclude lemma_equalanglessymmetric).
assert (等角 G E J P Q W) by (conclude lemma_equalanglestransitive).
assert (eq W W) by (conclude cn_equalityreflexive).
assert (Out Q W W) by (conclude lemma_ray4).
assert (等角 G E J U Q W) by (conclude lemma_equalangleshelper).
assert (nCol G E J) by (conclude lemma_equalanglesNC).
assert (nCol U Q W) by (conclude lemma_equalanglesNC).
assert (Triangle G E J) by (conclude_def Triangle ).
assert (Triangle U Q W) by (conclude_def Triangle ).
assert (Cong G J U W) by (conclude proposition_04).
assert (eq W W) by (conclude cn_equalityreflexive).
assert (等角 D E F U Q W) by (conclude lemma_equalangleshelper).
assert (等角 U Q W D E F) by (conclude lemma_equalanglessymmetric).
assert (等角 D E F U Q W) by (conclude lemma_equalangleshelper).
assert (角度小于 A B C U Q W) by (conclude lemma_angleorderrespectscongruence).
rename_H H;
let Tf:=fresh in
assert (Tf:exists H S T, (BetS S H T /\ Out Q U S /\ Out Q W T /\ 等角 A B C U Q H)) by (conclude_def 角度小于 );destruct Tf as [H[S[T]]];分离合取式.
assert (Out Q U P) by (conclude lemma_ray5).
assert (neq Q H) by (forward_using lemma_angledistinct).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Out Q H H) by (conclude lemma_ray4).
assert (等角 A B C P Q H) by (conclude lemma_equalangleshelper).
assert (等角 D E F P Q T) by (conclude lemma_equalangleshelper).
assert (nCol P Q T) by (conclude lemma_equalanglesNC).
assert (Triangle P Q T) by (conclude_def Triangle ).
assert (neq Q P) by (conclude lemma_ray2).
assert (Out Q T W) by (conclude lemma_ray5).
assert (~ Col S Q T).
 {
 intro.
 assert (Col Q U S) by (conclude lemma_rayimpliescollinear).
 assert (Col U Q S) by (forward_using lemma_collinearorder).
 assert (Col Q P U) by (conclude lemma_rayimpliescollinear).
 assert (Col U Q P) by (forward_using lemma_collinearorder).
 assert (neq Q U) by (conclude lemma_raystrict).
 assert (neq U Q) by (conclude lemma_inequalitysymmetric).
 assert (Col Q S P) by (conclude lemma_collinear4).
 assert (Col S Q P) by (forward_using lemma_collinearorder).
 assert (neq Q S) by (conclude lemma_raystrict).
 assert (neq S Q) by (conclude lemma_inequalitysymmetric).
 assert (Col Q T P) by (conclude lemma_collinear4).
 assert (Col P Q T) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle S Q T) by (conclude_def Triangle ).
assert (Out Q S U) by (conclude lemma_ray5).
let Tf:=fresh in
assert (Tf:exists K, (Out Q H K /\ BetS U K W)) by (conclude lemma_crossbar);destruct Tf as [K];分离合取式.
assert (BetS U K V) by (conclude lemma_3_6b).
assert (eq P P) by (conclude cn_equalityreflexive).
assert (Out Q P P) by (conclude lemma_ray4).
assert (等角 A B C P Q K) by (conclude lemma_equalangleshelper).
assert (角度小于 A B C P Q R) by (conclude_def 角度小于 ).
close.
Qed.

End Euclid.


