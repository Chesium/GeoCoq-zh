Require Export GeoCoq.Elements.OriginalProofs.proposition_03.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence : 
   forall A B C D E F P Q R, 
   角度小于 A B C D E F -> 等角 P Q R D E F ->
   角度小于 A B C P Q R.
Proof.
intros.
rename_H H;let Tf:=fresh in
assert (Tf:exists G H J, (BetS G H J /\ Out E D G /\ Out E F J /\ 等角 A B C D E H)) by (conclude_def 角度小于 );destruct Tf as [G[H[J]]];spliter.
assert ((neq P Q /\ neq Q R /\ neq P R /\ neq D E /\ neq E F /\ neq D F)) by (forward_using lemma_angledistinct).
assert (neq Q P) by (conclude lemma_inequalitysymmetric).
assert ((neq A B /\ neq B C /\ neq A C /\ neq D E /\ neq E H /\ neq D H)) by (forward_using lemma_angledistinct).
assert (neq E G) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists U, (Out Q P U /\ Cong Q U E G)) by (conclude lemma_layoff);destruct Tf as [U];spliter.
assert (neq E J) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists V, (Out Q R V /\ Cong Q V E J)) by (conclude lemma_layoff);destruct Tf as [V];spliter.
assert (Cong G H G H) by (conclude cn_congruencereflexive).
assert (Lt G H G J) by (conclude_def Lt ).
assert (等角 D E F P Q R) by (conclude lemma_equalanglessymmetric).
assert (等角 D E F U Q V) by (conclude lemma_equalangleshelper).
assert (等角 U Q V D E F) by (conclude lemma_equalanglessymmetric).
assert (等角 U Q V G E J) by (conclude lemma_equalangleshelper).
assert (等角 G E J U Q V) by (conclude lemma_equalanglessymmetric).
assert (Cong E G Q U) by (conclude lemma_congruencesymmetric).
assert (Cong E J Q V) by (conclude lemma_congruencesymmetric).
assert ((Cong G J U V /\ 等角 E G J Q U V /\ 等角 E J G Q V U)) by (conclude proposition_04).
assert (Cong U V G J) by (conclude lemma_congruencesymmetric).
assert (neq G J) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists W, (BetS U W V /\ Cong U W G H)) by (conclude proposition_03);destruct Tf as [W];spliter.
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Out E H H) by (conclude lemma_ray4).
assert (等角 A B C G E H) by (conclude lemma_equalangleshelper).
assert (nCol G E H) by (conclude lemma_equalanglesNC).
assert (nCol G H E) by (forward_using lemma_NCorder).
assert (neq U V) by (forward_using lemma_betweennotequal).
assert (Out U V W) by (conclude lemma_ray4).
assert (eq Q Q) by (conclude cn_equalityreflexive).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (nCol U Q V) by (conclude lemma_equalanglesNC).
assert (neq U Q) by (forward_using lemma_NCdistinct).
assert (Out U Q Q) by (conclude lemma_ray4).
assert (~ eq G E).
 {
 intro.
 assert (Col G H E) by (conclude_def Col ).
 contradict.
 }
assert (Out G E E) by (conclude lemma_ray4).
assert (等角 E G J Q U W) by (conclude lemma_equalangleshelper).
assert (等角 Q U W E G J) by (conclude lemma_equalanglessymmetric).
assert (Out G J H) by (conclude lemma_ray4).
assert (等角 Q U W E G H) by (conclude lemma_equalangleshelper).
assert (等角 E G H Q U W) by (conclude lemma_equalanglessymmetric).
assert (nCol Q U W) by (conclude lemma_equalanglesNC).
assert (nCol U W Q) by (forward_using lemma_NCorder).
assert (nCol H G E) by (forward_using lemma_NCorder).
assert (~ Col W U Q).
 {
 intro.
 assert (Col U W Q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Cong G H U W) by (conclude lemma_congruencesymmetric).
assert (Cong G E U Q) by (forward_using lemma_congruenceflip).
assert (等角 E G H Q U W) by (conclude lemma_equalanglessymmetric).
assert (等角 Q U W W U Q) by (conclude lemma_ABCequalsCBA).
assert (等角 E G H W U Q) by (conclude lemma_equalanglestransitive).
assert (等角 H G E E G H) by (conclude lemma_ABCequalsCBA).
assert (等角 H G E W U Q) by (conclude lemma_equalanglestransitive).
assert ((Cong H E W Q /\ 等角 G H E U W Q /\ 等角 G E H U Q W)) by (conclude proposition_04).
assert (等角 A B C U Q W) by (conclude lemma_equalanglestransitive).
assert (eq W W) by (conclude cn_equalityreflexive).
assert (~ eq Q W).
 {
 intro.
 assert (Col Q U W) by (conclude_def Col ).
 assert (Col W U Q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out Q W W) by (conclude lemma_ray4).
assert (Out Q U P) by (conclude lemma_ray5).
assert (等角 A B C P Q W) by (conclude lemma_equalangleshelper).
assert (角度小于 A B C P Q R) by (conclude_def 角度小于 ).
close.
Qed.

End Euclid.
