Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy1.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_26A : 
   forall A B C D E F, 
   Triangle A B C -> Triangle D E F -> 等角 A B C D E F -> 等角 B C A E F D -> Cong B C E F ->
   Cong A B D E /\ Cong A C D F /\ 等角 B A C E D F.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ Lt D E A B).
 {
 intro.
 assert (Cong A B B A) by (conclude cn_equalityreverse).
 assert (Lt D E B A) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists G, (BetS B G A /\ Cong B G D E)) by (conclude_def Lt );destruct Tf as [G];spliter.
 assert (neq B G) by (forward_using lemma_betweennotequal).
 assert (Cong B G E D) by (forward_using lemma_congruenceflip).
 assert (Out B A G) by (conclude lemma_ray4).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Out B C C) by (conclude lemma_ray4).
 assert (Cong G C G C) by (conclude cn_congruencereflexive).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Out B G G) by (conclude lemma_ray4).
 assert (Cong B G B G) by (conclude cn_congruencereflexive).
 assert (Cong B C B C) by (conclude cn_congruencereflexive).
 assert (等角 A B C G B C) by (conclude_def 等角 ).
 assert (等角 G B C A B C) by (conclude lemma_equalanglessymmetric).
 assert (等角 G B C D E F) by (conclude lemma_equalanglestransitive).
 assert ((Cong G C D F /\ 等角 B G C E D F /\ 等角 B C G E F D)) by (conclude proposition_04).
 assert (等角 E F D B C A) by (conclude lemma_equalanglessymmetric).
 assert (等角 B C G B C A) by (conclude lemma_equalanglestransitive).
 assert (等角 B C A B C G) by (conclude lemma_equalanglessymmetric).
 assert (Out C B B) by (conclude lemma_ray4).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Out C A A) by (conclude lemma_ray4).
 assert (角度小于 B C A B C A) by (conclude_def 角度小于 ).
 assert (~ 角度小于 B C A B C A) by (conclude lemma_angletrichotomy).
 contradict.
 }
assert (~ Lt A B D E).
 {
 intro.
 assert (Cong D E E D) by (conclude cn_equalityreverse).
 assert (Lt A B E D) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists G, (BetS E G D /\ Cong E G A B)) by (conclude_def Lt );destruct Tf as [G];spliter.
 assert (Cong E G B A) by (forward_using lemma_congruenceflip).
 assert (neq E D) by (forward_using lemma_betweennotequal).
 assert (Out E D G) by (conclude lemma_ray4).
 assert (eq D D) by (conclude cn_equalityreflexive).
 assert (eq F F) by (conclude cn_equalityreflexive).
 assert (nCol D E F) by (conclude_def Triangle ).
 assert (~ eq E F).
  {
  intro.
  assert (Col D E F) by (conclude_def Col ).
  contradict.
  }
 assert (Out E F F) by (conclude lemma_ray4).
 assert (Cong G F G F) by (conclude cn_congruencereflexive).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (neq E G) by (conclude lemma_raystrict).
 assert (Out E G G) by (conclude lemma_ray4).
 assert (Cong E G E G) by (conclude cn_congruencereflexive).
 assert (Cong E F E F) by (conclude cn_congruencereflexive).
 assert (等角 D E F G E F) by (conclude_def 等角 ).
 assert (等角 G E F D E F) by (conclude lemma_equalanglessymmetric).
 assert (等角 D E F A B C) by (conclude lemma_equalanglessymmetric).
 assert (等角 G E F A B C) by (conclude lemma_equalanglestransitive).
 assert (Cong E F B C) by (conclude lemma_congruencesymmetric).
 assert ((Cong G F A C /\ 等角 E G F B A C /\ 等角 E F G B C A)) by (conclude proposition_04).
 assert (等角 E F G E F D) by (conclude lemma_equalanglestransitive).
 assert (等角 E F D E F G) by (conclude lemma_equalanglessymmetric).
 assert (nCol E F G) by (conclude lemma_equalanglesNC).
 assert (等角 E F G E F G) by (conclude lemma_equalanglesreflexive).
 assert (neq E F) by (forward_using lemma_angledistinct).
 assert (neq F E) by (conclude lemma_inequalitysymmetric).
 assert (Out F E E) by (conclude lemma_ray4).
 assert (neq F D) by (forward_using lemma_angledistinct).
 assert (Out F D D) by (conclude lemma_ray4).
 assert (角度小于 E F D E F D) by (conclude_def 角度小于 ).
 assert (~ 角度小于 E F D E F D) by (conclude lemma_angletrichotomy).
 contradict.
 }
assert (~ eq D E).
 {
 intro.
 assert (Col D E F) by (conclude_def Col ).
 assert (nCol D E F) by (conclude_def Triangle ).
 contradict.
 }
assert (Cong A B D E) by (conclude lemma_trichotomy1).
assert (Cong B A E D) by (forward_using lemma_congruenceflip).
assert ((Cong A C D F /\ 等角 B A C E D F /\ 等角 B C A E F D)) by (conclude proposition_04).
close.
Qed.

End Euclid.
