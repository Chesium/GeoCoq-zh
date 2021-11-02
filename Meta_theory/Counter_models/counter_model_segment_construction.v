Require Export GeoCoq.Axioms.tarski_axioms.

Section 由一点往一方向构造等长线段_independent.

Inductive Point :=
 P0.

Definition Bet (A B C : Point) := False.

Definition Cong (A B C D : Point) := True.

Lemma 中间性的同一律 : forall A B, Bet A B A -> A=B.
Proof.
unfold Bet; tauto.
Qed.


Lemma 等长的伪自反性 : forall A B, Cong A B B A.
Proof.
unfold Cong; tauto.
Qed.

Lemma 等长的同一性 : forall A B C, Cong A B C C -> A = B.
Proof.
destruct A; destruct B; reflexivity.
Qed.

Lemma 等长的内传递性 : forall A B C D E F,
  Cong A B C D -> Cong A B E F -> Cong C D E F.
Proof.
unfold Cong; tauto.
Qed.

Lemma 帕施公理 : forall A B C P Q,
  Bet A P C -> Bet B Q C ->
  exists x, Bet P x B /\ Bet Q x A.
Proof.
unfold Bet; tauto.
Qed.

Lemma 五线段公理_等价SAS : forall A A' B B' C C' D D',
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.
Proof.
unfold Bet, Cong; tauto.
Qed.

Lemma not_由一点往一方向构造等长线段 : ~ (forall A B C D,
  exists E, Bet A B E /\ Cong B E C D).
Proof.
intro.
unfold Bet in *.
assert (T:= H P0 P0 P0 P0).
destruct T.
tauto.
Qed.

Lemma 防降维公理 : exists A, exists B, exists C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists P0.
exists P0.
exists P0.
unfold Bet;tauto.
Qed.

Lemma 防升维公理 : forall A B C P Q ,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros.
destruct P.
destruct Q.
tauto.
Qed.

Lemma euclid : forall A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) -> exists CC, Cong A CC B CC /\ Cong A CC C CC.
Proof.
intros.
exists P0.
unfold Cong;tauto.
Qed.

End 由一点往一方向构造等长线段_independent.
