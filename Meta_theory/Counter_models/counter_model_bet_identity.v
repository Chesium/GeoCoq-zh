Require Export GeoCoq.Axioms.tarski_axioms.

(** This proves that 中间性的同一律 is independent from other axioms of neutral geometry. *)

Section 中间性的同一律_independent.

Inductive Point :=
  P0 | P1 | P2 | P3.

Definition Bet (A B C : Point) :=
  A = B \/ B = C \/ A = C.

Definition Cong (A B C D : Point) :=
  (A = B /\ C = D) \/ (A <> B /\ C <> D).

Lemma not_中间性的同一律 : ~ (forall A B, Bet A B A -> A=B).
Proof.
intro.
assert (T:= H P0 P1).
assert (P0=P1).
apply T.
unfold Bet;tauto.
discriminate.
Qed.

Lemma 等长的伪自反性 : forall A B, Cong A B B A.
Proof.
unfold Cong;intros;destruct A; destruct B;try
tauto;
right;split;discriminate.
Qed.

Lemma 等长的同一性 : forall A B C, Cong A B C C -> A = B.
Proof.
unfold Cong.
intros.
tauto.
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
unfold Bet; intros.
intuition;subst;
try (exists P;tauto);
try (exists Q;tauto);
exists C;tauto.
Qed.

Lemma 五线段公理_等价SAS : forall A A' B B' C C' D D',
  Cong A B A' B' ->
  Cong B C B' C' ->
  Cong A D A' D' ->
  Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B -> Cong C D C' D'.
Proof.
unfold Bet, Cong;intros.
intuition;repeat subst;tauto.
Qed.

Lemma point_eq_dec : forall A B : Point, A=B \/ A<>B.
Proof.
intros.
destruct A; destruct B;try tauto;right;discriminate.
Qed.

Lemma 由一点往一方向构造等长线段 : forall A B C D,
  exists E, Bet A B E /\ Cong B E C D.
Proof.
intros.
unfold Bet, Cong.

elim (point_eq_dec C D).
intros.
exists B.
tauto.
intros.
elim (point_eq_dec A B).
intro;subst.
destruct B; try (exists P0; split; try tauto; right; split; try discriminate; assumption);
exists P1; split; try tauto; right; split; try discriminate; assumption.

intros; exists A; firstorder.
Qed.

Lemma 防降维公理 : exists A, exists B, exists C, ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists P0.
exists P1.
exists P2.
unfold Bet.
intro.
intuition discriminate.
Qed.

Lemma cong_sym : forall A B C D, Cong A B C D -> Cong C D A B.
Proof.
unfold Cong.
intros;tauto.
Qed.

Lemma cong_aux : forall A, Cong A P0 A P1 -> A = P2 \/ A = P3.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma cong_aux_2 : forall A, Cong A P0 A P2 -> A = P1 \/ A = P3.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma cong_aux_3 : forall A, Cong A P1 A P2 -> A = P0 \/ A = P3.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma cong_aux_4 : forall A, Cong A P0 A P3 -> A = P1 \/ A = P2.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma cong_aux_5 : forall A, Cong A P1 A P3 -> A = P0 \/ A = P2.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma cong_aux_6 : forall A, Cong A P2 A P3 -> A = P0 \/ A = P1.
Proof.
intros.
destruct A;unfold Cong in *;
intuition;congruence.
Qed.

Lemma 防升维公理 : forall A B C P Q ,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
intros.
destruct P; destruct Q; try solve [intuition];
try (apply cong_aux in H0; apply cong_aux in H1; apply cong_aux in H2);
try (apply cong_aux_2 in H0; apply cong_aux_2 in H1; apply cong_aux_2 in H2);
try (apply cong_aux_3 in H0; apply cong_aux_3 in H1; apply cong_aux_3 in H2);
try (apply cong_aux_4 in H0; apply cong_aux_4 in H1; apply cong_aux_4 in H2);
try (apply cong_aux_5 in H0; apply cong_aux_5 in H1; apply cong_aux_5 in H2);
try (apply cong_aux_6 in H0; apply cong_aux_6 in H1; apply cong_aux_6 in H2);
try (apply cong_sym in H0; apply cong_sym in H1; apply cong_sym in H2);
try (apply cong_aux in H0; apply cong_aux in H1; apply cong_aux in H2);
try (apply cong_aux_2 in H0; apply cong_aux_2 in H1; apply cong_aux_2 in H2);
try (apply cong_aux_3 in H0; apply cong_aux_3 in H1; apply cong_aux_3 in H2);
try (apply cong_aux_4 in H0; apply cong_aux_4 in H1; apply cong_aux_4 in H2);
try (apply cong_aux_5 in H0; apply cong_aux_5 in H1; apply cong_aux_5 in H2);
try (apply cong_aux_6 in H0; apply cong_aux_6 in H1; apply cong_aux_6 in H2);
intuition; subst; unfold Bet; tauto.
Qed.

Lemma not_bet_diff : forall A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) -> A <> B /\ B <> C /\ A <> C.
Proof.
unfold Bet; intros.
destruct A; destruct B; destruct C; intuition.
Qed.

Lemma euclid : forall A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) -> exists CC, Cong A CC B CC /\ Cong A CC C CC.
Proof.
intros.
apply not_bet_diff in H; 分离合取式; unfold Cong.
destruct A; destruct B; destruct C; try tauto;
try (exists P3; split; right; split; discriminate);
try (exists P2; split; right; split; discriminate);
try (exists P1; split; right; split; discriminate);
exists P0; split; right; split; discriminate.
Qed.

End 中间性的同一律_independent.
