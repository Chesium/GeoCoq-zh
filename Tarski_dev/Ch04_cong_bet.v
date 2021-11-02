Require Export GeoCoq.Tarski_dev.Ch03_bet.
Require Export GeoCoq.Tarski_dev.Tactics.CongR.

Ltac CongR :=
 let tpoint := constr:(Tpoint) in
 let cong := constr:(Cong) in
   treat_equalities; unfold 中点 in *; spliter; Cong; Cong_refl tpoint cong.

Section T3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l4_2 : forall A B C D A' B' C' D', 内五线段形式 A B C D A' B' C' D' -> Cong B D B' D'.
Proof.
unfold 内五线段形式.
intros.
spliter.

induction (两点重合的决定性 A C).

treat_equalities;assumption.

assert (exists E, Bet A C E /\ C <> E)
 by apply point_construction_different.
ex_and H6 E.
prolong A' C' E' C E.

assert  (Cong E D E' D')
 by (
  apply (五线段公理_等价SAS_with_def A C E D A' C' E' D');[
  unfold 外五线段形式;  repeat split;Cong|
  assumption]).

apply (五线段公理_等价SAS_with_def E C B D E' C' B' D').
unfold 外五线段形式.
repeat split; try solve [eBetween| Cong ].
auto.
Qed.

Lemma l4_3 : forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A C A' C' -> Cong B C B' C' -> Cong A B A' B'.
Proof.
intros.
apply 等长的交换性.
apply (l4_2 A B C A A' B' C' A').
unfold 内五线段形式.
repeat split;Cong.
Qed.

Lemma l4_3_1 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C'.
Proof.
    intros.
    apply 等长的交换性.
    eapply l4_3;eBetween;Cong.
Qed.

Lemma l4_5 : forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Bet A' B' C' /\ 三角形全等 A B C A' B' C'.
Proof.
intros.
unfold 三角形全等.

assert (exists D', Bet C' A' D' /\ A' <> D')
 by (apply point_construction_different).
ex_and H1 x'.
prolong x' A' B' A B.
prolong x' B' C'' B C.

assert (Bet A' B' C'') by eBetween.

assert (C'' = C').
eapply (点的唯一构造 x' A' ).

auto.
eBetween.

apply (两组连续三点分段等则全体等 A' B' C'' A B C);Between.

eBetween.
Cong.

subst C''.
exists B'.
repeat split;Cong.
Qed.

Lemma l4_6 : forall A B C A' B' C', Bet A B C -> 三角形全等 A B C A' B' C' -> Bet A' B' C'.
Proof.
unfold 三角形全等.
intros.
assert (exists B'', Bet A' B'' C' /\ 三角形全等 A B C A' B'' C')
  by (eapply l4_5;intuition).
ex_and H1 x.
unfold 三角形全等 in *;spliter.

assert (三角形全等 A' x C' A' B' C').
  unfold 三角形全等;repeat split; Cong.
  apply 等长的传递性 with A B; Cong.
  apply 等长的传递性 with B C; Cong.
unfold 三角形全等 in H7;spliter.

assert (内五线段形式 A' x C' x  A' x C' B')
 by (unfold 内五线段形式;repeat split;Cong).
assert (Cong x x x B')
 by (eapply l4_2;apply H10).
treat_equalities.
Between.
Qed.

Lemma cong3_bet_eq : forall  A B C X,
 Bet A B C -> 三角形全等 A B C A X C -> X = B.
Proof.
unfold 三角形全等.
intros.
spliter.
assert (内五线段形式 A B C B A B C X)
 by (unfold 内五线段形式;intuition).
assert (Cong B B B X)
 by (apply (l4_2 _ _ _ _ _ _ _ _ H3)).
treat_equalities.
Between.
Qed.

End T3.
