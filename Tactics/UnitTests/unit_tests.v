Require Import GeoCoq.Tarski_dev.Annexes.quadrilaterals_inter_dec.

Section UnitTests.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Goal forall A B I, A <> B -> 中点 I A B -> I <> A /\ I <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, B <> A -> 中点 I A B -> I <> A /\ I <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, I<>A -> 中点 I A B -> I <> B /\ A <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, I<>B -> 中点 I A B -> I <> A /\ A <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, A<>I -> 中点 I A B -> I <> B /\ A <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, B<>I -> 中点 I A B -> I <> A /\ A <> B.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B I, A<>B -> 中点 I A B -> A <> I /\ I <> B.
Proof.
intros.
统计不重合点.
split;auto.
Qed.

Goal forall A B:Tpoint, A<>B -> B<>A -> True.
Proof.
intros.
first [not_exist_hyp_comm A B | clear H].
first [not_exist_hyp_comm A B | clear H0].
not_exist_hyp_comm A B.
auto.
Qed.

Goal forall A B C, Col A B C -> Col A C B -> Col B A C -> Col B C A -> Col C A B -> Col C B A -> True.
Proof.
intros.
first [not_exist_hyp_perm_col A B C | clear H].
first [not_exist_hyp_perm_col A B C | clear H0].
first [not_exist_hyp_perm_col A B C | clear H1].
first [not_exist_hyp_perm_col A B C | clear H2].
first [not_exist_hyp_perm_col A B C | clear H3].
first [not_exist_hyp_perm_col A B C | clear H4].
not_exist_hyp_perm_col A B C.
auto.
Qed.

Goal forall A B C, ~ Col A B C -> ~ Col A C B ->
  ~ Col B A C -> ~ Col B C A -> ~ Col C A B -> ~ Col C B A -> True.
Proof.
intros.
first [not_exist_hyp_perm_ncol A B C | clear H].
first [not_exist_hyp_perm_ncol A B C | clear H0].
first [not_exist_hyp_perm_ncol A B C | clear H1].
first [not_exist_hyp_perm_ncol A B C | clear H2].
first [not_exist_hyp_perm_ncol A B C | clear H3].
first [not_exist_hyp_perm_ncol A B C | clear H4].
not_exist_hyp_perm_ncol A B C.
auto.
Qed.

Goal forall A B C Q,
 B <> A -> Col A B C -> 中点 Q A C ->
 A <> C -> B <> C -> 中点 A B C ->
 Q <> C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, A<>B -> Per A B C -> A<>C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, B<>A -> Per A B C -> A<>C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, B<>C -> Per A B C -> A<>C.
Proof.
intros.
统计不重合点.
auto.
Qed.

Goal forall A B C, C<>B -> Per A B C -> A<>C.
Proof.
intros.
统计不重合点.
auto.
Qed.

Goal forall A B C D, Perp A B C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp A B C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp B A C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;intuition.
Qed.

Goal forall A B C D, A<>B -> C<>D -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;intuition.
Qed.

Goal forall A B C D, D<>C -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;intuition.
Qed.

Goal forall X A B C D, 垂直于 X A B C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C D, Par A B C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C D, 严格平行 A B C D -> A<>B /\ C<>D.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C, Out A B C -> B<>A /\ C<>A.
Proof.
intros.
统计不重合点.
split;assumption.
Qed.

Goal forall A B C, Out A B C -> Col B A C.
Proof.
intros.
assert_cols.
Col.
Qed.

Goal forall A B C D, ~ Col A B C -> ~ Col A B D ->
  A<>D.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D I,
  中点 I A B -> Par A B C D -> I<>A.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C D I,
  中点 I A B -> Par A I C D -> B<>A.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> C<>D -> A<>B.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> D<>C -> A<>B.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> A<>B -> C<>D.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> B<>A -> C<>D.
Proof.
intros.
统计不重合点.
intuition.
Qed.

Goal forall A B C D E,
 ~ Col A B C ->
 ~ Col B D E -> A<>B ->
  Col A B D -> Col A B E -> Col A B C.
Proof.
intros.
search_contradiction.
Qed.
(*
Goal forall  A B C D E,
 ~ Col A B C ->
 ~ Col B D E -> A<>B ->
  Col A B D -> Col A B E -> C<>D.
Proof.
intros.
统计不重合点.
assert_all_diffs_by_contradiction'.
finish.
Qed.
*)

Goal forall A B C D X,
 Inter A B C D X ->
 A <> B /\ C <> D.
Proof.
intros.
统计不重合点.
split; auto.
Qed.

Goal forall A B C D,
 严格平行 A B C D ->
 A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.
Proof.
intros.
统计不重合点.
repeat split; auto.
Qed.

Goal forall A B C, (A<>B -> B<>C -> A<>C -> Col A B C) -> Col A B C.
Proof.
intros.
统计不重合点_by_cases.
intuition.
Qed.
(*
Goal forall A B C D I, I <> A -> I <> B -> I <> C -> I <> D -> Col I A B -> Col I C D -> ~ Col A B C -> ~ Col A B D.
Proof.
intros.
统计不重合点.
assert_all_not_cols_by_contradiction.
finish.
Qed.

Goal forall A B C D I, I <> A -> I <> B -> I <> C -> I <> D -> Col I A B -> Col I C D -> ~ Col A B C ->  A <> D.
Proof.
intros.
统计不重合点.
assert_all_diffs_by_contradiction'.
finish.
Qed.
*)

Goal forall A B C, 中点 A B C -> Cong A B C A.
Proof.
intros.
assert_congs_perm.
finish.
Qed.

Goal forall A B C, Bet A B C -> A <> B -> A <> C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, Bet A B C -> B <> A -> A <> C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, Bet A B C -> B <> C -> A <> C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, Bet A B C -> C <> B -> A <> C.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, ~ Bet A B C -> A <> B /\ B <> C.
Proof.
intros.
统计不重合点.
split; assumption.
Qed.

Goal forall A B C D, TS A B C D -> A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D, OS A B C D -> A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D, 严格平行四边形 A B C D ->
  A <> B /\ B <> C /\ C <> D /\ D <> A /\ A <> C /\ B <> D.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D, A <> B -> Le A B C D -> C <> D.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C D, Lt A B C D -> C <> D.
Proof.
intros.
统计不重合点.
assumption.
Qed.

Goal forall A B C, Bet A B C -> Bet B A C -> A = B.
Proof.
intros.
treat_equalities.
trivial.
Qed.

Goal forall A B C, Bet A B C -> Bet A C B -> B = C.
Proof.
intros.
treat_equalities.
trivial.
Qed.

Goal forall A B C, Bet A B C -> Bet C A B -> A = B.
Proof.
intros.
treat_equalities.
trivial.
Qed.

Goal forall A B C, Bet A B C -> Bet B C A -> B = C.
Proof.
intros.
treat_equalities.
trivial.
Qed.

Goal forall A B X Y, TS A B X Y -> ~ Col A B X /\ ~ Col A B Y.
Proof.
intros.
assert_ncols.
split; assumption.
Qed.

Goal forall A B X Y, OS A B X Y -> ~ Col A B X /\ ~ Col A B Y.
Proof.
intros.
assert_ncols.
split; assumption.
Qed.

Goal forall A B C D, ~ 共面 A B C D ->
  ~ Col A B C /\ ~ Col A B D /\ ~ Col A C D /\ ~ Col B C D.
Proof.
intros.
assert_ncols.
repeat split; assumption.
Qed.

Goal forall A B C D, 严格平行 A B C D ->
  ~ Col A B C /\ ~ Col B C D /\ ~ Col C D A /\ ~ Col A B D.
Proof.
intros.
assert_ncols.
repeat split; assumption.
Qed.

Goal forall A B C D, 严格平行四边形 A B C D ->
  ~ Col A B C /\ ~ Col B C D /\ ~ Col C D A /\ ~ Col A B D.
Proof.
intros.
assert_ncols.
repeat split; assumption.
Qed.

Goal forall A B C D, Col A B C \/ Col A B D \/ Col A C D \/ Col B C D -> 共面 A B C D.
Proof.
intros A B C D [|[|[|]]];
Cop.
Qed.

End UnitTests.

Section UnitTestsEucl.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Goal forall A B C D, 平行四边形 A B C D -> Cong A B C D.
Proof.
intros.
assert_congs_perm.
finish.
Qed.

End UnitTestsEucl.