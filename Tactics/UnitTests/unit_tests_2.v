Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section UnitTests.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Goal forall A B C D E F G H:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> True.
Proof.
intros.
first [not_exist_hyp4 A B C D E F G H | clear H0].
first [not_exist_hyp4 A B C D E F G H | clear H1].
not_exist_hyp4 A B C D E F G H.
auto.
Qed.

Goal forall A B C D E F G H:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> True.
Proof.
intros.
first [not_exist_hyp4 A B C D E F G H | clear H2].
first [not_exist_hyp4 A B C D E F G H | clear H3].
not_exist_hyp4 A B C D E F G H.
auto.
Qed.

Goal forall A B C D E F G H:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> True.
Proof.
intros.
first [not_exist_hyp4 A B C D E F G H | clear H4].
first [not_exist_hyp4 A B C D E F G H | clear H5].
not_exist_hyp4 A B C D E F G H.
auto.
Qed.

Goal forall A B C D E F G H:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> True.
Proof.
intros.
first [not_exist_hyp4 A B C D E F G H | clear H6].
first [not_exist_hyp4 A B C D E F G H | clear H7].
not_exist_hyp4 A B C D E F G H.
auto.
Qed.

Goal forall A B C D E F, 等角 A B C D E F -> A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C P, 在角内 P A B C -> A <> B /\ C <> B /\ P <> B.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D E F, 角度小于等于 A B C D E F -> A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D E F, 角度小于 A B C D E F -> A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C, 为锐角 A B C -> A <> B /\ C <> B.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C, 为钝角 A B C -> A <> B /\ C <> B.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D E F, 互为补角 A B C D E F -> A <> B /\ B <> C /\ D <> E /\ E <> F.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.


Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H0].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H1].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.

Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H2].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H3].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.

Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H4].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H5].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.

Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H6].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H7].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.

Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H8].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H9].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.

Goal forall A B C D E F G H I J K L:Tpoint, A<>B -> B<>A -> C<>D -> D<>C ->
 E<>F -> F<>E -> G<>H -> H<>G -> I<>J -> J<>I -> K<>L -> L<>K -> True.
Proof.
intros.
first [not_exist_hyp6 A B C D E F G H I J K L | clear H10].
first [not_exist_hyp6 A B C D E F G H I J K L | clear H11].
not_exist_hyp6 A B C D E F G H I J K L.
auto.
Qed.


Goal forall A B C D E F G H I, 和角 A B C D E F G H I ->
 A <> B /\ B <> C /\ D <> E /\ E <> F /\ G <> H /\ H <> I.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D E F, 三角形内角和 A B C D E F ->
 A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D E F, 和角不大于平角 A B C D E F -> A <> B /\ B <> C /\ D <> E /\ E <> F.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C D, ~ 共面 A B C D ->
  A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D. 
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C U V X, 垂直平面于 X A B C U V -> A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

Goal forall A B C U V, Orth A B C U V -> A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
intros.
统计不重合点.
repeat split; assumption.
Qed.

End UnitTests.