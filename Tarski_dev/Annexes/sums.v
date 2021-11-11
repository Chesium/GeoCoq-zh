Require Export GeoCoq.Tarski_dev.Ch06_out_lines.

Section Sums.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** Existence of the sum *)

Lemma 长度之和的存在性 : forall A B C D, exists E F, 长度之和 A B C D E F.
Proof.
  intros A B C D.
  destruct (由一点往一方向构造等长线段 A B C D) as [R [HR1 HR2]].
  exists A, R, A, B, R.
  repeat split; Cong.
Qed.

(** Commutativity of the sum. *)

Lemma 长度之和的对称性 : forall A B C D E F, 长度之和 A B C D E F -> 长度之和 C D A B E F.
Proof.
  intros A B C D E F H长度之和.
  destruct H长度之和 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  exists R, Q, P.
  repeat split; Between; Cong.
Qed.

(** Unicity of the sum. *)

Lemma 长度之和的唯一性 : forall A B C D E F E' F', 长度之和 A B C D E F -> 长度之和 A B C D E' F' ->
  Cong E F E' F'.
Proof.
  intros A B C D E F E' F' H长度之和 H长度之和'.
  destruct H长度之和 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct H长度之和' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply 等长的传递性 with P R; Cong.
  apply 等长的传递性 with P' R'; trivial.
  apply 两组连续三点分段等则全体等 with Q Q'; trivial.
  apply 等长的传递性 with A B; Cong.
  apply 等长的传递性 with C D; Cong.
Qed.

(** Unicity of the difference of segments. *)

Lemma 长度被加数的唯一性 : forall A B C D E F A' B', 长度之和 A B C D E F -> 长度之和 A' B' C D E F ->
  Cong A B A' B'.
Proof.
  intros A B C D E F A' B' H长度之和 H长度之和'.
  destruct H长度之和 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct H长度之和' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply 等长的传递性 with P Q; Cong.
  apply 等长的传递性 with P' Q'; trivial.
  apply l4_3 with R R'; trivial.
  apply 等长的传递性 with E F; Cong.
  apply 等长的传递性 with C D; Cong.
Qed.

(** Unicity of the difference of segments on the right. *)

Lemma 长度加数的唯一性 : forall A B C D E F C' D', 长度之和 A B C D E F -> 长度之和 A B C' D' E F ->
  Cong C D C' D'.
Proof.
  intros A B C D E F C' D' H长度之和 H长度之和'.
  apply 长度被加数的唯一性 with A B E F; apply 长度之和的对称性; trivial.
Qed.

(** Cong preserves 长度之和 *)

Lemma 等长保持长度之和性质 : forall A B C D E F A' B' C' D' E' F',
  Cong A B A' B' -> Cong C D C' D' -> Cong E F E' F' -> 长度之和 A B C D E F ->
  长度之和 A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HCong1 HCong2 HCong3 H长度之和.
  destruct H长度之和 as [P [Q [R [HBet [HCong4 [HCong5 HCong6]]]]]].
  exists P, Q, R; repeat split; trivial; eapply 等长的传递性; eauto.
Qed.

(** The degenerate segments represent the additive identity *)

Lemma 长度加零长不变 : forall A B C, 长度之和 A B C C A B.
Proof.
  intros A B C.
  exists A, B, B.
  repeat split; Between; Cong.
Qed.

Lemma 长度加零长与原长等长 : forall A B C D E, 长度之和 A B C C D E -> Cong A B D E.
Proof.
  intros A B C D E HSum.
  apply (长度之和的唯一性 A B C C); trivial.
  apply 长度加零长不变.
Qed.
(* 无用 *)
Lemma 长度加一长不变则该长两端点重合 : forall A B C D, 长度之和 A B C D A B -> C = D.
Proof.
  intros A B C D HSum.
  apply 等长的同一性 with C.
  apply 长度加数的唯一性 with A B A B; trivial.
  apply 长度加零长不变.
Qed.

Lemma 零长加一长仍为该长 : forall A B C, 长度之和 A A B C B C.
Proof.
  intros; apply 长度之和的对称性, 长度加零长不变.
Qed.

Lemma 零长加一长仍与该长等长 : forall A B C D E, 长度之和 A A B C D E -> Cong B C D E.
Proof.
  intros A B C D E HSum.
  apply (长度之和的唯一性 A A B C); trivial.
  apply 零长加一长仍为该长.
Qed.
(* 无用 *)
Lemma 一长加长度不变则该长两端点重合 : forall A B C D, 长度之和 A B C D C D -> A = B.
Proof.
  intros A B C D HSum.
  apply 等长的同一性 with A.
  apply 长度被加数的唯一性 with C D C D; trivial.
  apply 零长加一长仍为该长.
Qed.

(** Some permutation properties *)

Lemma 长度之和的左交换性 : forall A B C D E F, 长度之和 A B C D E F -> 长度之和 B A C D E F.
Proof.
  intros A B C D E F H长度之和.
  apply (等长保持长度之和性质 A B C D E F); Cong.
Qed.

Lemma 长度之和的中交换性 : forall A B C D E F, 长度之和 A B C D E F -> 长度之和 A B D C E F.
Proof.
  intros; apply 长度之和的对称性, 长度之和的左交换性, 长度之和的对称性; trivial.
Qed.

Lemma 长度之和的右交换性 : forall A B C D E F, 长度之和 A B C D E F -> 长度之和 A B C D F E.
Proof.
  intros A B C D E F H长度之和.
  apply (等长保持长度之和性质 A B C D E F); Cong.
Qed.

Lemma 长度之和的交换性 : forall A B C D E F, 长度之和 A B C D E F -> 长度之和 B A D C F E.
Proof.
  intros; apply 长度之和的左交换性, 长度之和的中交换性, 长度之和的右交换性; trivial.
Qed.

(** Basic case of sum *)

Lemma 中间性蕴含长度之和 : forall A B C, Bet A B C -> 长度之和 A B B C A C.
Proof.
  intros A B C HBet.
  exists A, B, C; repeat split; Cong.
Qed.

(* (AB+CD)+EF=KL=AB+(CD+EF) *)
Lemma 长度之和的结合律1 : forall A B C D E F G H I J K L,
  长度之和 A B C D G H -> 长度之和 C D E F I J -> 长度之和 G H E F K L ->
  长度之和 A B I J K L.
Proof.
  intros A B C D E F G H I J K L H长度之和1 H长度之和2 H长度之和3.
  destruct H长度之和1 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct (由一点往一方向构造等长线段 P R E F) as [S [HS1 HS2]].
  exists P, Q, S; repeat split; trivial.
  - apply 中间性的交换传递性2 with R; trivial.
  - apply (长度之和的唯一性 C D E F); trivial.
    exists Q, R, S; repeat split; Cong.
    apply 中间性的交换传递性1 with P; trivial.
  - apply (长度之和的唯一性 G H E F); trivial.
    exists P, R, S; repeat split; Cong.
Qed.
(* AB+(CD+EF)=KL=(AB+CD)+EF *)
Lemma 长度之和的结合律2 : forall A B C D E F G H I J K L,
  长度之和 A B C D G H -> 长度之和 C D E F I J -> 长度之和 A B I J K L ->
  长度之和 G H E F K L.
Proof.
  intros A B C D E F G H I J K L H长度之和1 H长度之和2 H长度之和3.
  apply 长度之和的对称性, 长度之和的结合律1 with C D A B I J; apply 长度之和的对称性; trivial.
Qed.

(** Associativity of the sum. *)

Lemma 长度之和的结合律 : forall A B C D E F G H I J K L,
  长度之和 A B C D G H -> 长度之和 C D E F I J ->
  (长度之和 G H E F K L <-> 长度之和 A B I J K L).
Proof.
  intros A B C D E F G H I J K L H长度之和1 H长度之和2.
  split; intro H长度之和3.
  - apply 长度之和的结合律1 with C D E F G H; trivial.
  - apply 长度之和的结合律2 with A B C D I J; trivial.
Qed.

(** AB <= AB + CD *)

Lemma 原长小于等于和长 : forall A B C D E F, 长度之和 A B C D E F -> Le A B E F.
Proof.
  intros A B C D E F H长度之和.
  destruct H长度之和 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  apply (l5_6_等长保持小于等于关系 P Q P R); trivial.
  exists Q; Cong.
Qed.

(** CD <= AB + CD *)

Lemma 加长小于等于和长 : forall A B C D E F, 长度之和 A B C D E F -> Le C D E F.
Proof.
  intros A B C D E F H长度之和.
  apply 原长小于等于和长 with A B, 长度之和的对称性; trivial.
Qed.

(** If the sum of two segments is degenerate, then the segments are degenerate *)

Lemma 和长为零则原长加长两端点均重合 : forall A B C D E, 长度之和 A B C D E E -> A = B /\ C = D.
Proof.
  intros A B C D E H长度之和.
  split; apply AB小于等于CC推出A与B重合 with E; [apply 原长小于等于和长 with C D|apply (加长小于等于和长 A B)]; assumption.
Qed.
(* 无用 *)
Lemma 长度之和推出点不重合1 : forall A B C D E F, A <> B -> 长度之和 A B C D E F -> E <> F.
Proof.
  intros A B C D E F Hdiff H长度之和 Heq.
  subst F.
  apply Hdiff.
  destruct (和长为零则原长加长两端点均重合 A B C D E H长度之和); assumption.
Qed.
(* 无用 *)
Lemma 长度之和推出点不重合2 : forall A B C D E F, C <> D -> 长度之和 A B C D E F -> E <> F.
Proof.
  intros A B C D E F Hdiff H长度之和 Heq.
  subst F.
  apply Hdiff.
  destruct (和长为零则原长加长两端点均重合 A B C D E H长度之和); assumption.
Qed.

(** 长度之和 preserves Le *)

Lemma 长度之和保持小于等于性质 : forall A B C D E F A' B' C' D' E' F',
  Le A B A' B' -> Le C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Le E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 H长度之和 H长度之和'.
  destruct H长度之和 as [P [Q [R [HBet [HCong1 [HCong2 HCong3]]]]]].
  destruct H长度之和' as [P' [Q' [R' [HBet' [HCong1' [HCong2' HCong3']]]]]].
  apply (l5_6_等长保持小于等于关系 P R P' R'); trivial.
  apply bet2_le2__le1346 with Q Q'; trivial.
  apply (l5_6_等长保持小于等于关系 A B A' B'); Cong.
  apply (l5_6_等长保持小于等于关系 C D C' D'); Cong.
Qed.

(** If AB <= A'B', CD <= C'D' and AB + CD = A'B' + C'D', then AB = A'B' and CD = C'D' *)

Lemma 小于等于与和长相等推等长1 : forall A B C D E F A' B' C' D',
  Le A B A' B' -> Le C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E F ->
  Cong A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' HLe1 HLe2 HSum HSum'.
  apply 长度被加数的唯一性 with C D E F; trivial.
  destruct (长度之和的存在性 A' B' C D) as [E' [F' HSum1]].
  apply (等长保持长度之和性质 A' B' C D E' F'); Cong.
  apply 长度小于等于的反对称性.
    apply 长度之和保持小于等于性质 with A' B' C D A' B' C' D'; Le.
    apply 长度之和保持小于等于性质 with A B C D A' B' C D; Le.
Qed.
(* 无用 *)
Lemma 小于等于与和长相等推等长2 : forall A B C D E F A' B' C' D',
  Le A B A' B' -> Le C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E F ->
  Cong C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' HLe1 HLe2 HSum HSum'.
  apply 小于等于与和长相等推等长1 with A B E F A' B'; try (apply 长度之和的对称性); trivial.
Qed.

(** If AB < A'B' and CD <= C'D', then AB + CD < A'B' + C'D' *)

Lemma 长度一全序一偏序则和长保持全序 : forall A B C D E F A' B' C' D' E' F',
  Lt A B A' B' -> Le C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt HLe HSum HSum'.
  split.
    apply 长度之和保持小于等于性质 with A B C D A' B' C' D'; Le.
  intro HCong.
  destruct HLt as [HLe1 HNCong].
  apply HNCong.
  apply 小于等于与和长相等推等长1 with C D E F C' D'; trivial.
  apply (等长保持长度之和性质 A' B' C' D' E' F'); Cong.
Qed.

Lemma 长度一偏序一全序则和长保持全序 : forall A B C D E F A' B' C' D' E' F',
  Le A B A' B' -> Lt C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply 长度一全序一偏序则和长保持全序 with C D A B C' D' A' B'; try (apply 长度之和的对称性); trivial.
Qed.

Lemma 长度双全序则和长保持全序 : forall A B C D E F A' B' C' D' E' F',
  Lt A B A' B' -> Lt C D C' D' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt E F E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt1 HLt2 HSum HSum'.
  apply 长度一全序一偏序则和长保持全序 with A B C D A' B' C' D'; Le.
Qed.

(** If CD >= C'D' and AB + CD <= A'B' + C'D', then AB <= A'B' *)

Lemma 加长反偏序和长偏序则原长偏序 : forall A B C D E F A' B' C' D' E' F',
  Le C' D' C D -> Le E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Le A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply 不小于推出反向小于等于; intro HLt.
  apply 长度小于等于推出反向不小于 in HLe2; apply HLe2.
  apply 长度一全序一偏序则和长保持全序 with A' B' C' D' A B C D; trivial.
Qed.

Lemma 原长反偏序和长偏序则加长偏序 : forall A B C D E F A' B' C' D' E' F',
  Le A' B' A B -> Le E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Le C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply 加长反偏序和长偏序则原长偏序 with A B E F A' B' E' F'; try (apply 长度之和的对称性); trivial.
Qed.

(** If CD > C'D' and AB + CD <= A'B' + C'D', then AB < A'B' *)

Lemma 加长反全序和长偏序则原长全序 : forall A B C D E F A' B' C' D' E' F',
  Lt C' D' C D -> Le E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt HLe HSum HSum'.
  apply 不小于等于推出反向小于; intro HLe1.
  apply 长度小于等于推出反向不小于 in HLe; apply HLe.
  apply 长度一偏序一全序则和长保持全序 with A' B' C' D' A B C D; trivial.
Qed.
(* 无用 *)
Lemma 原长反全序和长偏序则加长全序 : forall A B C D E F A' B' C' D' E' F',
  Lt A' B' A B -> Le E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe1 HLe2 HSum HSum'.
  apply 加长反全序和长偏序则原长全序 with A B E F A' B' E' F'; try (apply 长度之和的对称性); trivial.
Qed.

(** If CD >= C'D' and AB + CD < A'B' + C'D', then AB < A'B' *)

Lemma 加长反偏序和长全序则原长全序 : forall A B C D E F A' B' C' D' E' F',
  Le C' D' C D -> Lt E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply 不小于等于推出反向小于; intro HLe1.
  apply 小于推出反向不小于等于 in HLt; apply HLt.
  apply 长度之和保持小于等于性质 with A' B' C' D' A B C D; trivial.
Qed.

Lemma 原长反偏序和长全序则加长全序 : forall A B C D E F A' B' C' D' E' F',
  Le A' B' A B -> Lt E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply 加长反偏序和长全序则原长全序 with A B E F A' B' E' F'; try (apply 长度之和的对称性); trivial.
Qed.

Lemma 加长反全序和长全序则原长全序 : forall A B C D E F A' B' C' D' E' F',
  Lt C' D' C D -> Lt E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt A B A' B'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLt1 HLt2 HSum HSum'.
  apply 加长反偏序和长全序则原长全序 with C D E F C' D' E' F'; Le.
Qed.

Lemma 原长反全序和长全序则加长全序 : forall A B C D E F A' B' C' D' E' F',
  Lt A' B' A B -> Lt E F E' F' -> 长度之和 A B C D E F -> 长度之和 A' B' C' D' E' F' ->
  Lt C D C' D'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HLe HLt HSum HSum'.
  apply 原长反偏序和长全序则加长全序 with A B E F A' B' E' F'; Le.
Qed.

End Sums.

Hint Resolve 长度之和的对称性 长度之和的左交换性 长度之和的中交换性 长度之和的右交换性
             长度之和的交换性 零长加一长仍为该长 长度加零长不变 中间性蕴含长度之和 : sums.

Ltac Sums := auto 4 with sums.