Require Export GeoCoq.Tarski_dev.Annexes.saccheri.

Section 三角形内角和与平角之差.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 三角形内角和与平角之差推点不重合 : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F ->
  A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  suma.统计不重合点.
  repeat split; auto.
Qed.

Lemma 三角形内角和与平角之差的存在性 : forall A B C,
  A <> B -> B <> C -> A <> C -> exists D E F, 三角形内角和与平角之差 A B C D E F.
Proof.
  intros A B C HAB HBC HAC.
  destruct (三角形内角和的存在性 A B C) as [G [H [I HTri]]]; auto.
  suma.统计不重合点.
  destruct (ex_suppa G H I) as [D [E [F HSuppa]]]; auto.
  exists D, E, F, G, H, I.
  split; assumption.
Qed.

Lemma 等角保持三角形内角和与平角之差性质 : forall A B C D E F D' E' F',
  三角形内角和与平角之差 A B C D E F -> 等角 D E F D' E' F' ->
  三角形内角和与平角之差 A B C D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HConga.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  统计不重合点.
  apply (conga2_suppa__suppa G H I D E F); 等角.
Qed.

Lemma 同三角形内角和与平角之差唯一 : forall A B C D E F D' E' F',
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 A B C D' E' F' ->
  等角 D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HDef'.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  destruct HDef' as [G' [H' [I' [HTri' HSuppa']]]].
  apply (suppa2__conga456 G H I); trivial.
  suma.统计不重合点.
  apply (conga2_suppa__suppa G' H' I' D' E' F'); try apply 同角相等; auto.
  apply (三角形内角和的唯一性 A B C); assumption.
Qed.

Lemma 等价三角形内角和与平角之差排列BCA : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 B C A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply 等价三角形内角和BCA, HTri.
Qed.

Lemma 等价三角形内角和与平角之差排列CAB : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 C A B D E F.
Proof.
  intros.
  do 2 apply 等价三角形内角和与平角之差排列BCA; trivial.
Qed.

Lemma 等价三角形内角和与平角之差排列CBA : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 C B A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply 等价三角形内角和CBA, HTri.
Qed.

Lemma 等价三角形内角和与平角之差排列BAC : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 B A C D E F.
Proof.
  intros.
  apply 等价三角形内角和与平角之差排列CBA, 等价三角形内角和与平角之差排列CAB; trivial.
Qed.

Lemma 等价三角形内角和与平角之差排列ACB : forall A B C D E F,
  三角形内角和与平角之差 A B C D E F -> 三角形内角和与平角之差 A C B D E F.
Proof.
  intros.
  apply 等价三角形内角和与平角之差排列CBA, 等价三角形内角和与平角之差排列BCA; trivial.
Qed.

Lemma 等内角三角形内角和与平角之差相等 : forall A B C D E F A' B' C',
  三角形内角和与平角之差 A B C D E F ->
  等角 A B C A' B' C' -> 等角 B C A B' C' A' -> 等角 C A B C' A' B' ->
  三角形内角和与平角之差 A' B' C' D E F.
Proof.
  intros A B C D E F A' B' C' HDef HCongaB HCongaC HCongaA.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply (两三角形内角对应相等则内角和相等 A B C); trivial.
Qed.

Lemma 退化三角形内角和与平角之差为零角 : forall A B C D E F,
  Col A B C -> 三角形内角和与平角之差 A B C D E F -> Out E D F.
Proof.
  intros A B C D E F HCol HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (bet_suppa__out G H I); trivial.
  apply (退化三角形的内角和为平角 A B C); Col.
Qed.
(* 无用 *)
Lemma 直角萨凯里四边形假设蕴含三角形内角和与平角之差为零角 :
  直角萨凯里四边形假设 ->
  forall A B C D E F, 三角形内角和与平角之差 A B C D E F -> Out E D F.
Proof.
  intros rah A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (bet_suppa__out G H I); trivial.
  apply (t22_14__bet rah A B C), HTri.
Qed.

Lemma 非退化三角形内角和与平角之差为零角蕴含直角萨凯里四边形假设 : forall A B C D E F,
  ~ Col A B C -> 三角形内角和与平角之差 A B C D E F -> Out E D F ->
  直角萨凯里四边形假设.
Proof.
  intros A B C D E F HNCol HDef HOut.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (t22_14__rah A B C G H I); trivial.
  apply (out_suppa__bet D E F); [|apply suppa_sym]; assumption.
Qed.

(** The following development is inspired by The Foundations of Geometry and the Non-Euclidean Plane, by George E Martin, chapter 22 *)

(** Additivity of the defect : if C1 is between A and C, the defect of ABC is
    the sum of the defects of ABC1 and BC1C.
    In this proof, we have to exclude the semi-elliptical case so that the sums of angles behave. *)
(* 
         B
        / \_
       /   |\_
      /     \ \_
     /      |   \_
    /  DEFECT\    \_
   /  =defect+defect\_
  /          \        \
 A------------C1-------C
*)
    Lemma t22_16_1_三角形内角和与平角之差的可加性1 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C C1 D E F G H I K L M,
    Bet A C1 C -> 三角形内角和与平角之差 A B C1 D E F -> 三角形内角和与平角之差 B C1 C G H I ->
    和角 D E F G H I K L M ->
    和角不大于平角 D E F G H I /\ 三角形内角和与平角之差 A B C K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefC HSuma.
  assert (HDA := 三角形内角和与平角之差推点不重合 A B C1 D E F HDefA).
  assert (HDC := 三角形内角和与平角之差推点不重合 B C1 C G H I HDefC).
  分离合取式; clean.
  apply 等价三角形内角和与平角之差排列CBA in HDefA.
  destruct HDefA as [P [Q [R [HTri HSuppa]]]].
  assert (HSuma1 : 和角 P Q R D E F A C1 C) by 和角.
  destruct HTri as [S [T [U [HSuma2 HSuma3]]]].
  assert (HInter : 和角 S T U D E F B C1 C /\ 和角不大于平角 S T U D E F).
  { suma.统计不重合点.
    assert (HSuma4 : 和角 B C1 C A C1 B A C1 C) by 和角.
    destruct (和角的存在性 A C1 B D E F) as [V [W [X HSuma5]]]; auto.
    assert (HIsi : 和角不大于平角 P Q R D E F) by (apply 补角之和不大于平角; trivial).
    assert (HIsi1 : 和角不大于平角 S T U A C1 B) by (apply (t22_20 noah), HSuma2).
    assert (HIsi2 : 和角不大于平角 A C1 B D E F).
    { apply 角度小于等于保持和角不大于平角性质 with P Q R D E F; Lea.
      apply (加角小于等于和角 S T U); trivial.
    }
    assert (HSuma6 : 和角 S T U V W X A C1 C) by (apply 和角结合律1 with A C1 B D E F P Q R; trivial).
    assert (HIsi3 : 和角不大于平角 S T U D E F).
      apply 角度小于等于保持和角不大于平角性质 with P Q R D E F; Lea; apply 原角小于等于和角 with A C1 B; 和角.
    split; trivial.
    destruct (和角的存在性 S T U D E F) as [B' [C1' [C' HSuma']]]; auto.
    assert (HSuma7 : 和角 B' C1' C' A C1 B A C1 C) by (apply 和角结合律2 with S T U D E F V W X; 和角).
    apply (等角保持和角性质 S T U D E F B' C1' C'); try (apply 同角相等); auto.
    apply (suppa2__conga456 A C1 B).
      apply suppa_sym, 和角为平角则为补角 with A C1 C; assumption.
      apply bet__suppa; auto.
  }
  clear dependent P; clear Q R.

  destruct HInter as [HSuma3 HIsi3].
  apply 等价三角形内角和与平角之差排列BCA in HDefC.
  destruct HDefC as [P [Q [R [HTri HSuppa]]]].
  assert (HSuma1 : 和角 P Q R G H I A C1 C) by 和角.
  destruct HTri as [V [W [X [HSuma4 HSuma5]]]].
  assert (HIsi1 : 和角不大于平角 P Q R G H I) by (apply 和角为平角推和角不大于平角 with A C1 C; trivial).
  assert (HIsi5 : 和角不大于平角 V W X B C1 C) by (apply (t22_20 noah), HSuma4).
  assert (HIsi : 和角不大于平角 D E F G H I).
  { apply 角度小于等于保持和角不大于平角性质 with P Q R G H I; Lea.
    apply lea_trans with B C1 C.
      apply (加角小于等于和角 S T U); trivial.
    apply (加角小于等于和角 V W X); trivial.
  }
  split; trivial.

  suma.统计不重合点.
  destruct (和角的存在性 V W X S T U) as [A' [B' [C' HSuma6]]]; auto.
  assert (HIsi6 : 和角不大于平角 V W X S T U).
  { apply 角度小于等于保持和角不大于平角性质 with V W X B C1 C; Lea.
    apply 原角小于等于和角 with D E F; trivial.
  }
  assert (HSuma7 : 和角 A' B' C' D E F P Q R) by (apply 和角结合律2 with V W X S T U B C1 C; trivial).
  assert (HSuma8 : 和角 A' B' C' K L M A C1 C).
  { apply 和角结合律1 with D E F G H I P Q R; trivial.
    apply 和角不大于平角结合律2 with V W X S T U B C1 C; trivial.
  }
  exists A', B', C'.
  split; [|apply 和角为平角则为补角 with A C1 C; assumption].
  clear dependent D; clear dependent E; clear dependent G; clear dependent H;
  clear dependent K; clear dependent L; clear dependent P; clear dependent Q; clear F I M R.

  destruct (和角的存在性 V W X C1 B A) as [D [E [F HSuma]]]; auto.
  assert (HIsi : 和角不大于平角 V W X C1 B A).
  { apply 角度小于等于保持和角不大于平角性质 with V W X S T U; Lea.
    apply 原角小于等于和角 with B A C1; 和角.
  }
  suma.统计不重合点.
  apply 等价三角形内角和ACB.
  exists D, E, F.
  split.
  - assert (HConga : 等角 C1 C B A C B).
      apply out2__conga; [apply l6_6, bet_out|apply out_trivial]; Between.
    apply (等角保持和角性质 C1 C B C B A D E F); 等角.
    assert (H在角内 : 在角内 C1 C B A).
      repeat split; auto; exists C1; split; Between; right; apply out_trivial; auto.
    apply 和角结合律1 with C B C1 C1 B A V W X; 和角.
  - assert (HConga : 等角 B A C B A C1).
      apply out2__conga; [apply out_trivial|apply bet_out]; auto.
    apply (等角保持和角性质 D E F B A C1 A' B' C'); 等角.
    apply 和角结合律2 with V W X C1 B A S T U; 和角.
Qed.

Lemma t22_16_1_三角形内角和与平角之差的可加性2 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C C1 D E F G H I K L M,
    Bet A C1 C ->
    三角形内角和与平角之差 A B C1 D E F -> 三角形内角和与平角之差 B C1 C G H I -> 三角形内角和与平角之差 A B C K L M ->
    和角不大于平角 D E F G H I /\ 和角 D E F G H I K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefB HDef.
  assert (Hd := 三角形内角和与平角之差推点不重合 A B C1 D E F HDefA).
  assert (Hd' := 三角形内角和与平角之差推点不重合 B C1 C G H I HDefB).
  分离合取式.
  destruct (和角的存在性 D E F G H I) as [K' [L' [M' HSuma]]]; auto.
  destruct (t22_16_1_三角形内角和与平角之差的可加性1 noah A B C C1 D E F G H I K' L' M') as [HIsi HDef']; trivial.
  split; trivial.
  apply (等角保持和角性质 D E F G H I K' L' M'); try (apply 同角相等); auto.
  apply (同三角形内角和与平角之差唯一 A B C); trivial.
Qed.


Lemma t22_16_2_证明辅助定理1 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    三角形内角和与平角之差 A B C D1 D2 D3 -> 三角形内角和与平角之差 A B D C1 C2 C3 ->
    三角形内角和与平角之差 A D C B1 B2 B3 -> 三角形内角和与平角之差 C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D -> Col A B C -> 和角 D1 D2 D3 B1 B2 B3 P Q R ->
    和角不大于平角 C1 C2 C3 A1 A2 A3 /\ 和角 C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := 三角形内角和与平角之差推点不重合 A B D C1 C2 C3 HDefC).
  assert (Hd' := 三角形内角和与平角之差推点不重合 C B D A1 A2 A3 HDefA).
  assert (Hd'' := 三角形内角和与平角之差推点不重合 A B C D1 D2 D3 HDefD).
  分离合取式; suma.统计不重合点.
  apply 退化三角形内角和与平角之差为零角 in HDefD; trivial.
  destruct (共线的决定性 A D C) as [HCol1|HNCol].
  { assert (Col C B D) by ColR.
    assert (Col A B D) by ColR.
    apply 退化三角形内角和与平角之差为零角 in HDefA; trivial.
    apply 退化三角形内角和与平角之差为零角 in HDefB; trivial.
    apply 退化三角形内角和与平角之差为零角 in HDefC; trivial.
    split; [和角|].
    apply (等角保持和角性质 D1 D2 D3 B1 B2 B3 P Q R); try (apply 同角相等); auto;
    apply l11_21_b; trivial.
  }
  assert (B = O) by (apply (l6_21_两线交点的唯一性 A C D B); Col).
  subst O.
  apply 零角加上任何角后者大小不变 in HSuma; trivial.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah A D C B C1 C2 C3 A1 A2 A3 B1 B2 B3) as [HIsi HSuma1]; trivial.
    apply 等价三角形内角和与平角之差排列ACB, HDefC.
    apply 等价三角形内角和与平角之差排列CBA, HDefA.
  split; trivial.
  apply (等角保持和角性质 C1 C2 C3 A1 A2 A3 B1 B2 B3); 等角.
Qed.

Lemma t22_16_2_证明辅助定理2 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    三角形内角和与平角之差 A B C D1 D2 D3 -> 三角形内角和与平角之差 A B D C1 C2 C3 ->
    三角形内角和与平角之差 A D C B1 B2 B3 -> 三角形内角和与平角之差 C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D -> Col A B D -> 和角 D1 D2 D3 B1 B2 B3 P Q R ->
    和角不大于平角 C1 C2 C3 A1 A2 A3 /\ 和角 C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := 三角形内角和与平角之差推点不重合 A B D C1 C2 C3 HDefC).
  assert (Hd' := 三角形内角和与平角之差推点不重合 C B D A1 A2 A3 HDefA).
  分离合取式; suma.统计不重合点.
  assert (HOut : Out C2 C1 C3) by (apply (退化三角形内角和与平角之差为零角 A B D); trivial).
  split; [和角|].
  assert (HSuma1 : 和角 C1 C2 C3 A1 A2 A3 A1 A2 A3) by (apply 零角加上任何角即为该角; auto).
  apply (等角保持和角性质 C1 C2 C3 A1 A2 A3 A1 A2 A3); try (apply 同角相等); auto.
  apply (和角的唯一性 D1 D2 D3 B1 B2 B3); trivial.
  destruct (t22_16_2_证明辅助定理1 noah B A D C B1 B2 B3 A1 A2 A3 D1 D2 D3 C1 C2 C3 O A1 A2 A3); Col;
  apply 等价三角形内角和与平角之差排列BAC; trivial.
Qed.

(** In a convex quadrilateral ABCD, the sum of the defects of ABC and ADC is equal to
    the sum of the defects of ABD and CBD. We add some hypotheses to make the proof easier *)
(* 
 A---------B
 |\       /|
 | \     / |
 |  \   /  |
 |   \ /   |
 |    O    |
 |   / \   |
 |  /   \  |
 | /     \ |
 |/       \|
 D---------C
*)
Lemma t22_16_2_四边形内三角形内角和与平角之差的可加性 :
  ~ 钝角萨凯里四边形假设 ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    三角形内角和与平角之差 A B C D1 D2 D3 -> 三角形内角和与平角之差 A B D C1 C2 C3 ->
    三角形内角和与平角之差 A D C B1 B2 B3 -> 三角形内角和与平角之差 C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D ->
    和角不大于平角 D1 D2 D3 B1 B2 B3 -> 和角 D1 D2 D3 B1 B2 B3 P Q R ->
    和角不大于平角 C1 C2 C3 A1 A2 A3 /\ 和角 C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HIsi HSuma.
  assert (Hd := 三角形内角和与平角之差推点不重合 A B D C1 C2 C3 HDefC).
  assert (Hd' := 三角形内角和与平角之差推点不重合 C B D A1 A2 A3 HDefA).
  分离合取式; suma.统计不重合点.

  destruct (共线的决定性 A B C) as [HCol|HNCol].
    apply (t22_16_2_证明辅助定理1 noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (共线的决定性 A D C) as [HCol1|HNCol1].
    apply (t22_16_2_证明辅助定理1 noah A D C B A1 A2 A3 D1 D2 D3 C1 C2 C3 B1 B2 B3 O); Between; 和角;
    apply 等价三角形内角和与平角之差排列ACB; trivial.
  destruct (共线的决定性 A B D) as [HCol2|HNCol2].
    apply (t22_16_2_证明辅助定理2 noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (共线的决定性 C B D) as [HCol3|HNCol3].
    destruct (t22_16_2_证明辅助定理2 noah C B A D C1 C2 C3 B1 B2 B3 A1 A2 A3 D1 D2 D3 O P Q R); Between; 和角;
    apply 等价三角形内角和与平角之差排列CBA; trivial.
  assert (Hdiff : O <> A /\ O <> B /\ O <> C /\ O <> D).
    assert_cols; repeat split; intro; subst O; Col.
  分离合取式.

  destruct (三角形内角和与平角之差的存在性 A B O) as [S1 [T1 [U1 HDef1]]]; auto.
  destruct (三角形内角和与平角之差的存在性 B C O) as [S2 [T2 [U2 HDef2]]]; auto.
  destruct (三角形内角和与平角之差的存在性 C D O) as [S3 [T3 [U3 HDef3]]]; auto.
  destruct (三角形内角和与平角之差的存在性 A D O) as [S4 [T4 [U4 HDef4]]]; auto.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah A B C O S1 T1 U1 S2 T2 U2 D1 D2 D3) as [HIsi12 HSuma12]; trivial.
    apply 等价三角形内角和与平角之差排列ACB, HDef2.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah A D C O S4 T4 U4 S3 T3 U3 B1 B2 B3) as [HIsi34 HSuma34]; trivial.
    apply 等价三角形内角和与平角之差排列BCA, HDef3.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah B A D O S1 T1 U1 S4 T4 U4 C1 C2 C3) as [HIsi14 HSuma14]; trivial.
    apply 等价三角形内角和与平角之差排列BAC, HDef1.
    apply 等价三角形内角和与平角之差排列ACB, HDef4.
    apply 等价三角形内角和与平角之差排列BAC, HDefC.
  destruct (t22_16_1_三角形内角和与平角之差的可加性2 noah B C D O S2 T2 U2 S3 T3 U3 A1 A2 A3) as [HIsi23 HSuma23]; trivial.
    apply 等价三角形内角和与平角之差排列ACB, HDef3.
    apply 等价三角形内角和与平角之差排列BAC, HDefA.
  suma.统计不重合点.

  destruct (和角的存在性 D1 D2 D3 S3 T3 U3) as [V [W [X HSuma1]]]; auto.
  assert (HIsi1 : 和角不大于平角 D1 D2 D3 S3 T3 U3).
    apply 角度小于等于保持和角不大于平角性质 with D1 D2 D3 B1 B2 B3; Lea; apply (加角小于等于和角 S4 T4 U4); trivial.
  assert (HSuma2 : 和角 V W X S4 T4 U4 P Q R).
    apply 和角结合律2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; 和角.
  assert (HIsi2 : 和角不大于平角 V W X S4 T4 U4).
    apply 和角不大于平角结合律2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; 和角.
  assert (HSuma3 : 和角 A1 A2 A3 S1 T1 U1 V W X).
    apply 和角结合律2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; 和角.
  assert (HIsi3 : 和角不大于平角 A1 A2 A3 S1 T1 U1).
    apply 和角不大于平角结合律2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; 和角.
  split.
    apply 和角不大于平角结合律2 with S4 T4 U4 S1 T1 U1 V W X; 和角.
  apply 和角结合律2 with S4 T4 U4 S1 T1 U1 V W X; 和角.
Qed.

End 三角形内角和与平角之差.