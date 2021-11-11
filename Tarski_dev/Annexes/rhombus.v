(* Roland Coghetto, 29 March 2018, 
                    04 April 2018.
   GNU Lesser General Public License v3.0 
   See LICENSE GeoCoq 2.3.0
     
     MOTIVATION: 
     
      - Existence of a rhombus (absolute geometry).
      - Unicity of rhomus with 3 points determinated (absolute geometry).
      
     TODO:
     
      29 march 2018 - In Euclidean geometry, construction of a rhombus from 3 determined points. DONE
                    - What about rhombus in non-euclidean geometry case ?
      04 april 2018 - MOVE all "平四"'s lemma in quadrialterals.v 
                       (after modify context Tarski_2D by 
                          无维度中性塔斯基公理系统_带两点重合决定性 
                          in quadrilaterals.v) ?
                    - MOVE all "rhombus"'s lemma in quadrilaterals.v
                       (after modify context Tarski_2D by 
                          无维度中性塔斯基公理系统_带两点重合决定性 
                          in quadrilaterals.v) ?
                    - DELETE rhombus.v
                    - EXPERIMENTAL: (in quadrilaterals_inter_dec.v)
                        Lemma rmb_cong :
                          forall A B C D,
                          菱形 A B C D ->
                          Cong A B B C /\ Cong A B C D /\ Cong A B D A.
                        TRY MODIFY CONTEXT ? Tarski_2D_euclidean -> Tarski_2D or 无维度中性塔斯基公理系统_带两点重合决定性

   CHANGES: 04 april 2018, RC
   1) See JNarboux, comments about pull requests 菱形.
   2) ADD End 菱形_Existence_Unicity.
   2) MODIFY CONTEXT: Tarski_2D by 无维度中性塔斯基公理系统_带两点重合决定性.
   3) ADD Existence 平四, 菱形.

*)

Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section 菱形_Existence_Unicity.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.
(* 无用 *)
Lemma 平四推点不重合: forall A B C D, 平四 A B C D -> (A <> C \/ B <> D).
Proof.
  intros.
  unfold 平四 in H. 分离合取式.
assumption.
Qed.
(* 无用 *)
Lemma 平四_等价定义: forall A B C D, (A <> C \/ B <> D) -> ((exists M,
在圆上 C M A /\ 在圆上 D M B /\ Bet C M A /\ Bet D M B) <-> 平四 A B C D).
Proof.
  intros.
  split.
  - intros.
    unfold 在圆上 in *.
    split. 
    assumption.
    ex_and H0 M.
    exists M.
    split.
    { unfold 中点.
      split;Between. 
      Cong. 
    }
    { unfold 中点 in *.
      split;Between. 
      Cong.
    }
  - intros.
    unfold 在圆上 in *.
    ex_and H0 M.
    ex_and H1 M1.
    unfold 中点 in *.
    exists M1.
    split;Cong.
    split;[Cong|Between].
Qed.

Lemma AABB平四: forall A B, A <> B -> 平四 A A B B.
Proof.
  intros.
  unfold 平四.
  split;auto.
  midpoint M A B.
  exists M.
  split;auto.
Qed.

Lemma 平四的存在性: exists A B C D, 平四 A B C D.
Proof.
  destruct 存在不重合的点 as [A [B H]].
  exists A, A, B, B.
  apply AABB平四.
  assumption.
Qed.

Lemma 菱形的存在性: exists A B C D, 菱形 A B C D.
Proof.
  destruct 防降维公理_老版本 as [A [B [C HNC]]].
  assert (H1 : ~ Col A B C) by auto.
  clear HNC.
  统计不重合点.
  assert (HAB := 中垂线的存在性 A B);
  destruct HAB as [C1 [C2 HAB]]; try (统计不重合点; assumption).
  assert(Cong A C1 B C1).
  apply 中垂线顶点距线两端等长2 with C2.
  apply 中垂线左对称性.
  assumption.
  unfold 中垂线 in HAB.
  分离合取式.
  unfold 严格对称 in *.
  分离合取式.
  destruct H0 as [M H0];
  分离合取式.
  assert(H10 := H).
  unfold 中点 in H10.
  分离合取式.
  assert (exists x, Bet C1 M x /\ Cong M x C1 M) by (apply 由一点往一方向构造等长线段).
  ex_and H8 x.
  exists A.
  exists C1.
  exists B.
  exists x.
  assert(平四 A C1 B x).
  unfold 平四.
  split.
  tauto.
  exists M.
  split.
  apply M是AB中点则M是BA中点;assumption.
  unfold 中点.
  split.
  assumption.
  Cong.
  unfold 菱形.
  split.
  assumption.
  Cong.
Qed.
(* 无用 *)
Lemma 确定三点后菱形的唯一性: forall A B C D E, 菱形 A B C D -> 菱形 A B C E -> D = E.
Proof.
  intros.
  unfold 菱形 in *.
  分离合取式.
  unfold 平四 in *.
  分离合取式.
  ex_and H4 M.
  ex_and H3 N.
  assert (M = N). 
  apply 中点的唯一性1 with A C;assumption.
  subst.
  apply 中点组的唯一性1 with B N;assumption.
Qed.

Lemma 不重合共线点间距相同则为中点: forall A B C, A <> C -> Col A B C -> Cong A B B C -> 中点 B A C.
Proof.
  intros.
  assert(Col A B C). Col.
  assert(Cong B A B C). Cong.
  assert(A = C \/ 中点 B A C).
  apply 共线点间距相同要么重合要么中点; tauto. 
  tauto.
Qed.
(* 无用 *)
Lemma 共线等距三点可构造平四: forall A B C, A <> C -> Col A B C -> Cong A B B C -> exists D, 平四 A B C D.
Proof.
  intros.
  unfold Col in H0.
  assert(中点 B A C).
  apply 不重合共线点间距相同则为中点;
  trivial.
  exists B.
  unfold 平四 in *.
  split.
  tauto.
  exists B.
  split.
  trivial.
  中点.
Qed.

Lemma 不共线等距三点可构造平四: forall A B C, ~Col A B C -> Cong A B B C -> exists D, 平四 A B C D.
Proof.
  intros A B C HC H.
  unfold 平四 in *.
  assert(在中垂线上 B A C). exact H.
  destruct (中点的存在性 A B) as [X H1].
  destruct (l10_2_existence A C B) as [D H3].
  unfold 对称 in H3.
  unfold 严格对称 in H3.
  induction (两点重合的决定性 A C).
  case H3.
    - intros. tauto.
    - intros.
      unfold 中点 in H4.
      destruct (中点的存在性 A C) as [Y H5].
      destruct (构造对称点 B Y) as [E H6].
      exists E.
      assert(B <> E).
      induction (两点重合的决定性 B E).
      subst E.
      assert(Y = B).
      apply M是AA中点则M与A重合. exact H6.
      subst Y.
      assert(Col A B C). Col. tauto. tauto. 
      split. tauto.
      exists Y.
      tauto.
    - intros.
      destruct H3.
      destruct H3;destruct H4;destruct H4.
      destruct H4.
      unfold 中点 in H4.
      destruct (中点的存在性 A C) as [Y H7].
      destruct (构造对称点 B Y) as [E H8].
      exists E.
      assert(B <> E).
      induction (两点重合的决定性 B E).
      subst E.
      assert(Y = B).
      apply M是AA中点则M与A重合. exact H8.
      subst Y.
      assert(Col A B C). Col. tauto. tauto. 
      split. tauto.
      exists Y.
      tauto.
      exists D.
      split.
      tauto.
      exists A.
      tauto.
Qed.
(* 无用 *)
Lemma 共线等距三点可构造菱形: forall A B C, A <> C -> Col A B C -> Cong A B B C -> exists D, 菱形 A B C D.
Proof.
  intros.
  assert(中点 B A C).
  apply 不重合共线点间距相同则为中点; tauto.
  exists B.
  unfold 菱形 in *.
  split.
  unfold 平四 in *.
  split.
  tauto.
  exists B.
  split. 
  assumption. 
  中点. 
  assumption.
Qed.
(* 无用 *)
Lemma 不共线等距三点可构造菱形: forall A B C, ~Col A B C -> Cong A B B C -> exists D, 菱形 A B C D.
Proof.
  intros.
  assert(exists D, 平四 A B C D).
  apply 不共线等距三点可构造平四;trivial.
  destruct H1 as [D H2].
  exists D.
  unfold 菱形 in *.
  tauto.
Qed.

End 菱形_Existence_Unicity.
