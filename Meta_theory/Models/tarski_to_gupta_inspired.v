Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.

Section 无维度中性塔斯基公理系统_to_Gupta_inspired_variant_of_无维度中性塔斯基公理系统.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma 等长的内传递性' : forall A B C D E F, Cong A B E F -> Cong C D E F -> Cong A B C D.
Proof.
  intros A B C D E F H1 H2; apply (等长的内传递性 E F); apply 等长的对称性; assumption.
Qed.

Lemma 帕施公理' : forall A B C P Q,
  Bet A P C -> Bet B Q C -> A <> P -> P <> C -> B <> Q -> Q <> C ->
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B) ->
  exists x : Tpoint, Bet P x B /\ Bet Q x A.
Proof.
  intros A B C P Q; intros; apply 帕施公理 with C; assumption.
Qed.

Instance T_to_GI : Gupta_inspired_variant_of_无维度中性塔斯基公理系统_带两点重合决定性.
Proof.
exact (Build_Gupta_inspired_variant_of_无维度中性塔斯基公理系统_带两点重合决定性
  Tpoint Bet Cong 两点重合的决定性
  等长的伪自反性 等长的内传递性' 等长的同一性
  由一点往一方向构造等长线段 五线段公理_等价SAS 中间性的对称性 中间性的内传递性1 帕施公理'
  PA PB PC 防降维公理).
Defined.

End 无维度中性塔斯基公理系统_to_Gupta_inspired_variant_of_无维度中性塔斯基公理系统.

Section Tarski_2D_to_Gupta_inspired_variant_of_Tarski_2D.

Context `{T2D:Tarski_2D}.

Instance T2D_to_TG2D : Gupta_inspired_variant_of_Tarski_2D T_to_GI.
Proof.
  split; intros A B C P Q HPQ HAB HAC HBC; apply 防升维公理, HPQ.
Defined.

End Tarski_2D_to_Gupta_inspired_variant_of_Tarski_2D.

Section 塔斯基公理系统_欧几里得几何_to_Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何.

Context `{TE:塔斯基公理系统_欧几里得几何}.

Instance T_euclidean_to_TG_euclidean : Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何 T_to_GI.
Proof.
  split; intros A B C D T H1 H2 HBD HDC HNCol.
  assert (A <> D) by (intro; subst; apply HNCol; right; right; apply 中间性的对称性, H2).
  apply euclid with D; assumption.
Defined.

End 塔斯基公理系统_欧几里得几何_to_Gupta_inspired_variant_of_塔斯基公理系统_欧几里得几何.