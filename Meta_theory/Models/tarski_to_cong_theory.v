Require Export GeoCoq.Tarski_dev.Ch02_cong.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

(** In this file we prove that Tarski neutral dimensionless is a Cong_theory. *)

Section Tarski_is_a_Cong_theory.

Context `{Tn:无维度中性塔斯基公理系统}.

Global Instance Tarski_is_a_Cong_theory : (Cong_theory Tpoint Cong).
Proof.
exact (Build_Cong_theory Tpoint Cong 等长的自反性 等长的左交换性 等长的对称性 等长的传递性).
Defined.

End Tarski_is_a_Cong_theory.