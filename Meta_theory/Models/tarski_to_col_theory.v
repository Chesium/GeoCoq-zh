Require Export GeoCoq.Tarski_dev.Ch06_out_lines.
Require Import GeoCoq.Tactics.Coinc.tactics_axioms.

(** In this file we prove that Tarski neutral dimensionless is a Col_theory. *)

Section Tarski_is_a_Col_theory.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Global Instance Tarski_is_a_Col_theory : (Col_theory Tpoint Col).
Proof.
exact (Build_Col_theory Tpoint Col AAB型共线 等价共线BCA 等价共线ACB 共线的传递性4).
Defined.

End Tarski_is_a_Col_theory.
