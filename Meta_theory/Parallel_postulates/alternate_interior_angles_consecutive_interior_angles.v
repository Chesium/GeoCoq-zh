Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section alternate_interior_angles_consecutive_interior_angles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma alternate_interior__consecutive_interior :
   alternate_interior_angles_postulate -> consecutive_interior_angles_postulate.
Proof.
  intros aia A B C D Hos HPar.
  split.
    assert_diffs; auto.
  destruct (由一点往一方向构造等长线段 A B B A) as [A' []].
  exists A'; split; trivial.
  apply conga_comm, conga_sym, aia; [|assert_diffs; apply par_col_par_2 with A; Col; Par].
  apply l9_2, l9_8_2 with A; trivial.
  apply one_side_not_col123 in Hos.
  repeat split.
    Col.
    intro; apply Hos; ColR.
  exists B; split; Col.
Qed.

End alternate_interior_angles_consecutive_interior_angles.
