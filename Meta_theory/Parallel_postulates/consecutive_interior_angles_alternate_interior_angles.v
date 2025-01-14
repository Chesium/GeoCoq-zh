Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section consecutive_interior_angles_alternate_interior_angles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma consecutive_interior__alternate_interior :
   consecutive_interior_angles_postulate -> alternate_interior_angles_postulate.
Proof.
  intros cia A B C D Hts HPar.
  destruct (由一点往一方向构造等长线段 D C C D) as [D' []].
  apply suppa2__conga123 with A C D'.
  - apply cia; [|统计不重合点; apply par_left_comm, par_col_par with D; Col].
    exists D; split; trivial.
    destruct Hts as [_ [HNCol _]].
    repeat split.
      intro; apply HNCol; ColR.
      Col.
    exists C; split; [Col|Between].
  - 统计不重合点; split; auto.
    exists D'; split; 等角.
Qed.

End consecutive_interior_angles_alternate_interior_angles.