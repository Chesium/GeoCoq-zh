Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_alternate_interior_angles.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma playfair__alternate_interior :  playfair_s_postulate -> alternate_interior_angles_postulate.
Proof.
intros playfair A B C D Hts HPar.
assert(~ Col B A C) by (destruct Hts; auto).
assert(HD' := 给定角一边可作出与给定点异侧一点构成等角_非平角 B A C A C B).
destruct HD' as [D' []]; Col.
apply (角等的传递性 _ _ _ D' C A).
等角.
统计不重合点.
apply out2__conga; [|apply out_trivial; auto].
apply (col_one_side_out _ A).
assert (HP := playfair A B C D C D' C).
destruct HP; Col.
apply l12_21_b; 等角; Side.
apply invert_one_side; exists B; split; Side.
Qed.

End playfair_alternate_interior_angles.