Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_SPP.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma proclus_s_postulate_implies_strong_parallel_postulate :
  proclus_postulate -> strong_parallel_postulate.
Proof.
intros HP P Q R S T U HPTQ HRTS HNC1 HCop HCong1 Hcong2.
unfold BetS in *; 分离合取式.
elim (共线的决定性 P Q R); [exists P; split; ColR|intro HNC2].
destruct (HP P R Q S P U) as [I [HCol1 HCol2]]; [..|exists I; split]; Col.
apply l12_17 with T; [统计不重合点|split..]; Cong.
assert (共面 P Q R S) by (exists T; left; split; Col).
CopR.
Qed.

End proclus_SPP.