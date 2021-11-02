Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Definitions.

Section playfair_existential_playfair.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma playfair__existential_playfair :
  playfair_s_postulate ->
  existential_playfair_s_postulate.
Proof.
intro HF.
exists PA, PB, PC.
split; [apply 防降维公理|]; intros; apply HF with PA PB PC; assumption.
Qed.

End playfair_existential_playfair.