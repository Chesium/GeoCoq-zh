Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_thales_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__thales_postulate : postulate_of_right_saccheri_quadrilaterals -> thales_postulate.
Proof.
  intros rah A B C M HM HCong.
  destruct (col_dec A B C).
  { destruct (两点重合的决定性 A B).
      treat_equalities; Perp.
    destruct (l7_20 M A C); [ColR|Cong|..].
      subst; Perp.
    assert (B = C) by (apply l7_9 with M A; Midpoint).
    subst; Perp.
  }
  apply (t22_17__rah _ _ _ M); assumption.
Qed.

End rah_thales_postulate.