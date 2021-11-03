Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_thales_postulate.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma rah__thales_postulate : postulate_of_right_saccheri_quadrilaterals -> thales_postulate.
Proof.
  intros rah A B C M HM HCong.
  destruct (共线的决定性 A B C).
  { destruct (两点重合的决定性 A B).
      treat_equalities; Perp.
    destruct (共线点间距相同要么重合要么中点 M A C); [ColR|Cong|..].
      subst; Perp.
    assert (B = C) by (apply 中点组的唯一性2 with M A; 中点).
    subst; Perp.
  }
  apply (t22_17__rah _ _ _ M); assumption.
Qed.

End rah_thales_postulate.