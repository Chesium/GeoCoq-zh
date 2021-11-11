Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_bis_playfair.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma playfair_bis__playfair : alternative_playfair_s_postulate -> playfair_s_postulate.
Proof.
intros playfair_bis.
intros A1 A2 B1 B2 C1 C2 P HParAB HPB HParAC HPC.
elim (共线的决定性 A1 A2 P); [intro HCol; treat_equalities|intro HNC1].

  {
  elim HParAB; [intros [_ HF]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol1 HCol2]]].
  elim HParAC; [intros [_ HF]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol3 HCol4]]].
  统计不重合点; split; ColR.
  }

  {
  destruct (垂点的存在性 P A1 A2) as [X HPerp1]; [统计不重合点; auto|].
  revert dependent A2; revert A1.
  cut (forall A1 A2, Par A1 A2 B1 B2 -> Par A1 A2 C1 C2 -> ~ Col A1 A2 P -> Perp P X A1 A2 ->
                     ~ Col P X A1 -> Col C1 B1 B2 /\ Col C2 B1 B2).
  {
  intros Haux A1 A2 HParAB HParAC HNC1 HPerp1.
  elim (垂直推出不共线 _ _ _ _ HPerp1); [apply (Haux A1 A2)|apply (Haux A2 A1)]; Par; Col; Perp.
  }

  intros A1 A2 HParAB HParAC HNC1 HPerp1 HNC2.
  assert (HCop1 : 共面 P X A1 A2) by Cop.
  assert(HD := ex_perp_cop P X P A1).
  统计不重合点.
  destruct HD as [D [HPerp2 HCop2]]; auto.
  统计不重合点.
  assert(Perp2 A1 A2 P D P).
    {
    exists X.
    exists P.
    split; Col.
    split; Perp.
    }
  assert(Col B1 P D /\ Col B2 P D)
    by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
  assert(Col C1 P D /\ Col C2 P D)
    by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
  分离合取式.
  split; apply(共线的传递性4 P D); Col.
  }
Qed.

End playfair_bis_playfair.