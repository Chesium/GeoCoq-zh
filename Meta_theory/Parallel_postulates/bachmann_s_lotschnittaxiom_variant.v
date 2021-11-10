Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_variant.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma bachmann_s_lotschnittaxiom_aux : bachmann_s_lotschnittaxiom <->
  forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD, IAB <> IAC -> IAB <> IBD ->
  Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
  Col A1 A2 IAB -> Col B1 B2 IAB -> Col A1 A2 IAC ->
  Col C1 C2 IAC -> Col B1 B2 IBD -> Col D1 D2 IBD ->
  共面 IAB IAC IBD C1 -> 共面 IAB IAC IBD C2 ->
  共面 IAB IAC IBD D1 -> 共面 IAB IAC IBD D2 ->
  exists I, Col C1 C2 I /\ Col D1 D2 I.
Proof.
  split.
  - intros bla A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD Hd Hd' HPerpAB HPerpAC HPerpBD.
    intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
    assert (Col IAB IAC A1) by ColR.
    assert (Col IAB IAC A2) by ColR.
    assert (Col IAB IBD B1) by ColR.
    assert (Col IAB IBD B2) by ColR.
    assert (共面 IAB IAC IBD A1) by Cop.
    assert (共面 IAB IAC IBD A2) by Cop.
    assert (共面 IAB IAC IBD B1) by Cop.
    assert (共面 IAB IAC IBD B2) by Cop.
    assert (Per IAC IAB IBD) by (apply L形垂直转直角1, (与垂直两线分别共线的两线垂直 A1 A2 B1 B2); auto).
    assert (HNC1 : ~ Col IAC IAB IBD) by (apply 成直角三点不共线; auto).
    assert (HParA : 严格平行 A1 A2 D1 D2).
      {
      clear dependent C1; clear dependent C2;
      apply par_not_col_strict with IBD; Col.
        apply l12_9 with B1 B2; Perp; CopR.
      intro; apply HNC1; ColR.
      }
    assert (HParB : 严格平行 B1 B2 C1 C2).
      {
      clear dependent D1; clear dependent D2;
      apply par_not_col_strict with IAC; Col.
        apply l12_9 with A1 A2; Perp; CopR.
      intro; apply HNC1; ColR.
      }
    assert (HPQ : IAC <> IAB) by (统计不重合点; auto).
    assert (HQR : IAB <> IBD) by (统计不重合点; auto).
    destruct (每组共线三点都有另一共线点 C1 C2 IAC) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
    destruct (每组共线三点都有另一共线点 D1 D2 IBD) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
    统计不重合点.
    destruct (bla IAC IAB IBD P1 R1) as [I [HI1 HI2]]; auto.
      apply L形垂直转直角1, (与垂直两线分别共线的两线垂直 A1 A2 C1 C2); Col.
      apply L形垂直转直角1, (与垂直两线分别共线的两线垂直 B1 B2 D1 D2); Col.
      apply col_cop2__cop with C1 C2; Cop.
      apply col_cop2__cop with D1 D2; Cop.
    exists I.
    split; ColR.

  - intros lotschnitt P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR HCop1 HCop2.
    destruct (两点重合的决定性 P P1).
      subst; exists R; Col.
    destruct (两点重合的决定性 R R1).
      subst; exists P; Col.
    destruct (lotschnitt P Q Q R P P1 R R1 Q P R) as [S [HS1 HS2]]; Col; Perp; Cop.
    exists S; split; assumption.
Qed.

End bachmann_s_lotschnittaxiom_variant.