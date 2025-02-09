Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.bachmann_s_lotschnittaxiom_variant.
Require Import GeoCoq.Tarski_dev.Ch11_angles.

Section weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom :
  weak_triangle_circumscription_principle -> bachmann_s_lotschnittaxiom.
Proof.
intro HP.
apply bachmann_s_lotschnittaxiom_aux.
intros A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD Hd1 Hd2 HPerp1 HPerp2 HPerp3.
intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4.
destruct (构造对称点 IAB IAC) as [E HE].
destruct (构造对称点 IAB IBD) as [F HF].
统计不重合点.
assert (HPerp4 : Perp E IAB IAB F).
  {
  apply 与垂线共线之线也为垂线1 with B1 B2; [apply 与垂线共线之线也为垂线1 with A1 A2|..]; ColR.
  }
assert (~ Col IAC IAB IBD).
  apply 成直角三点不共线; auto; apply 直角边共线点也构成直角2 with F; Col; apply 直角的对称性, 直角边共线点也构成直角2 with E; Perp; Col.
assert (共面 E F IAB D1) by CopR.
assert (共面 E F IAB D2) by CopR.
assert (共面 E F IAB C1) by CopR.
assert (共面 E F IAB C2) by CopR.
destruct (HP E F IAB D1 D2 C1 C2) as [I [HC7 HC8]]; auto;
[apply 共线否定排列BCA, L形垂直推出不共线| |split..|exists I; split; Col]; Perp; split.
  exists IBD; split; auto.
  left; apply 与垂线共线之线也为垂线1 with B1 B2; ColR.
  exists IAC; split; auto.
  left; apply 与垂线共线之线也为垂线1 with A1 A2; ColR.
Qed.

End weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.