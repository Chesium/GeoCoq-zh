Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_par_trans.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** This is Legendre theorem XXV http://gallica.bnf.fr/ark:/12148/bpt6k202689z/f29.image *)

Lemma playfair_implies_par_trans :
  playfair_s_postulate -> postulate_of_transitivity_of_parallelism.
Proof.
  intros HP A1 A2 B1 B2 C1 C2 HAB HBC.
  统计不重合点.
  destruct (cop_dec A1 A2 C1 B1) as [|HNCop]; [induction (共线的决定性 A1 A2 C1)|].

  - right.
    destruct (HP B1 B2 C1 C2 A1 A2 C1); repeat split; Par; Col.

  - left.
    split.
    { apply par_symmetry in HBC.
      destruct HBC; [destruct HAB|]; [|分离合取式..].
      - CopR.
      - apply 等价共面CDAB, col2_cop__cop with B1 B2; Col; Cop.
      - apply col2_cop__cop with B1 B2; Col; Cop.
    }
    intros [X []].
    destruct (HP B1 B2 A1 A2 C1 C2 X); Par; Col.

  - apply (par_not_col_strict A1 A2 B1 B2 B1) in HAB; [|Col|intro; apply HNCop; Cop].
    apply (par_not_col_strict B1 B2 C1 C2 C1) in HBC;
      [|Col|intro; apply HNCop, 等价共面ABDC, col_cop__cop with B2; Cop].
    destruct (cop_osp__ex_cop2 A1 A2 C1 B1 B2 C1) as [C' [HCop1 [HCop2 HC1C']]]; Cop.
      apply cop2_os__osp with A1 A2; Side; Cop.
    assert (HC' : forall X, 共面 A1 A2 B1 X -> ~ Col X C1 C').
    { intros X HX1 HX2.
      apply (par_not_col A1 A2 B1 B2 X HAB).
      - apply (l9_30 A1 A2 C1 A1 A2 B1 B1); Cop.
          apply par_strict_not_col_1 with B2, HAB.
        apply col_cop__cop with C'; Col.
      - apply (l9_30 A1 A2 B1 B1 B2 C1 C1); Cop.
          apply par_strict_not_col_1 with C2, HBC.
        apply col_cop__cop with C'; Col.
    }
    left; apply par_strict_col_par_strict with C'; auto.
    { split; trivial.
      intros [X [HX1 HX2]].
      revert HX2.
      apply HC'; Cop.
    }
    assert (HBC' : 严格平行 B1 B2 C1 C').
    { split; trivial.
      intros [X [HX1 HX2]].
      revert HX2.
      apply HC', col_cop__cop with B2; Col; Cop.
    }
    destruct (HP B1 B2 C1 C2 C1 C' C1); Par; Col.
Qed.

End playfair_par_trans.
