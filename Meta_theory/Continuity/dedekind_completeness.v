Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.completeness.
Require Import GeoCoq.Meta_theory.Continuity.grad.
Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

(** This file contains the proof that Dedekind completeness implies Hilbert's line completeness. *)

Section Completeness.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(** If there exists n such that (f A) X = n times (f A) (f B),
    then X belongs to the image of the line extension f *)

Lemma extension_grad : forall {Tm: 无维度中性塔斯基公理系统}
  {TmEQD : 无维度中性塔斯基公理系统_带两点重合决定性 Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  line_extension f P Q ->
  forall A B X, Col P Q A -> Col P Q B -> Grad (f A) (f B) X ->
  exists C, Col P Q C /\ Grad A B C /\ f C = X.
Proof.
intros Tm TmEQD P Q f [HPQ [fInj [fBet fCong]]] A B X HA HB HGrad.
elim (两点重合的决定性 A B); [intro; subst; apply grad112__eq in HGrad; subst|];
[exists B; repeat split; [auto|constructor]|intro HAB].
remember (f A) as fA; remember (f B) as fB.
induction HGrad as [|fA fB C C' ? HInd ? ?];
[exists B; repeat split; [auto|constructor|auto]|].
rename C into X, C' into X'; destruct HInd as [C [? []]]; trivial.
destruct (由一点往一方向构造等长线段 A C A B) as [C' []]; exists C'.
assert (Col P Q C')
  by (apply (共线的传递性5 A C); Col; apply grad_neq__neq13 with B; auto).
split; [auto|split; [apply 线性刻度_步进 with C; Cong|]].
apply (点的唯一构造 fA X fA fB); Cong; [|subst; auto..].
intro; subst X; assert (A = C) by (apply fInj; auto; congruence).
subst; apply grad121__eq, fInj in HGrad; auto.
Qed.

(** If there exists n such that (f A) X = (f A) (f B) divided by 2^n,
    then X belongs to the image of the line extension f *)

Lemma extension_gradexp : forall {Tm: 无维度中性塔斯基公理系统}
  {TmEQD : 无维度中性塔斯基公理系统_带两点重合决定性 Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  line_extension f P Q ->
  forall A B X, Col P Q A -> Col P Q B -> 在对数刻度上 (f A) X (f B) ->
  exists C, Col P Q C /\ 在对数刻度上 A C B /\ f C = X.
Proof.
intros Tm TmEQD P Q f [HPQ [fInj [fBet fCong]]] A B X HA HB.
remember (f A) as fA; remember (f B) as fB; rewrite gradexp__gradexpinv.
intro HI; induction HI as [|fA fB C C' ? ? ? HInd];
[exists B; repeat split; [auto|constructor|auto]|].
rename C into X, C' into X'; destruct HInd as [C [? []]]; auto.
destruct (中点的存在性 A C) as [C' []]; exists C'.
assert (Col P Q C')
  by (destruct (两点重合的决定性 A C); [treat_equalities|apply (共线的传递性5 A C)]; Col).
split; [auto|split; [|apply 中点的唯一性1 with fA fB; split; subst; auto]].
rewrite gradexp__gradexpinv; apply gradexpinv_stab with C; auto.
rewrite <- gradexp__gradexpinv; assumption.
Qed.

(** Given a line extension f to a line l in an Archimedean space, the image of f is dense in l *)

Lemma extension_image_density : forall {Tm: 无维度中性塔斯基公理系统}
  {TmEQD : 无维度中性塔斯基公理系统_带两点重合决定性 Tm}
  P Q (f : @Tpoint Tn -> @Tpoint Tm),
  @archimedes_axiom Tm ->
  line_extension f P Q ->
  forall A B, Col (f P) (f Q) A -> Col (f P) (f Q) B -> A <> B ->
  exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B.
Proof.
intros Tm TmEQD P Q f archi HPQ A B; revert P Q A B HPQ.
(* It suffices to prove the following statement *)
cut(forall P Q A B,
       line_extension f P Q ->
       Col (f P) (f Q) A -> Col (f P) (f Q) B -> A <> B ->
       Lt (f P) (f Q) A B -> Bet (f P) A B ->
       exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B).

  {
  (* Indeed *)
  intros HX P Q A B fPQ HColA HColB HAB.
  assert (Hf' := fPQ); destruct Hf' as [HPQ [fInj [fBet fCong]]].
  assert (HfPfQ : f P <> f Q) by (intro; apply HPQ, fInj; Col).
  destruct (reach__ex_gradexp_lt (f P) (f Q) A B) as [fQ' [HGrad' HLt]]; auto.
  (* Archimedes' axiom let us construct fQ' by repeated bisection such that
     (f P) fQ' is smaller than A B and Lemma 2 gives us Q' on PQ such that
     fQ' = f Q' *)
  destruct (extension_gradexp P Q f fPQ P Q fQ') as [Q' [_ [HGrad]]]; Col.
  subst fQ'; apply gradexp__grad in HGrad; apply gradexp__grad in HGrad'.
  assert (HPQ' : P <> Q') by (intro; subst; apply grad112__eq in HGrad; auto).
  assert (fPQ' : line_extension f P Q')
    by (apply line_extension_stability with Q; Col).
  assert (HCols : Col (f P) (f Q') A /\ Col (f P) (f Q') B /\ Col (f P) A B)
    by (split; [|split]; apply 共线的传递性2 with (f Q); Col).
  assert (HColX : forall X, Col P Q' X -> Col P Q X)
    by (intros; apply 共线的传递性2 with Q'; Col).
  destruct HCols as [HColA' [HColB' HE]].
  assert (HH : Bet (f P) A B \/ Bet (f P) B A ->
               exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B).
    {
    intros [|]; [destruct (HX P Q' A B) as [X]|destruct (HX P Q' B A) as [X]];
    Col; [exists X; intuition|apply 长度小于的右交换性, HLt|exists X; intuition].
    }
  (* Either we can conclude using HH which is a corrolary of the auxilliary
     statement or Bet A (f P) B holds in which case we are done *)
  destruct HE as [|[|]]; [apply HH; Between..|].
  destruct (两点重合的决定性 (f P) A); [subst; apply HH; Between|].
  destruct (两点重合的决定性 (f P) B); [subst; apply HH; Between|].
  exists P; repeat split; finish.
  }

  {
  intros P Q A B fPQ HColA HColB HAB HLt HBet.
  assert (Hf' := fPQ); destruct Hf' as [HPQ [fInj [fBet fCong]]].
  destruct (两点重合的决定性 (f P) A); [treat_equalities|].

    {
    assert (f P <> f Q) by (intro; apply HPQ, fInj; Col).
    (* Either (f P) is between (f Q) and B and then the symmetric of Q wrt  P is
       a desired point or (f Q) and B are on the same side of (f P) and then
       Q is such a point since these three points are collinear *)
    destruct (or_bet_out (f Q) (f P) B) as [HBet|[HOut|]]; [..|exfalso; Col];
    [destruct (由一点往一方向构造等长线段 Q P P Q) as [Q' []]; exists Q'|exists Q];
    [assert (f Q' <> f P) by (intro; cut (P = Q'); 统计不重合点; finish)|];
    repeat split; Col; [| |apply l6_13_1; Le|];
    [|intro; subst; destruct HLt; intuition..].
    assert (Bet (f Q) (f P) (f Q')) by (apply fBet; Col).
    assert (Cong (f P) (f Q') (f P) (f Q)) by (apply fCong; Col).
    apply l6_13_1; [apply l6_2 with (f Q); Between|].
    apply 长度小于等于的传递性 with (f P) (f Q); Le.
    }

    {
    (* Again the cases are similar and it suffices to show the conclusion
       when (f Q) is between (f P) and A *)
    cut (forall P Q A B,
            line_extension f P Q ->
            A <> B -> Lt (f P) (f Q) A B ->
            Bet (f P) (f Q) A -> Bet (f P) A B ->
            exists X, Col P Q X /\ Bet A (f X) B /\ f X <> A /\ f X <> B).

      {
      (* Since these three points are collinear either we the auxilliary
         statement allows to conclude (we can swap P and Q) or A is between
         (f P) and (f Q) *)
      intro HX; destruct HColA as [|[]]; [destruct (HX P Q A B) as [X]; Col|..].

        {
        (* In which case either A = (f Q) and then the symmetric of P wrt Q is
           a desired point or A <> (f Q) and then Q is such a point *)
        destruct (两点重合的决定性 (f Q) A); [treat_equalities|exists Q].

          {
          destruct (由一点往一方向构造等长线段 P Q P Q) as [Q' []]; exists Q'.
          assert (Bet (f P) (f Q) (f Q')) by (apply fBet; Col).
          assert (Cong (f Q) (f Q') (f P) (f Q)) by (apply fCong; Col).
          assert (f Q <> f Q') by (统计不重合点; auto).
          assert (HLt2 : Lt (f Q) (f Q') (f Q) B)
            by (apply (等长保持小于关系 (f P) (f Q) (f Q) B); Cong).
          repeat split; Col; [|intro; subst; destruct HLt2; Cong].
          apply l6_13_1; Le; apply l6_2 with (f P); Between.
          }

          {
          assert (HLt2 : Lt A (f Q) A B)
            by (apply 长度小于等于_小于_传递性 with (f P) (f Q); Le).
          repeat split; Col; [|intro; subst; destruct HLt2; Cong].
          apply l6_13_1; Le; apply l6_2 with (f P); Between.
          }
        }

        {
        destruct (HX Q P A B) as [X]; [..|exists X; repeat split; intuition];
        [apply line_extension_symmetry|Between|apply 长度小于的左交换性, HLt|..];
        [auto| |apply 中间性的外传递性1 with (f P)]; Between.
        }
      }

      {
      (* Repeated duplication of (f P) (f Q) allows to reach
         a point Y (reach__grad_min) that is strictly between A and B and
         there is a point X on P Q such that (f X) = Y by the analogous of
         Lemma 2 for duplication instead of bisection *)
      clear dependent P; clear Q; clear dependent A; clear B.
      intros P Q A B fPQ HAB HLt HBet1 HBet2.
      cut (exists C, Grad (f P) (f Q) C /\ Bet A C B /\ C <> A /\ C <> B);
      [intros [C []]; destruct (extension_grad _ _ _ fPQ P Q C) as [X]; Col;
       exists X; 分离合取式; subst; auto|].
      assert (Hdiff : f P <> f Q) by (intro; destruct fPQ as [? []]; Col).
      destruct (reach__grad_min (f P) (f Q) A) as [D [E]]; auto; 分离合取式.
      assert (Bet D A E) by (apply (中间性的交换传递性1 (f P)); assumption).
      exists E; repeat split; [apply 线性刻度_步进 with D| | |intro; subst E]; auto;
      [|apply 小于推出反向不小于等于 in HLt; apply HLt, 长度小于等于的传递性 with D B; 分离合取式; Le].
      apply l6_13_1; [destruct (两点重合的决定性 A D); [subst D|]|];
      [apply l6_2 with (f P); 统计不重合点|apply l6_2 with D|]; eBetween.
      apply 长度小于等于的传递性 with D E; Le.
      apply 长度小于等于的传递性 with (f P) (f Q); Le.
      }
    }
  }
Qed.

Lemma dedekind_variant__completeness : dedekind_variant -> line_completeness.
Proof.
  intros dedekind Tm Tm2 P Q f archi fLineExt A HA.
  destruct (两点重合的决定性 (f P) A).
    subst; exists P; split; Col.
  assert (HR : exists R, Col P Q R /\ Bet (f P) A (f R)).
  { destruct (由一点往一方向构造等长线段 (f P) A (f P) A) as [A1 []].
    统计不重合点.
    destruct (extension_image_density P Q f archi fLineExt A A1) as [R [HR1 [HR2 []]]]; Col.
      apply 共线的传递性2 with A; Col.
    exists R; split; eBetween.
  }
  destruct HR as [R []].
  destruct (dedekind (fun X => Col P Q X /\ Bet (f P) (f X) A /\ (f X) <> A)
    (fun X => Col P Q X /\ Bet (f P) A (f X)) P R) as [B HB]; simpl.
  - repeat split; finish.
  - split; assumption.
  - intros Z HZ.
    assert (Col P Q Z) by (统计不重合点; apply 共线的传递性2 with R; Col).
    destruct (两点重合的决定性 (f Z) A).
      subst; right; split; Between.
    assert (HOut : Out (f P) (f Z) A).
    { apply l6_7 with (f R); [|Out].
      destruct HZ as [HZP [HRP Hdij]].
      destruct fLineExt as [HPQ [fInj [fBet fCong]]].
      repeat split.
        intro; apply HZP, fInj; Col.
        intro; apply HRP, fInj; Col.
      destruct Hdij; [left|right]; apply fBet; Col.
    }
    destruct HOut as [_ [_ [|]]]; [left|right]; split; auto.
  - intros X Y [HX1 [HX2 HX3]] [HY1 HY2].
    split.
      apply (line_extension_reverse_bet f P Q); Col; eBetween.
      intro; treat_equalities; contradiction.

  - exists B.
    assert (HBet : Bet P B R).
      apply HB; split; Col; Between.
    assert (Col P Q B).
      apply 共线的传递性2 with R; Col; intro; treat_equalities; auto.
    destruct (两点重合的决定性 (f B) A); [split; assumption|].
    exfalso.
    assert (Hf := fLineExt).
    destruct Hf as [HPQ [finj [fBet fCong]]].
    destruct (extension_image_density P Q f archi fLineExt A (f B)) as [X [HX1 [HX2 [HX3 Habs]]]]; auto.
      apply (pres_bet_line__col f P Q); Col.
    destruct (l5_3 (f P) A (f B) (f R)); auto; [apply fBet; Col|apply Habs..].
    * apply 双中间性推出点重合 with (f P).
        apply 中间性的对称性, fBet, HB; try split; Col; Between.
        apply 中间性的内传递性1 with (f B); assumption.
      clear dependent R; eBetween.
    * apply 双中间性推出点重合 with (f P).
        clear dependent R; eBetween.
      apply 中间性的交换传递性1 with (f R); [|apply bet3__bet with A (f B); eBetween].
      apply 中间性的对称性, fBet; Col.
      apply HB; split; Col.
      split; trivial.
      apply 中间性的内传递性2 with (f B); Between.
Qed.

End Completeness.
