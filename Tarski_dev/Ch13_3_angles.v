 (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_2_length.

Section Angles_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

(************************************* angle *****************************)

Lemma ang_exists : forall A B C, A <> B -> C <> B -> exists a, 角谓词 a /\ a A B C.
Proof.
    intros.
    exists (fun D E F => 等角 A B C D E F).
    split.
      unfold 角谓词.
      exists A.
      exists B.
      exists C.
      split; auto.
      split; auto.
      intros.
      split.
        auto.
      auto.
    apply conga_refl; auto.
Qed.

Lemma ex_points_ang : forall a , 角谓词 a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    unfold 角谓词 in H.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:= H1 A B C).
    destruct HH.
    exists A.
    exists B.
    exists C.
    apply H2.
    apply conga_refl; auto.
Qed.

End Angles_1.

Ltac ang_instance a A B C :=
  assert(tempo_ang:= ex_points_ang a);
  match goal with
    |H: 角谓词 a |-  _ => assert(tempo_H:=H); apply tempo_ang in tempo_H;
                       elim tempo_H; intros A ; let tempo_HP := fresh "tempo_HP" in intro tempo_HP; clear tempo_H;
                       elim tempo_HP; intro B; let tempo_HQ := fresh "tempo_HQ" in intro tempo_HQ ; clear tempo_HP ;
                       elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_ang.

Section Angles_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma ang_conga : forall a A B C A' B' C', 角谓词 a -> a A B C -> a A' B' C' -> 等角 A B C A' B' C'.
Proof.
    intros.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:=H3 A B C).
    assert(HH1:= H3 A' B' C').
    destruct HH.
    destruct HH1.
    apply H5 in H0.
    apply H7 in H1.
    eapply conga_trans.
      apply conga_sym.
      apply H0.
    auto.
Qed.

Lemma is_ang_conga : forall A B C A' B' C' a, Ang A B C a -> Ang A' B' C' a -> 等角 A B C A' B' C'.
Proof.
    intros.
    unfold Ang in *.
    spliter.
    eapply (ang_conga a); auto.
Qed.

Lemma is_ang_conga_is_ang : forall A B C A' B' C' a, Ang A B C a -> 等角 A B C A' B' C' -> Ang A' B' C' a.
Proof.
    intros.
    unfold Ang in *.
    spliter.
    split.
      auto.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_not_ang : forall A B C A' B' C' a , 角谓词 a -> ~(等角 A B C A' B' C') -> a A B C -> ~(a A' B' C').
Proof.
    intros.
    intro.
    assert(HH:=ang_conga a A B C A' B' C' H H1 H2).
    contradiction.
Qed.

Lemma not_conga_is_ang : forall A B C A' B' C' a , ~(等角 A B C A' B' C') -> Ang A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold Ang in H0.
    spliter.
    intro.
    apply H.
    apply (ang_conga a); auto.
Qed.

Lemma not_cong_is_ang1 : forall A B C A' B' C' a , ~(等角 A B C A' B' C') -> Ang A B C a -> ~(Ang A' B' C' a).
Proof.
    intros.
    intro.
    unfold Ang in *.
    spliter.
    apply H.
    apply (ang_conga a); auto.
Qed.

Lemma ex_eqa : forall a1 a2, (exists A , exists B, exists C, Ang A B C a1 /\ Ang A B C a2)  -> EqA a1 a2.
Proof.
    intros.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:=H).
    assert(HH0:=H0).
    unfold Ang in HH.
    unfold Ang in HH0.
    spliter.
    unfold EqA.
    repeat split; auto; intro.
      assert(等角 A B C A0 B0 C0).
        eapply (is_ang_conga _ _ _ _ _ _ a1); auto.
        split; auto.
      assert(Ang A0 B0 C0 a2).
        apply (is_ang_conga_is_ang A B C); auto.
      unfold Ang in H7.
      tauto.
    assert(等角 A B C A0 B0 C0).
      eapply (is_ang_conga _ _ _ _ _ _ a2); auto.
      split; auto.
    assert(Ang A0 B0 C0 a1).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold Ang in H7.
    tauto.
Qed.

Lemma all_eqa : forall A B C a1 a2, Ang A B C a1 -> Ang A B C a2 -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_ang_distinct : forall A B C a , Ang A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    unfold Ang in H.
    spliter.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    unfold 等角 in H0.
    spliter.
    tauto.
Qed.


Lemma null_ang : forall A B C D a1 a2, Ang A B A a1 -> Ang C D C a2 -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B A).
      apply H.
    eapply (is_ang_conga_is_ang C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_ang_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_ang_distinct in H.
    tauto.
Qed.

Lemma flat_ang : forall A B C A' B' C' a1 a2, Bet A B C -> Bet A' B' C' -> Ang A B C a1 -> Ang A' B' C' a2  -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B C).
      apply H1.
    eapply (is_ang_conga_is_ang A' B' C').
      apply H2.
    apply is_ang_distinct in H1.
    apply is_ang_distinct in H2.
    spliter.
    eapply conga_line; auto.
Qed.

Lemma ang_distinct: forall a A B C, 角谓词 a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(Ang A B C a).
      split; auto.
    apply (is_ang_distinct _ _ _ a); auto.
Qed.

Lemma ex_ang : forall A B C, B <> A -> B <> C -> exists a, 角谓词 a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => 等角 A B C X Y Z).
    unfold 角谓词.
    split.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      split.
        auto.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

(************************************* 为锐角 angle *****************************************)

Lemma anga_exists : forall A B C, A <> B -> C <> B -> 为锐角 A B C -> exists a, 锐角谓词 a /\ a A B C.
Proof.
    intros.
    exists (fun D E F => 等角 A B C D E F).
    split.
      unfold 角谓词.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      intros.
      split; auto.
    apply conga_refl; auto.
Qed.

Lemma anga_is_ang : forall a, 锐角谓词 a -> 角谓词 a.
Proof.
    intros.
    unfold 锐角谓词 in H.
    unfold 角谓词.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    apply acute_distincts in H.
    spliter.
    split.
      auto.
    split.
      auto.
    intros.
    split.
      intro.
      assert(Ang X Y Z a).
        unfold Ang.
        split.
          unfold 角谓词.
          exists A.
          exists B.
          exists C.
          split.
            assumption.
          split.
            assumption.
          auto.
        assert(HH:= H0 X Y Z).
        apply HH.
        auto.
      unfold Ang in H3.
      spliter.
      auto.
    intro.
    apply H0.
    auto.
Qed.

Lemma ex_points_anga : forall a , 锐角谓词 a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    assert(HH:=H).
    apply anga_is_ang in H.
    ang_instance a A B C.
    exists A.
    exists B.
    exists C.
    assumption.
Qed.

End Angles_2.

Ltac anga_instance a A B C :=
  assert(tempo_anga:= ex_points_anga a);
  match goal with
    |H: 锐角谓词 a |-  _ => assert(tempo_H:=H); apply tempo_anga in tempo_H;
                                 elim tempo_H; intros A ;
                                 let tempo_HP := fresh "tempo_HP" in
                                 intro tempo_HP; clear tempo_H;
                                 elim tempo_HP; intro B;
                                 let tempo_HQ := fresh "tempo_HQ" in
                                 intro tempo_HQ ; clear tempo_HP ;
                        elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_anga.

Require Import Setoid.

Section Angles_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma anga_conga : forall a A B C A' B' C', 锐角谓词 a -> a A B C -> a A' B' C' -> 等角 A B C A' B' C'.
Proof.
    intros.
    apply (ang_conga a); auto.
    apply anga_is_ang.
    auto.
Qed.

Lemma is_anga_to_is_ang : forall A B C a, 锐角 A B C a -> Ang A B C a.
Proof.
    intros.
    unfold 锐角 in H.
    unfold Ang.
    spliter.
    split.
      apply anga_is_ang.
      auto.
    auto.
Qed.

Lemma is_anga_conga : forall A B C A' B' C' a, 锐角 A B C a -> 锐角 A' B' C' a -> 等角 A B C A' B' C'.
Proof.
    intros.
    unfold 锐角 in *.
    spliter.
    apply (anga_conga a); auto.
Qed.

Lemma is_anga_conga_is_anga : forall A B C A' B' C' a, 锐角 A B C a -> 等角 A B C A' B' C' -> 锐角 A' B' C' a.
Proof.
    intros.
    unfold 锐角 in *.
    spliter.
    split.
      auto.
    apply anga_is_ang in H.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_is_anga : forall A B C A' B' C' a , ~ 等角 A B C A' B' C' -> 锐角 A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold 锐角 in H0.
    spliter.
    intro.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma not_cong_is_anga1 : forall A B C A' B' C' a , ~ 等角 A B C A' B' C' -> 锐角 A B C a -> ~ 锐角 A' B' C' a.
Proof.
    intros.
    intro.
    unfold 锐角 in *.
    spliter.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma ex_eqaa : forall a1 a2, (exists A , exists B, exists C, 锐角 A B C a1 /\ 锐角 A B C a2)  -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    split; apply is_anga_to_is_ang; auto.
Qed.

Lemma all_eqaa : forall A B C a1 a2, 锐角 A B C a1 -> 锐角 A B C a2 -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqaa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_anga_distinct : forall A B C a , 锐角 A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    apply (is_ang_distinct A B C a).
    apply is_anga_to_is_ang.
    auto.
Qed.

Global Instance eqA_equivalence : Equivalence EqA.
Proof.
split.
unfold Reflexive.
intros.
unfold EqA.
intros;tauto.
unfold Symmetric, EqA.
intros.
firstorder.
unfold Transitive, EqA.
intros.
rewrite H.
apply H0.
Qed.

Lemma null_anga : forall A B C D a1 a2, 锐角 A B A a1 -> 锐角 C D C a2 -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqaa A B A).
      apply H.
    eapply (is_anga_conga_is_anga C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_anga_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_anga_distinct in H.
    tauto.
Qed.

Lemma anga_distinct: forall a A B C, 锐角谓词 a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(锐角 A B C a).
      split; auto.
    apply (is_anga_distinct _ _ _ a); auto.
Qed.

Lemma out_is_len_eq : forall A B C l, Out A B C -> Len A B l -> Len A C l -> B = C.
Proof.
    intros.
    assert(Cong A B A C).
      apply (is_len_cong _ _ _ _ l); auto.
    assert(A <> C).
      unfold Out in H.
      spliter.
      auto.
    eapply (l6_11_uniqueness A A C C ); Cong.
    apply out_trivial.
    auto.
Qed.

Lemma out_len_eq : forall A B C l, Q_Cong l -> Out A B C -> l A B -> l A C -> B = C.
Proof.
    intros.
    apply (out_is_len_eq A _ _ l).
      auto.
      split; auto.
    split; auto.
Qed.

Lemma ex_anga : forall A B C, 为锐角 A B C -> exists a, 锐角谓词 a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => 等角 A B C X Y Z).
    unfold 锐角谓词.
    assert (HH := acute_distincts A B C H).
    spliter.
    split.
      exists A.
      exists B.
      exists C.
      split; auto.
      intros.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

Lemma not_null_ang_ang : forall a, 非零角谓词 a -> 角谓词 a.
Proof.
    intros.
    unfold 非零角谓词  in H.
    spliter; auto.
Qed.

Lemma not_null_ang_def_equiv : forall a, 非零角谓词 a <-> (角谓词 a /\ exists A, exists B, exists C, a A B C /\  ~Out B A C).
Proof.
    intros.
    split.
      intro.
      unfold 非零角谓词 in H.
      spliter.
      assert(HH:= H).
      unfold 角谓词 in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold 非零角谓词.
    split; auto.
    intros.
    assert(等角 A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (l11_21_a A0 B0 C0); auto.
Qed.

Lemma not_flat_ang_def_equiv : forall a, 非平角谓词 a <-> (角谓词 a /\ exists A, exists B, exists C, a A B C /\  ~Bet A B C).
Proof.
    intros.
    split.
      intro.
      unfold 非平角谓词 in H.
      spliter.
      assert(HH:= H).
      unfold 角谓词 in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold 非平角谓词.
    split; auto.
    intros.
    assert(等角 A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (bet_conga__bet A0 B0 C0); auto.
Qed.

Lemma ang_const : forall a A B, 角谓词 a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    apply(不重合的对称性) in H1.
    assert(HH:= H2 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H3.
      apply conga_refl; auto.
    assert(HH :=两点不重合则存在不共线的点 A B H0).
    ex_and HH P.
    induction(两点重合的决定性 A0 C0).
      subst C0.
      exists A.
      assert(HH:= (H2 A B A)).
      destruct HH.
      apply H7.
      apply conga_trivial_1; auto.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H H7 H1).
    ex_and HH C; auto.
    exists C.
    apply H2.
    auto.
Qed.

End Angles_3.

Ltac ang_instance1 a A B C :=
	assert(tempo_ang:= ang_const a A B);
        match goal with
           |H: 角谓词 a |-  _ => assert(tempo_H:= H);apply tempo_ang in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_ang.

Section Angles_4.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma ang_sym : forall a A B C, 角谓词 a -> a A B C -> a C B A.
Proof.
    intros.
    unfold 角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H2 C B A).
    destruct HH.
    apply H5.
    auto.
Qed.

Lemma ang_not_null_lg : forall a l A B C, 角谓词 a -> Q_Cong l -> a A B C -> l A B -> ~ 零长谓词 l.
Proof.
    intros.
    intro.
    unfold 角谓词 in H.
    unfold 零长谓词 in H3.
    spliter.
    unfold Q_Cong in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H6 A B C).
    destruct HH.
    assert(等角 A0 B0 C0 A B C).
      apply H8.
      auto.
    apply conga_distinct in H8.
      spliter.
      ex_and H0 A1.
      ex_and H14 B1.
      assert(HH:= H0 A B).
      destruct HH.
      ex_and H4 A'.
      assert(HH:= H0 A' A').
      destruct HH.
      assert(Cong A1 B1 A' A').
        apply H17.
        auto.
      assert(Cong A1 B1 A B).
        apply H15.
        auto.
      apply 等长的同一性 in H17.
        subst B1.
        apply 等长的对称性 in H19.
        apply 等长的同一性 in H19.
        contradiction.
      auto.
    auto.
Qed.

Lemma ang_distincts : forall a A B C, 角谓词 a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= ang_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply ang_sym; auto.
    assert(HQ:= ang_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold 零长谓词.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold 零长谓词.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma anga_sym : forall a A B C, 锐角谓词 a -> a A B C -> a C B A.
Proof.
    intros.
    unfold 锐角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H1 A B C).
    destruct HH.
    apply H3 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H1 C B A).
    destruct HH.
    apply H4.
    auto.
Qed.

Lemma anga_not_null_lg : forall a l A B C, 锐角谓词 a -> Q_Cong l -> a A B C -> l A B -> ~ 零长谓词 l.
Proof.
    intros.
    intro.
    unfold 锐角谓词 in H.
    unfold 零长谓词 in H3.
    spliter.
    unfold Q_Cong in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H5 A B C).
    destruct HH.
    assert(等角 A0 B0 C0 A B C).
      apply H7.
      auto.
    apply conga_distinct in H8.
    spliter.
    ex_and H0 A1.
    ex_and H13 B1.
    assert(HH:= H0 A B).
    destruct HH.
    ex_and H4 A'.
    assert(HH:= H0 A' A').
    destruct HH.
    assert(Cong A1 B1 A' A').
      apply H16.
      auto.
    assert(Cong A1 B1 A B).
      apply H14.
      auto.
    apply 等长的同一性 in H17.
    subst B1.
    apply 等长的对称性 in H18.
    apply 等长的同一性 in H18.
    contradiction.
Qed.

Lemma anga_distincts : forall a A B C, 锐角谓词 a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= anga_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply anga_sym; auto.
    assert(HQ:= anga_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold 零长谓词.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold 零长谓词.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma ang_const_o : forall a A B P, ~Col A B P -> 角谓词 a -> 非零角谓词 a -> 非平角谓词 a -> exists C, a A B C /\ OS A B C P.
Proof.
    intros.
    assert(HH:= H0).
    unfold 角谓词 in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    apply(不重合的对称性) in H4.
    assert(HH:= H5 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H6.
      apply conga_refl; auto.
    assert(HH:=ang_distincts a A0 B0 C0 H0 H8).
    assert(A0 <> C0).
      intro.
      subst C0.
      unfold 非零角谓词 in H1.
      spliter.
      assert(HH:=H11 A0 B0 A0 H8).
      apply HH.
      apply out_trivial; auto.
    spliter.
    assert(A <> B).
      intro.
      subst B.
      apply H.
      Col.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H10 H9 H4).
    ex_and HH C; auto.
    exists C.
    assert(a A B C).
      assert(HH:= H5 A B C).
      destruct HH.
      apply H15.
      auto.
    split.
      auto.
    induction H14.
      auto.
    unfold 非零角谓词 in H1.
    spliter.
    assert(HH:= H16 A B C H15).
    unfold 非平角谓词 in H2.
    spliter.
    assert(Hh:=H17 A B C H15).
    apply False_ind.
    assert(HH0:=ang_distincts a A B C H0 H15).
    spliter.
    assert(HP:=or_bet_out A B C).
    induction HP.
      contradiction.
    induction H20.
      contradiction.
    contradiction.
Qed.

Lemma anga_const : forall a A B, 锐角谓词 a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    apply anga_is_ang in H.
    apply ang_const; auto.
Qed.

End Angles_4.

Ltac anga_instance1 a A B C :=
	assert(tempo_anga:= anga_const a A B);
        match goal with
           |H: 锐角谓词 a |-  _ => assert(tempo_H:= H); apply tempo_anga in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_anga.

Section Angles_5.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma null_anga_null_anga' : forall a, 锐零角谓词 a <-> 零角谓词' a.
Proof.
    intro.
    split.
      intro.
      unfold 锐零角谓词 in H.
      unfold 零角谓词'.
      spliter.
      split.
        auto.
      anga_instance a A B C.
      assert(HH:= H0 A B C H1).
      exists A.
      exists B.
      exists C.
      split; auto.
    intro.
    unfold 零角谓词' in H.
    unfold 锐零角谓词.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    split; auto.
    intros.
    assert(等角 A B C A0 B0 C0).
      apply (anga_conga a); auto.
    apply (l11_21_a A B C); auto.
Qed.

Lemma is_null_anga_out : forall a A B C, 锐角谓词 a -> a A B C -> 锐零角谓词 a -> Out B A C.
Proof.
    intros.
    unfold 锐零角谓词 in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.


Lemma acute_not_bet : forall A B C, 为锐角 A B C -> ~Bet A B C.
Proof.
    intros.
    unfold 为锐角 in H.
    ex_and H A0.
    ex_and H0 B0.
    ex_and H C0.
    unfold 角度小于 in H0.
    spliter.
    unfold 角度小于等于 in H0.
    ex_and H0 P.
    unfold 在角内 in H0.
    spliter.
    ex_and H5 X.
    intro.
    apply conga_distinct in H2.
    spliter.
    assert(A<>C) by (intro; treat_equalities; auto).
    induction H6.
      subst X.
      apply H1.
      apply conga_line; auto.
    assert(Bet A0 B0 P).
      apply (bet_conga__bet A B C); auto.
    assert(Bet A0 B0 C0).
      unfold Out in H6.
      spliter.
      induction H15.
        eBetween.
      eBetween.
    apply H1.
    apply (conga_line A B C); auto.
Qed.

Lemma anga_acute : forall a A B C , 锐角谓词 a -> a A B C -> 为锐角 A B C.
Proof.
    intros.
    unfold 锐角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= acute_lea_acute A B C A0 B0 C0).
    apply HH.
      auto.
    unfold 角度小于等于.
    exists C0.
    split.
      unfold 在角内.
      apply acute_distincts in H.
      spliter.
      repeat split; auto.
      exists C0.
      split.
        Between.
      right.
      apply out_trivial.
      auto.
    assert(HP:= H1 A B C).
    destruct HP.
    apply conga_sym.
    apply H3.
    auto.
Qed.

Lemma not_null_not_col : forall a A B C, 锐角谓词 a -> ~ 锐零角谓词 a -> a A B C -> ~Col A B C.
Proof.
    intros.
    intro.
    apply H0.
    unfold 锐零角谓词.
    split.
      auto.
    assert(为锐角 A B C).
      apply (anga_acute a); auto.
    intros.
    assert(Out B A C).
      apply acute_col__out; auto.
    assert(HH:= anga_conga a A B C A0 B0 C0 H H1 H4).
    apply (l11_21_a A B C); auto.
Qed.


Lemma ang_cong_ang : forall a A B C A' B' C', 角谓词 a -> a A B C -> 等角 A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    assert(Ang A B C a).
      unfold Ang.
      split; auto.
    assert(Ang A' B' C' a).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold Ang in H3.
    tauto.
Qed.

Lemma is_null_ang_out : forall a A B C, 角谓词 a -> a A B C -> 零角谓词 a -> Out B A C.
Proof.
    intros.
    unfold 零角谓词 in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.

Lemma out_null_ang : forall a A B C, 角谓词 a -> a A B C -> Out B A C -> 零角谓词 a.
Proof.
    intros.
    unfold 零角谓词.
    split.
      auto.
    intros.
    assert(HH:=l11_21_a A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma bet_flat_ang : forall a A B C, 角谓词 a -> a A B C -> Bet A B C -> 平角谓词 a.
Proof.
    intros.
    unfold 平角谓词.
    split.
      auto.
    intros.
    assert(HH:=bet_conga__bet A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma out_null_anga : forall a A B C, 锐角谓词 a -> a A B C -> Out B A C -> 锐零角谓词 a.
Proof.
    intros.
    unfold 锐零角谓词.
    split.
      auto.
    intros.
    assert(HH:=l11_21_a A B C A0 B0 C0 H1).
    apply HH.
    apply (anga_conga a); auto.
Qed.

Lemma anga_not_flat : forall a, 锐角谓词 a -> 非平角谓词 a.
Proof.
    intros.
    unfold 非平角谓词.
    split.
      apply anga_is_ang in H.
      auto.
    intros.
    assert(HH:= anga_acute a A B C H H0).
    unfold 锐角谓词 in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HP:= H1 A B C).
    apply acute_not_bet.
    auto.
Qed.


Lemma anga_const_o : forall a A B P, ~Col A B P -> ~ 锐零角谓词 a -> 锐角谓词 a -> exists C, a A B C /\ OS A B C P.
Proof.
    intros.
    assert(角谓词 a).
      apply anga_is_ang; auto.
    assert(非零角谓词 a).
      unfold 非零角谓词.
      split.
        auto.
      intros A' B' C' HP.
      intro.
      apply H0.
      eapply (out_null_anga a A' B' C'); auto.
    assert(非平角谓词 a).
      apply anga_not_flat.
      auto.
    assert(HH:= ang_const_o a A B P H H2 H3 H4).
    auto.
Qed.

Lemma anga_conga_anga : forall a A B C A' B' C' , 锐角谓词 a -> a A B C -> 等角 A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    unfold 锐角谓词 in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH := H2 A B C).
    assert(HP := H2 A' B' C').
    destruct HH.
    destruct HP.
    apply H4 in H0.
    assert(等角 A0 B0 C0 A' B' C').
      eapply conga_trans.
        apply H0.
      apply H1.
    apply H5.
    auto.
Qed.

Lemma anga_out_anga : forall a A B C A' C', 锐角谓词 a -> a A B C -> Out B A A' -> Out B C C' -> a A' B C'.
Proof.
    intros.
    assert(HH:= H).
    unfold 锐角谓词 in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    assert(HP:= H4 A B C).
    destruct HP.
    assert(等角 A0 B0 C0 A B C).
      apply H6.
      auto.
    assert(HP:= anga_distincts a A B C H H0).
    spliter.
    assert(等角 A B C A' B C').
      apply out2__conga; apply l6_6; assumption.
    assert(HH:= H4 A' B C').
    destruct HH.
    apply H11.
    apply (conga_trans _ _ _ A B C); auto.
Qed.

Lemma out_out_anga : forall a A B C A' B' C', 锐角谓词 a -> Out B A C -> Out B' A' C' -> a A B C -> a A' B' C'.
Proof.
    intros.
    assert(等角 A B C A' B' C').
      apply l11_21_b; auto.
    apply (anga_conga_anga a A B C); auto.
Qed.

Lemma is_null_all : forall a A B, A <> B -> 锐零角谓词 a -> a A B A.
Proof.
    intros.
    unfold 锐零角谓词 in H0.
    spliter.
    assert(HH:= H0).
    unfold 锐角谓词 in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    apply acute_distincts in H2.
    spliter.
    apply H3.
    assert (a A0 B0 C0).
      apply H3.
      apply conga_refl; auto.
    assert(HH:= (H1 A0 B0 C0 H5)).
    apply l11_21_b; auto.
    apply out_trivial.
    auto.
Qed.

Lemma anga_col_out : forall a A B C, 锐角谓词 a -> a A B C -> Col A B C -> Out B A C.
Proof.
    intros.
    assert(为锐角 A B C).
      apply (anga_acute a); auto.
    unfold Col in H1.
    induction H1.
      apply acute_not_bet in H2.
      contradiction.
    unfold Out.
    apply (anga_distinct a A B C) in H.
      spliter.
      repeat split; auto.
      induction H1.
        right.
        auto.
      left.
      Between.
    auto.
Qed.

Lemma ang_not_lg_null : forall a la lc A B C, Q_Cong la -> Q_Cong lc -> 角谓词 a ->
 la A B -> lc C B -> a A B C -> ~ 零长谓词 la /\ ~ 零长谓词 lc.
Proof.
    intros.
    assert(HH:=ang_distincts a A B C H1 H4).
    spliter.
    split.
      intro.
      unfold 零长谓词 in H7.
      spliter.
      ex_and H8 P.
      assert(HH:= lg_cong la A B P P H H2 H9).
      apply 等长的同一性 in HH.
      contradiction.
    intro.
    unfold 零长谓词 in H7.
    spliter.
    ex_and H8 P.
    assert(HH:= lg_cong lc C B P P H0 H3 H9).
    apply 等长的同一性 in HH.
    contradiction.
Qed.

Lemma anga_not_lg_null : forall a la lc A B C, Q_Cong la -> Q_Cong lc ->
 锐角谓词 a -> la A B -> lc C B -> a A B C -> ~ 零长谓词 la /\ ~ 零长谓词 lc.
Proof.
    intros.
    apply anga_is_ang in H1.
    apply(ang_not_lg_null a la lc A B C); auto.
Qed.

Lemma anga_col_null : forall a A B C, 锐角谓词 a -> a A B C -> Col A B C -> Out B A C /\ 锐零角谓词 a.
Proof.
    intros.
    assert(HH:= anga_distincts a A B C H H0).
    spliter.
    assert(Out B A C).
      induction H1.
        assert(HP:=anga_acute a A B C H H0).
        assert(HH:=acute_not_bet A B C HP).
        contradiction.
      induction H1.
        unfold Out.
        repeat split; auto.
      unfold Out.
      repeat split; auto.
      left.
      Between.
    split.
      auto.
    apply (out_null_anga a A B C); auto.
Qed.

Lemma eqA_preserves_ang: forall a b, 角谓词 a -> EqA a b -> 角谓词 b.
Proof.
intros.
unfold 角谓词 in *.
decompose [ex and] H.
exists x. exists x0. exists x1.
split.
assumption.
split.
assumption.
intros.
rewrite H4.
unfold EqA in H0.
apply H0.
Qed.

Lemma eqA_preserves_anga : forall a b, 锐角谓词 a -> 角谓词 b -> EqA a b -> 锐角谓词 b.
Proof.
    intros.
    assert (角谓词 a).
        apply eqA_preserves_ang with b;auto.
        symmetry;auto.
    unfold EqA in H1.
    anga_instance a A B C.

    assert(HH:= H1 A B C).
    destruct HH.
    unfold 锐角谓词.
    exists A.
    exists B.
    exists C.
    split.
      unfold 锐角谓词 in H.
      ex_and H A'.
      ex_and H6 B'.
      ex_and H C'.
      assert(a A' B' C').
        assert(HP:= H6 A B C).
        destruct HP.
        assert(等角 A B C A' B' C') by (apply conga_sym;auto).
        assert(HP:=is_ang_conga_is_ang A B C A' B' C' a).
        assert(Ang A' B' C' a).
          apply HP.
            split; auto.
          auto.
        unfold Ang in H10.
        spliter.
        auto.
      apply (acute_lea_acute _ _ _ A' B' C').
        auto.
      unfold 角度小于等于.
      exists C'.
      split.
        assert (HH:= acute_distincts A' B' C' H).
        spliter.
        apply inangle3123; auto.
      apply (is_ang_conga _ _ _ _ _ _ a).
        split; auto.
      split; auto.
    intros.
    split.
      intro.
      assert(HH:= H1 X Y Z).
      destruct HH.
      assert(Ang X Y Z a).
        eapply (is_ang_conga_is_ang A B C).
          split; auto.
        auto.
      unfold Ang in H9.
      spliter.
      auto.
    intro.
    assert(HH:= H1 X Y Z).
    destruct HH.
    assert(a X Y Z).
      auto.
    apply (is_ang_conga _ _ _ _ _ _ a).
      split; auto.
    split; auto.
Qed.

End Angles_5.