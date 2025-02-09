Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section T12_1.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma par_reflexivity : forall A B, A<>B -> Par A B A B.
Proof.
    intros.
    unfold Par.
    unfold 严格平行.
    right.
    repeat split.
      assumption.
      assumption.
      apply AAB型共线.
    apply ABA型共线.
Qed.

Lemma par_strict_irreflexivity : forall A B,
 ~ 严格平行 A B A B.
Proof.
    intros.
    intro.
    unfold 严格平行 in H.
    分离合取式.
    apply H0.
    exists A.
    split; apply AAB型共线.
Qed.

Lemma not_par_strict_id : forall A B C,
 ~ 严格平行 A B A C.
Proof.
    intros.
    intro.
    unfold 严格平行 in H.
    分离合取式.
    apply H0.
    exists A.
    split; Col.
Qed.

Lemma par_id : forall A B C,
 Par A B A C -> Col A B C.
Proof.
    intros.
    unfold Par in H.
    induction H.
      exfalso.
      apply (not_par_strict_id A B C H).
    分离合取式;Col.
Qed.

Lemma par_strict_not_col_1 : forall A B C D,
 严格平行 A B C D  -> ~ Col A B C.
Proof.
    intros.
    unfold 严格平行 in *.
    分离合取式.
    intro.
    apply H0.
    exists C.
    split;Col.
Qed.

Lemma par_strict_not_col_2 : forall A B C D,
 严格平行 A B C D  -> ~ Col B C D.
Proof.
    intros.
    unfold 严格平行 in *.
    分离合取式.
    intro.
    apply H0.
    exists B.
    split;Col.
Qed.

Lemma par_strict_not_col_3 : forall A B C D,
 严格平行 A B C D  -> ~ Col C D A.
Proof.
    intros.
    unfold 严格平行 in *.
    分离合取式.
    intro.
    apply H0.
    exists A.
    split;Col.
Qed.

Lemma par_strict_not_col_4 : forall A B C D,
 严格平行 A B C D  -> ~ Col A B D.
Proof.
    intros.
    unfold 严格平行 in *.
    分离合取式.
    intro.
    apply H0.
    exists D.
    split;Col.
Qed.

Lemma par_strict_not_cols : forall A B C D,
 严格平行 A B C D -> ~ Col A B C /\ ~ Col B C D /\ ~ Col C D A /\ ~ Col A B D.
Proof.
    intros.
    repeat split.
    apply par_strict_not_col_1 with D, H.
    apply (par_strict_not_col_2 A), H.
    apply par_strict_not_col_3 with B, H.
    apply par_strict_not_col_4 with C, H.
Qed.

Lemma par_strict_symmetry :forall A B C D,
 严格平行 A B C D -> 严格平行 C D A B.
Proof.
    unfold 严格平行.
    intros.
    分离合取式.
    split.
      apply 等价共面CDAB;assumption.
    intro.
    apply H0.
    ex_and H1 X.
    exists X.
    split; assumption.
Qed.

Lemma par_symmetry :forall A B C D,
 Par A B C D -> Par C D A B.
Proof.
    unfold Par.
    intros.
    induction H.
      left.
      apply par_strict_symmetry.
      assumption.
    分离合取式.
    right.
    repeat split; try assumption.
      eapply (共线的传递性2 _ D);Col.
    eapply (共线的传递性2 _ C);Col.
Qed.

Lemma par_strict_left_comm : forall A B C D,
 严格平行 A B C D -> 严格平行 B A C D.
Proof.
    unfold 严格平行.
    intros.
    decompose [and] H;clear H.
    split.
      apply 等价共面BACD;assumption.
    intro.
    apply H1.
    ex_and H X.
    exists X; Col.
Qed.

Lemma par_strict_right_comm : forall A B C D,
 严格平行 A B C D -> 严格平行 A B D C.
Proof.
    unfold 严格平行.
    intros.
    decompose [and] H;clear H.
    split.
      apply 等价共面ABDC;assumption.
    intro.
    apply H1.
    ex_and H X.
    exists X; Col.
Qed.

Lemma par_strict_comm : forall A B C D,
 严格平行 A B C D -> 严格平行 B A D C.
Proof.
    intros.
    apply par_strict_left_comm in H.
    apply par_strict_right_comm.
    assumption.
Qed.

Lemma par_left_comm : forall A B C D,
 Par A B C D -> Par B A C D.
Proof.
    unfold Par.
    intros.
    induction H.
      left.
      apply par_strict_left_comm; assumption.
    right.
    分离合取式.
    Col5.
Qed.

Lemma par_right_comm : forall A B C D,
 Par A B C D -> Par A B D C.
Proof.
    intros.
    apply par_symmetry in H.
    apply par_symmetry.
    apply par_left_comm.
    assumption.
Qed.

Lemma par_comm : forall A B C D,
 Par A B C D -> Par B A D C.
Proof.
    intros.
    apply par_left_comm.
    apply par_right_comm.
    assumption.
Qed.

Lemma par_strict_distinct : forall A B C D,
 严格平行 A B C D ->
  A<>B /\ A<>C /\ A<>D /\ B<>C /\ B<>D /\ C<>D.
Proof.
    unfold 严格平行.
    intros; 分离合取式.
    repeat split; intro; apply H0; [exists C|exists A|exists A|exists B..]; subst; split; Col.
Qed.

Lemma par_neq1 : forall A B C D, Par A B C D -> A <> B.
Proof.
    intros.
    induction H.
      apply par_strict_distinct in H; 分离合取式; auto.
    分离合取式; auto.
Qed.

Lemma par_neq2 : forall A B C D, Par A B C D -> C <> D.
Proof. intros; apply par_symmetry in H; apply (par_neq1 C D A B H). Qed.

End T12_1.

Ltac 统计不重合点 :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := 不共线则不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := 非中间性则任两点不重合 X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_AB不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BA不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_BC不等推AC不等 A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 中间性_CB不等推AC不等 A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 与不同点等长之点不同_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 与不同点等长之点不同_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于等于推出不重合 A B C D (不重合的对称性 B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= 小于推出不重合 A B C D H);clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= 严格中点组推论1 I A B (不重合的对称性 B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= 严格中点组推论2 I A B (不重合的对称性 A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:中点 ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:中点 ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= 严格中点组推论3 I A B (不重合的对称性 B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合1 A B C H (不重合的对称性 B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= 直角一边不重合则另一边不重合2 A B C H (不重合的对称性 C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直推出不重合 A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:垂直于 ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= 垂直于推出不重合 X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= 角等推AB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= 角等推CB不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= 角等推DE不重合 A B C A' B' C' H);clean_reap_hyps
      | H:等角 ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= 角等推FE不重合 A B C A' B' C' H);clean_reap_hyps

      | H:(在角内 ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := 在角内推出点不重合 A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于等于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于等于推出点不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:角度小于 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := 角度小于推不重合 A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为锐角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为锐角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(为钝角 ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := 角为钝角推不重合 A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:互为补角 ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(垂直平面于 ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= par_neq1 A B C D H);clean_reap_hyps
      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= par_neq2 A B C D H);clean_reap_hyps
      | H:严格平行 ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp6 A B A C A D B C B D C D);
       assert (T:= par_strict_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
 end.

Ltac ColR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
   treat_equalities; assert_cols; Col; 统计不重合点; Col_refl tpoint col.

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y H))

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y H))

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);Side)

      | H:~ 共面 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := 四点不共面则任三点不共线 A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:严格平行 ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm_ncol4 A B C D;
      assert (h := par_strict_not_cols A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.

Ltac CopR :=
 let tpoint := constr:(Tpoint) in
 let col := constr:(Col) in
 let cop := constr:(共面) in
   treat_equalities; assert_cols; clean; assert_ncols; 推导四点共面; auto 2 with 共面的排列;
   solve[apply 共线三点和任一点共面; Col|apply 等价共面ABDC, 共线三点和任一点共面; Col
        |apply 等价共面ADBC, 共线三点和任一点共面; Col|apply 等价共面DABC, 共线三点和任一点共面; Col
        |copr_aux; Cop_refl tpoint col cop] || fail "Can not be deduced".


Hint Resolve
 par_reflexivity par_strict_irreflexivity
 par_strict_symmetry par_strict_comm par_strict_right_comm par_strict_left_comm
 par_symmetry par_comm par_right_comm par_left_comm : par.

Hint Resolve par_strict_not_col_1 par_strict_not_col_2
             par_strict_not_col_3 par_strict_not_col_4 : col.

Ltac Par := auto 4 with par.

Section T12_2.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma Par_cases :
  forall A B C D,
  Par A B C D \/ Par B A C D \/ Par A B D C \/ Par B A D C \/
  Par C D A B \/ Par C D B A \/ Par D C A B \/ Par D C B A ->
  Par A B C D.
Proof.
    intros.
    decompose [or]  H;Par.
Qed.

Lemma Par_perm :
  forall A B C D,
  Par A B C D ->
  Par A B C D /\ Par B A C D /\ Par A B D C /\ Par B A D C /\
  Par C D A B /\ Par C D B A /\ Par D C A B /\ Par D C B A.
Proof.
    intros.
    do 7 (split; Par).
Qed.

Lemma 严格平行_cases :
  forall A B C D,
  严格平行 A B C D \/ 严格平行 B A C D \/ 严格平行 A B D C \/ 严格平行 B A D C \/
  严格平行 C D A B \/ 严格平行 C D B A \/ 严格平行 D C A B \/ 严格平行 D C B A ->
  严格平行 A B C D.
Proof.
    intros.
    decompose [or]  H; eauto with par.
Qed.

Lemma 严格平行_perm :
  forall A B C D,
  严格平行 A B C D ->
  严格平行 A B C D /\ 严格平行 B A C D /\ 严格平行 A B D C /\ 严格平行 B A D C /\
  严格平行 C D A B /\ 严格平行 C D B A /\ 严格平行 D C A B /\ 严格平行 D C B A.
Proof.
    intros.
    do 7 (split; Par).
Qed.

End T12_2.

Section T12_2'.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma l12_6 : forall A B C D,
 严格平行 A B C D -> OS A B C D.
Proof.
    intros.
    unfold 严格平行 in H.
    分离合取式.
    assert(HH:= cop_nts__os A B C D).
    apply HH.
      assumption.
      intro.
      apply H0.
      exists C;Col.
      intro.
      apply H0.
      exists D;Col.
    intro.
    apply H0.
    unfold TS in H1.
    分离合取式.
    ex_and H3 T.
    exists T.
    split; Col.
Qed.

Lemma pars__os3412 : forall A B C D,
 严格平行 A B C D -> OS C D A B.
Proof.
    intros.
    apply l12_6.
    apply par_strict_symmetry.
    assumption.
Qed.

Lemma perp_dec : forall A B C D, Perp A B C D \/ ~ Perp A B C D.
Proof.
    intros.
    induction (共线的决定性 A B C).
      induction (垂直于的决定性 C A B C D).
        left.
        apply l8_14_2_1a_垂直于转垂直 with C;auto.
      right.
      intro.
      apply H0. clear H0.
      apply 垂直于的右交换性.
      apply (l8_15_1_垂线顶点在该线上则其为垂点 A B D C).
        apply 垂直推出不重合 in H1.
        intuition.
      apply 垂直的右交换性;assumption.
    elim (l8_18_过一点垂线之垂点的存在性 A B C H); intros P HP.
    分离合取式.
    induction (两点重合的决定性 C D).
      subst.
      right.
      intro.
      assert (A <> B /\ D <> D) by (apply 垂直推出不重合;assumption).
      intuition.
    induction (共线的决定性 P C D).
      left.
      assert (A <> B /\ C <> P) by (apply 垂直推出不重合;assumption).
      分离合取式.
      apply 垂线共线点也构成垂直2 with P;Col.
    right.
    intro.
    apply H3.
    apply 等价共线CAB, cop_perp2__col with A B; [Cop|apply 垂直的对称性;assumption..].
Qed.

Lemma col_cop2_perp2__col : forall X1 X2 Y1 Y2 A B,
 Perp X1 X2 A B -> Perp Y1 Y2 A B -> Col X1 Y1 Y2 ->
 共面 A B X2 Y1 -> 共面 A B X2 Y2 -> Col X2 Y1 Y2.
Proof.
    intros.
    induction(两点重合的决定性 X1 Y2).
      subst Y2.
      assert(Perp Y1 X1 A B).
        eapply 垂线共线点也构成垂直1.
          intro.
          treat_equalities.
          apply 垂直推出不重合 in H0.
          intuition.
          apply H0.
        Col.
      apply 等价共线BCA.
      apply cop_perp2__col with A B.
        assumption.
        apply H.
      apply 垂直的左交换性.
      assumption.
    assert(Perp Y2 X1 A B).
      eapply 垂线共线点也构成垂直1.
        auto.
        apply 垂直的左交换性.
        apply H0.
      Col.
    assert(Perp X1 Y2 A B).
      eapply 垂直的左交换性.
      assumption.
    induction(两点重合的决定性 X1 Y1).
      subst Y1.
      apply 等价共线CAB.
      apply cop_perp2__col with A B; Cop.
    assert(Perp X1 Y1 A B).
      eauto using 垂直的左交换性, 垂线共线点也构成垂直1 with col.
    assert (Col X1 X2 Y1).
      apply cop_perp2__col with A B; Perp; Cop.
    ColR.
Qed.

Lemma col_perp2_ncol__col : forall X1 X2 Y1 Y2 A B,
 Perp X1 X2 A B -> Perp Y1 Y2 A B ->
 Col X1 Y1 Y2 -> ~ Col X1 A B ->
 Col X2 Y1 Y2.
Proof.
    intros.
    assert (共面 A B X2 Y1).
      induction (两点重合的决定性 X1 Y1).
        subst; Cop.
      apply coplanar_trans_1 with X1; [Cop..|].
      assert (Perp Y1 X1 A B) by (apply 垂线共线点也构成垂直1 with Y2; Col); Cop.
    assert (共面 A B X2 Y2).
      induction (两点重合的决定性 X1 Y2).
        subst; Cop.
      apply coplanar_trans_1 with X1; [Cop..|].
      assert (Perp Y2 X1 A B) by (apply 垂线共线点也构成垂直1 with Y1; Perp; Col); Cop.
    apply col_cop2_perp2__col with X1 A B; assumption.
Qed.

Lemma l12_9 : forall A1 A2 B1 B2 C1 C2,
 共面 C1 C2 A1 B1 -> 共面 C1 C2 A1 B2 ->
 共面 C1 C2 A2 B1 -> 共面 C1 C2 A2 B2 ->
 Perp A1 A2 C1 C2 -> Perp B1 B2 C1 C2 ->
 Par A1 A2 B1 B2.
Proof.
    intros A1 A2 B1 B2 C1 C2.
    intros.
    unfold Par.
    unfold 严格平行.
    assert(A1 <> A2 /\ C1 <> C2) by (apply 垂直推出不重合;assumption).
    assert(B1 <> B2 /\ C1 <> C2) by (apply 垂直推出不重合;assumption).
    分离合取式.
    induction(共线的决定性 A1 B1 B2).
      right.
      repeat split; auto.
      apply col_cop2_perp2__col with A1 C1 C2; auto.
    (***********************************)
    left.
    split.
      induction (垂直推出不共线 C1 C2 A1 A2); Perp.
        apply coplanar_pseudo_trans with C1 C2 A1; Cop.
        apply coplanar_pseudo_trans with C1 C2 A2; Cop.
    intro.
    ex_and H10 AB.
    apply H9.
    induction(两点重合的决定性 AB A1).
      subst AB.
      assumption.
    assert(Perp A1 AB C1 C2) by (eauto using 垂线共线点也构成垂直1 with col).
    apply col_cop2_perp2__col with AB C1 C2; Perp.
Qed.

(** We show here that from the axioms of neutral geometry we can deduce the existence of a parallel line.
This is important because it shows that axioms of neutral geometry are inconsistent with
those of elliptic geometry, as elliptic geometry assumes that no parallel lines exist. *)
(** This corresponds to l12_10 in Tarski's book. *)

Lemma parallel_existence : forall A B P, A <> B ->
 exists C, exists D, C<>D /\ Par A B C D /\ Col P C D.
Proof.
    intros.
    induction(共线的决定性 A B P).
      exists A.
      exists B.
      repeat split.
        assumption.
        Par.
      Col.
    assert(exists P', Col A B P' /\ Perp A B P P').
      eapply l8_18_过一点垂线之垂点的存在性.
      assumption.
    ex_and H1 P'.
    assert(P <> P').
      intro.
      subst P'.
      contradiction.
    induction(两点重合的决定性 P' A).
      subst P'.
      assert(exists Q, Per Q P A /\ Cong Q P A B /\ OS A P Q B).
        eapply ex_四点成首末边等长双直角S形则对边等长.
          auto.
          assumption.
          apply ABB型共线.
        intro.
        apply H0.
        Col.
      ex_and H4 Q.
      exists P.
      exists Q.
      assert(P <> Q).
        intro.
        treat_equalities.
        intuition.
      repeat split.
        assumption.
        apply l12_9 with P A; Cop.
        apply 直角转L形垂直于 in H4.
          apply 垂直于转T形垂直 in H4.
          induction H4.
            apply 垂直推出不重合 in H4.
            分离合取式.
            absurde.
          apply 垂直的左交换性.
          assumption.
          auto.
        assumption.
      Col.
    assert(exists Q, Per Q P P' /\ Cong Q P A B /\ OS P' P Q A).
      eapply ex_四点成首末边等长双直角S形则对边等长.
        auto.
        assumption.
        Col.
      intro.
      apply H0.
      eapply (共线的传递性2 _ P').
        auto.
        Col.
      Col.
    ex_and H5 Q.
    exists P.
    exists Q.
    assert(P <> Q).
      intro.
      treat_equalities.
      intuition.
    repeat split.
      assumption.
      apply l12_9 with P P'.
        exists P; left; split; Col.
        Cop.
        exists P; left; split; Col.
        apply 等价共面ACDB, col_cop__cop with A; Col; Cop.
        apply H2.
      apply 直角转L形垂直于 in H5.
        apply 垂直于转T形垂直 in H5.
        induction H5.
          apply 垂直推出不重合 in H5.
          分离合取式.
          absurde.
        apply 垂直的左交换性.
        assumption.
        auto.
      assumption.
    Col.
Qed.

Lemma par_col_par : forall A B C D D',
 C <> D' -> Par A B C D -> Col C D D' -> Par A B C D'.
Proof.
    intros.
    unfold Par in *.
    induction H0.
      left.
      统计不重合点.
      unfold 严格平行 in *.
      分离合取式.
      split.
        apply col_cop__cop with D; auto.
      intro.
      apply H2.
      ex_and H8 P.
      exists P.
      split.
        assumption.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H.
        Col.
      Col.
    right.
    分离合取式.
    repeat split.
      assumption.
      assumption.
      apply 等价共线CAB.
      eapply 共线的传递性2.
        apply H2.
        assumption.
      Col.
    apply 等价共线CAB.
    eapply 共线的传递性2.
      apply H2.
      assumption.
    Col.
Qed.

Lemma parallel_existence1 : forall A B P, A <> B -> exists Q, Par A B P Q.
Proof.
    intros.
    assert (T:= parallel_existence A B P H).
    decompose [and ex] T;clear T.
    elim (两点重合的决定性 x P);intro.
      subst.
      exists x0.
      intuition.
    exists x.
    apply par_right_comm.
    apply par_col_par with x0; Par.
    Col.
Qed.

Lemma par_not_col : forall A B C D X, 严格平行 A B C D -> Col X A B -> ~Col X C D.
Proof.
    intros.
    unfold 严格平行 in H.
    intro.
    分离合取式.
    apply H2.
    exists X; Col.
Qed.

Lemma not_strict_par1 : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B C.
Proof.
    intros.
    unfold Par in H.
    induction H.
      unfold 严格平行 in H.
      分离合取式.
      assert(exists X, Col X A B /\ Col X C D).
        exists X.
        split; Col.
      contradiction.
    分离合取式.
    apply 等价共线BCA.
    eapply 共线的传递性2.
      apply H2.
      Col.
    Col.
Qed.

Lemma not_strict_par2 : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B D.
Proof.
    intros.
    eapply not_strict_par1.
      apply par_right_comm.
      apply H.
      apply H0.
    Col.
Qed.

Lemma not_strict_par : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B C /\ Col A B D.
Proof.
    intros.
    split.
      eapply not_strict_par1.
        apply H.
        apply H0.
      assumption.
    eapply not_strict_par2.
      apply H.
      apply H0.
    assumption.
Qed.

Lemma col2_par__col4 : forall A B C D X, Par A B C D -> Col A B X -> Col C D X ->
 Col A B C /\ Col A B D /\ Col A C D /\ Col B C D.
Proof.
    intros.
    destruct (not_strict_par A B C D X); trivial.
    apply par_symmetry in H.
    destruct (not_strict_par C D A B X); trivial.
    repeat split; Col.
Qed.

Lemma not_par_not_col : forall A B C, A <> B -> A <> C -> ~Par A B A C -> ~Col A B C.
Proof.
    intros.
    intro.
    apply H1.
    unfold Par.
    right.
    repeat split.
      assumption.
      assumption.
      apply AAB型共线.
    Col.
Qed.

Lemma not_par_inter_uniqueness : forall A B C D X Y,
  A <> B -> C <> D -> ~Par A B C D -> Col A B X -> Col C D X -> Col A B Y -> Col C D Y ->
  X = Y.
Proof.
    intros.
    induction(两点重合的决定性 C Y).
      subst Y.
      induction (两点重合的决定性 C X).
        subst X.
        reflexivity.
      apply (l6_21_两线交点的唯一性 C D A B); auto.
      intro.
      apply H1.
      unfold Par.
      right.
      repeat split; ColR.
    apply (l6_21_两线交点的唯一性 A B C D); auto.
    intro.
    apply H1.
    unfold Par.
    right.
    repeat split; ColR.
Qed.

Lemma inter_uniqueness_not_par : forall A B C D P,
  ~Col A B C -> Col A B P -> Col C D P -> ~Par A B C D.
Proof.
    intros.
    intro.
    unfold Par in H2.
    induction H2.
      unfold 严格平行 in H2.
      分离合取式.
      apply H3.
      exists P.
      Col5.
    分离合取式.
    apply H.
    ColR.
Qed.

Lemma col_not_col_not_par :
 forall A B C D,
 (exists P, Col A B P /\ Col C D P) ->
 (exists Q, Col C D Q /\ ~Col A B Q) -> ~Par A B C D.
Proof.
    intros.
    ex_and H P.
    ex_and H0 Q.
    intro.
    unfold Par in H3.
    induction H3.
      unfold 严格平行 in H3.
      分离合取式.
      apply H4.
      exists P.
      Col5.
    分离合取式.
    apply H2.
    eapply 共线的传递性4.
      apply H4.
      Col.
      Col.
    Col.
Qed.

Lemma par_distincts : forall A B C D,
 Par A B C D -> (Par A B C D /\ A <> B /\ C <> D).
Proof.
    intros.
    split.
      assumption.
    unfold Par in H.
    induction H.
      统计不重合点.
      split; assumption.
    分离合取式.
    split; assumption.
Qed.

Lemma par_not_col_strict : forall A B C D P,
 Par A B C D -> Col C D P -> ~Col A B P -> 严格平行 A B C D.
Proof.
    intros.
    induction H.
      assumption.
    分离合取式.
    exfalso.
    apply H1.
    apply (共线的传递性4 C D); Col.
Qed.

Lemma col_cop_perp2__pars : forall P Q A B C D, ~ Col A B P ->
    Col C D P -> 共面 A B C D -> Perp A B P Q -> Perp C D P Q -> 严格平行 A B C D.
Proof.
    intros.
    apply par_not_col_strict with P; trivial.
    统计不重合点.
    assert (共面 A B C P) by (apply col_cop__cop with D; Col).
    assert (共面 A B D P) by (apply col_cop__cop with C; Col; Cop).
    apply l12_9 with P Q; trivial; apply 等价共面ACBD.
      apply coplanar_trans_1 with B; Col; Cop.
      apply coplanar_trans_1 with B; Col; Cop.
      apply coplanar_trans_1 with A; Col; Cop.
      apply coplanar_trans_1 with A; Col; Cop.
Qed.

Lemma all_one_side_par_strict : forall A B C D,
 C <> D -> (forall P, Col C D P -> OS A B C P) ->
 严格平行 A B C D.
Proof.
    intros.
    split.
      apply os__coplanar, H0; Col.
    intro.
    ex_and H1 X.
    assert(HH:= H0 X (等价共线BCA _ _ _ H2) ).
    ex_and HH M.
    unfold TS in H4.
    分离合取式.
    contradiction.
Qed.

Lemma par_col_par_2 : forall A B C D P,
 A <> P -> Col A B P -> Par A B C D -> Par A P C D.
Proof.
    intros.
    apply par_symmetry.
    apply par_symmetry in H1.
    apply par_col_par with B; assumption.
Qed.


Lemma par_col2_par : forall A B C D E F,
 E <> F -> Par A B C D -> Col C D E -> Col C D F -> Par A B E F.
Proof.
    intros.
    induction (两点重合的决定性 C E).
      subst E.
      eapply par_col_par.
        assumption.
        apply H0.
      assumption.
    eapply par_col_par.
      assumption.
      apply par_right_comm.
      eapply par_col_par.
        apply H3.
        apply H0.
      assumption.
    apply 等价共线CAB.
    eapply 共线的传递性2.
      apply par_distincts in H0.
      分离合取式.
      apply H5.
      assumption.
    assumption.
Qed.

Lemma par_col2_par_bis : forall A B C D E F,
 E <> F -> Par A B C D -> Col E F C -> Col E F D -> Par A B E F.
Proof.
intros.
apply par_col2_par with C D; ColR.
Qed.

Lemma par_strict_col_par_strict : forall A B C D E,
 C <> E -> 严格平行 A B C D -> Col C D E ->
 严格平行 A B C E.
Proof.
    intros.
    assert(Par C E A B).
      eapply par_col_par_2.
        auto.
        apply H1.
      apply par_symmetry.
      left.
      assumption.
    induction H2.
      apply par_strict_symmetry.
      assumption.
    unfold 严格平行 in H0.
    分离合取式.
    apply False_ind.
    apply H6.
    exists C.
    split; Col.
Qed.

Lemma par_strict_col2_par_strict : forall A B C D E F,
 E <> F -> 严格平行 A B C D -> Col C D E -> Col C D F ->
 严格平行 A B E F.
Proof.
    intros.
    统计不重合点.
    unfold 严格平行 in *.
    分离合取式.
    split.
      apply col2_cop__cop with C D; assumption.
    intro.
    apply H3.
    ex_and H9 X.
    exists X.
    split.
      assumption.
    apply 等价共线CAB.
    apply (共线的传递性5 E F); Col.
Qed.

Lemma line_dec : forall B1 B2 C1 C2, (Col C1 B1 B2 /\ Col C2 B1 B2) \/ ~ (Col C1 B1 B2 /\ Col C2 B1 B2).
Proof.
    intros.
    induction (共线的决定性 C1 B1 B2); induction (共线的决定性 C2 B1 B2);tauto.
Qed.

Lemma par_distinct : forall A B C D, Par A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    induction H.
      apply par_strict_distinct in H; intuition.
    intuition.
Qed.

Lemma par_col4__par : forall A B C D E F G H, E <> F -> G <> H -> Par A B C D ->
 Col A B E -> Col A B F -> Col C D G -> Col C D H -> Par E F G H.
Proof.
    intros A B C D E F G H.
    intros.
    apply (par_col2_par _ _ C D); auto.
    apply par_symmetry.
    apply (par_col2_par _ _ A B); auto.
    apply par_symmetry; auto.
Qed.

Lemma par_strict_col4__par_strict : forall A B C D E F G H, E <> F -> G <> H ->
 严格平行 A B C D -> Col A B E -> Col A B F -> Col C D G -> Col C D H ->
 严格平行 E F G H.
Proof.
    intros A B C D E F G H.
    intros.
    apply (par_strict_col2_par_strict _ _ C D); auto.
    apply par_strict_symmetry.
    apply (par_strict_col2_par_strict _ _ A B); auto.
    apply par_strict_symmetry; auto.
Qed.

Lemma par_strict_one_side : forall A B C D P,
 严格平行 A B C D -> Col C D P -> OS A B C P.
Proof.
  intros A B C D P HPar HCol.
  destruct (两点重合的决定性 C P).
    subst P; apply par_strict_not_col_1 in HPar; apply one_side_reflexivity; Col.
  apply l12_6, par_strict_col_par_strict with D; trivial.
Qed.

Lemma par_strict_all_one_side : forall A B C D,
 严格平行 A B C D -> (forall P, Col C D P -> OS A B C P).
Proof.
    intros.
    eapply par_strict_one_side.
      apply H.
    assumption.
Qed.

Lemma inter_distincts : forall A B C D X, Inter A B C D X -> A <> B /\ C <> D.
Proof.
    intros.
    destruct H as [HAB [[P []] _]].
    统计不重合点.
    split; auto.
Qed.

Lemma inter_trivial : forall A B X, ~ Col A B X -> Inter A X B X X.
Proof.
    intros.
    统计不重合点.
    unfold Inter.
    repeat split; Col.
      exists B.
      split.
        Col.
      intro.
      apply H.
      Col.
Qed.

Lemma inter_sym : forall A B C D X, Inter A B C D X -> Inter C D A B X.
Proof.
    intros.
    unfold Inter in *.
    分离合取式.
    ex_and H0 P.
    assert(A <> B).
      intro.
      subst B.
      apply H3.
      Col.
    split.
      assumption.
    split.
      induction(两点重合的决定性 A X).
        treat_equalities.
        exists B.
        split.
          Col.
        intro.
        apply H3.
        eapply 共线的传递性4.
          apply H.
          Col.
          Col.
        Col.
      exists A.
      split.
        Col.
      intro.
      apply H3.
      assert(Col A P X).
        eapply 共线的传递性4.
          apply H.
          Col.
          Col.
        Col.
      ColR.
    split; Col.
Qed.

Lemma inter_left_comm : forall A B C D X, Inter A B C D X -> Inter B A C D X.
Proof.
    intros.
    unfold Inter in *.
    分离合取式.
    ex_and H0 P.
    split.
      assumption.
    split.
      exists P.
      split.
        assumption.
      intro.
      apply H3.
      Col.
    split; Col.
Qed.

Lemma inter_right_comm : forall A B C D X, Inter A B C D X -> Inter A B D C X.
Proof.
    intros.
    unfold Inter in *.
    分离合取式.
    ex_and H0 P.
    split.
      auto.
    split.
      exists P.
      split.
        Col.
      assumption.
    split; Col.
Qed.

Lemma inter_comm : forall A B C D X, Inter A B C D X -> Inter B A D C X.
Proof.
    intros.
    apply inter_left_comm.
    apply inter_right_comm.
    assumption.
Qed.

(** In the proof given by Tarski on page 125 the distinction of cases is explicit.
This is a good example on the significance of decidability. *)
Lemma l12_17 : forall A B C D P,
 A <> B -> 中点 P A C -> 中点 P B D -> Par A B C D.
Proof.
    intros.
    induction(共线的决定性 A B P).
      unfold Par.
      right.
      induction(两点重合的决定性 A P).
        subst P.
        apply A是AB中点则A与B重合 in H0.
        subst C.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
          apply AAB型共线.
        unfold 中点 in H1.
        分离合取式.
        apply 中间性蕴含共线1.
        assumption.
      induction(两点重合的决定性 B P).
        subst P.
        apply A是AB中点则A与B重合 in H1.
        subst D.
        repeat split.
          assumption.
          intro.
          subst C.
          apply M是AB中点则M是BA中点 in H0.
          apply A是AB中点则A与B重合 in H0.
          auto.
          unfold 中点 in H0.
          分离合取式.
          apply 中间性蕴含共线1 in H0 .
          Col.
        apply ABA型共线.
      assert(HH0 := H0).
      assert(HH1:= H1).
      unfold 中点 in H0.
      unfold 中点 in H1.
      分离合取式.
      apply 中间性蕴含共线1 in H1.
      apply 中间性蕴含共线1 in H0.
      assert(Col B C P).
        eapply 等价共线BCA.
        eapply (共线的传递性2 _ A).
          auto.
          Col.
        Col.
      assert(Col B C D).
        eapply (共线的传递性2 _ P).
          assumption.
          Col.
        Col.
      repeat split.
        assumption.
        intro.
        treat_equalities.
        intuition.
        induction(两点重合的决定性 A D).
          subst D.
          apply ABA型共线.
        assert(Col C D P).
          eapply (共线的传递性2 _ B).
            intro.
            subst C.
            assert(A = D).
              eapply 中点组的唯一性1.
                eapply M是AB中点则M是BA中点.
                apply HH0.
              assumption.
            contradiction.
            Col.
          Col.
        induction(两点重合的决定性 C P).
          treat_equalities.
          intuition.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ P).
          assumption.
          Col.
        Col.
      assumption.
    (* cas non degenere *)
    assert(exists E, Col A B E /\ Perp A B P E).
      eapply l8_18_过一点垂线之垂点的存在性.
      assumption.
    ex_and H3 E.
    assert(A <> P).
      intro.
      treat_equalities.
      apply H2.
      apply ABA型共线.
    induction(两点重合的决定性 A E).
      treat_equalities.
      assert(Per P A B).
        eapply L形垂直于转直角.
        apply 垂直于的交换性.
        eapply L形垂直转垂直于.
        apply 垂直的对称性.
        apply 垂直的交换性.
        assumption.
      prolong B A B' B A.
      prolong B' P D' B' P.
      assert(中点 C D D').
        eapply 对称保持中点.
          apply H1.
          apply H0.
          split.
            apply H8.
          Cong.
        split.
          assumption.
        Cong.
      assert(Per P A B').
        eapply 直角边共线点也构成直角2.
          apply H.
          assumption.
        apply 中间性蕴含共线1 in H6.
        Col.
      ex_and H3 B''.
      assert(B' = B'').
        eapply 中点组的唯一性1.
          split.
            apply H6.
          Cong.
        assumption.
      subst B''.
      assert(Cong P D P D').
        apply  (等长的传递性 _ _ B P).
          unfold 中点 in H1.
          分离合取式.
          Cong.
        apply  (等长的传递性 _ _ B' P).
          Cong.
        Cong.
      assert(Per P C D).
        unfold Per.
        exists D'.
        split; assumption.
      apply 直角转L形垂直于 in H14.
        apply 垂直于转T形垂直 in H14.
        induction H14.
          apply 垂直推出不重合 in H14.
          intuition.
        apply l12_9 with P A; Cop.
        apply 垂直的对称性.
        eapply 垂线共线点也构成垂直1.
          auto.
          apply H14.
        unfold 中点 in H0.
        分离合取式.
        apply 中间性蕴含共线1 in H0.
        Col.
        intro.
        treat_equalities.
        auto.
      intro.
      subst D.
      assert(C = D').
        apply A是AB中点则A与B重合.
        assumption.
      subst D'.
      assert(A = B).
        eapply 中点组的唯一性1.
          apply M是AB中点则M是BA中点.
          apply H0.
        apply M是AB中点则M是BA中点.
        assumption.
      auto.
    prolong E P F E P.
    assert(Col C D F).
      apply (mid_preserves_col A B E P); trivial.
      split.
        assumption.
      Cong.
    prolong A E A' A E.
    prolong A' P C' A' P.
    assert(中点 F C C').
      eapply 对称保持中点.
        apply H0.
        split.
          apply H7.
        Cong.
        split.
          apply H12.
        Cong.
      split.
        assumption.
      Cong.
    assert(Per P E A).
      eapply L形垂直于转直角.
      apply 垂直于的交换性.
      apply L形垂直转垂直于.
      apply 垂直的对称性.
      eapply 垂线共线点也构成垂直1.
        assumption.
        apply 垂直的右交换性.
        apply H4.
      Col.
    assert(Cong P C P C').
      eapply (等长的传递性 _ _ P A).
        unfold 中点 in H0.
        分离合取式.
        Cong.
      eapply (等长的传递性 _ _ P A').
        unfold Per in H15.
        ex_and H15 A''.
        assert( A' = A'').
          eapply 中点组的唯一性1.
            split.
              apply H10.
            Cong.
          assumption.
        subst A''.
        assumption.
      Cong.
    assert(Per P F C).
      unfold Per.
      exists C'.
      split.
        assumption.
      assumption.
    apply 直角转L形垂直于 in H17.
      apply 垂直于的交换性 in H17.
      apply 垂直于转T形垂直 in H17.
      induction H17.
        apply l12_9 with P E.
          exists P; left; split; Col.
          exists B; right; right; split; Col.
          exists A; right; right; split; Col.
          exists P; left; split; Col.
          apply H4.
        eapply 垂线共线点也构成垂直1.
          intro.
          subst D.
          assert (A = B).
            eapply 中点组的唯一性1.
              apply M是AB中点则M是BA中点.
              apply H0.
            apply M是AB中点则M是BA中点.
            assumption.
          auto.
          apply 垂直的对称性.
          eapply 垂线共线点也构成垂直1.
            intro.
            treat_equalities.
            apply 垂直推出不重合 in H17.
            分离合取式.
            auto.
            apply 垂直的左交换性.
            apply H17.
          apply 中间性蕴含共线1 in H7.
          Col.
        Col.
      apply 垂直推出不重合 in H17.
      分离合取式.
      tauto.
      intro.
      treat_equalities.
      apply 垂直推出不重合 in H4.
      分离合取式.
      tauto.
    intro.
    subst C.
    assert(F = C').
      apply A是AB中点则A与B重合 .
      assumption.
    treat_equalities.
    assert(A = E).
      eapply 中点组的唯一性1.
        apply M是AB中点则M是BA中点.
        apply H0.
      split.
        apply 中间性的对称性.
        assumption.
      Cong.
    tauto.
Qed.

Lemma l12_18_a :
  forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par A B C D.
Proof.
    intros.
    assert(中点 P A C /\ 中点 P B D) by (apply 四点对边等长则对角线交点平分对角线; assumption).
    分离合取式.
    eapply l12_17.
      intro.
      subst B.
      apply H1.
      apply AAB型共线.
      apply H5.
    apply H6.
Qed.

Lemma l12_18_b :
  forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par B C D A.
Proof.
    intros.
    assert(中点 P A C /\ 中点 P B D) by (apply 四点对边等长则对角线交点平分对角线; assumption).
    eapply l12_18_a.
      assumption.
      Cong.
      intro.
      apply H1.
      assert(Col B C P).
        eapply 共线的传递性2.
          apply H2.
          Col.
        Col.
      apply 等价共线BCA.
      eapply (共线的传递性2 _ P).
        intro.
        subst P.
        分离合取式.
        apply M是AB中点则M是BA中点 in H5.
        apply A是AB中点则A与B重合 in H5.
        subst C.
        apply H1.
        apply ABA型共线.
        Col.
      Col.
      intro.
      subst C.
      apply H1.
      apply ABA型共线.
      apply H4.
    Col.
Qed.

Lemma l12_18_c :
 forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  TS B D A C.
Proof.
    intros.
    assert(中点 P A C /\ 中点 P B D) by (apply 四点对边等长则对角线交点平分对角线; assumption).
    unfold TS.
    repeat split.
      intro.
      apply H1.
      assert(Col A B P).
        apply 等价共线CAB.
        eapply (共线的传递性2 _ D).
          assumption.
          Col.
        Col.
      eapply (共线的传递性2 _ P).
        intro.
        subst P.
        分离合取式.
        apply A是AB中点则A与B重合 in H5.
        subst C.
        apply H1.
        apply ABA型共线.
        Col.
      Col.
      intro.
      apply H1.
      assert(Col B P C).
        eapply (共线的传递性2 _ D).
          assumption.
          Col.
        Col.
      apply 等价共线BCA.
      eapply (共线的传递性2 _ P).
        intro.
        subst P.
        分离合取式.
        apply M是AB中点则M是BA中点 in H5.
        apply A是AB中点则A与B重合 in H5.
        subst C.
        apply H1.
        apply ABA型共线.
        Col.
      Col.
    exists P.
    split.
      Col.
    分离合取式.
    unfold 中点 in H5.
    tauto.
Qed.

Lemma l12_18_d :
 forall A B C D P,
 Cong A B C D -> Cong B C D A -> ~Col A B C ->
 B <> D -> Col A P C -> Col B P D ->
 TS A C B D.
Proof.
    intros.
    assert(中点 P A C /\ 中点 P B D) by (apply 四点对边等长则对角线交点平分对角线; assumption).
    eapply (l12_18_c _ _ _ _ P).
      Cong.
      Cong.
      intro.
      apply H1.
      assert(Col A B P).
        eapply 等价共线CAB.
        eapply 共线的传递性2.
          apply H2.
          Col.
        Col.
      eapply (共线的传递性2 _ P).
        intro.
        subst P.
        分离合取式.
        apply A是AB中点则A与B重合 in H5.
        subst C.
        contradiction.
        Col.
      Col.
      intro.
      subst C.
      apply H1.
      apply ABA型共线.
      Col.
    Col.
Qed.

Lemma l12_18 :
 forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par A B C D /\ Par B C D A /\ TS B D A C /\ TS A C B D.
Proof.
    intros.
    split.
      apply (l12_18_a _ _ _ _ P); assumption.
    split.
      apply (l12_18_b _ _ _ _ P); assumption.
    split.
      apply (l12_18_c _ _ _ _ P); assumption.
    apply (l12_18_d _ _ _ _ P); assumption.
Qed.

Lemma par_two_sides_two_sides :
  forall A B C D,
  Par A B C D -> TS B D A C ->
  TS A C B D.
Proof.
    intros.
    apply par_distincts in H.
    分离合取式.
    unfold Par in H.
    induction H.
      统计不重合点.
      unfold TS in *.
      分离合取式.
      ex_and H6 T.
      repeat split.
        intro.
        assert(Col T B C).
          apply 等价共线BCA.
          apply (共线的传递性2 _ A); Col.
        apply H3.
        apply 等价共线CAB.
        eapply (共线的传递性2 _ T).
          intro.
          treat_equalities.
          apply par_strict_not_col_1 in H.
          Col.
          Col.
          Col.
        intro.
        assert(Col T C D).
          apply 等价共线CAB.
          apply (共线的传递性2 _ A); Col.
        apply H3.
        apply 等价共线BCA.
        apply (共线的传递性2 _ T).
          intro.
          treat_equalities.
          apply par_strict_not_col_3 in H.
          Col.
          Col.
          Col.
      exists T.
      split.
        apply 中间性蕴含共线1 in H8.
        Col.
      induction H6.
        assert(HH:= outer_pasch C D T A B (中间性的对称性 _ _ _ H8) (中间性的对称性 _ _ _ H6)).
        ex_and HH X.
        unfold 严格平行 in H.
        分离合取式.
        apply False_ind.
        apply H12.
        exists X.
        split; Col.
      induction H6.
        assert(HH:= outer_pasch A B T C D H8 H6).
        ex_and HH X.
        apply False_ind.
        unfold 严格平行 in H.
        分离合取式.
        apply H12.
        exists X.
        split; Col.
      apply 中间性的对称性.
      assumption.
    unfold TS in H0.
    分离合取式.
    apply False_ind.
    apply H3.
    Col.
Qed.

Lemma par_one_or_two_sides :
 forall A B C D,
  严格平行 A B C D ->
 TS A C B D /\ TS B D A C \/ OS A C B D /\ OS B D A C.
Proof.
    intros.
    induction(two_sides_dec A C B D).
      left.
      split.
        assumption.
      apply par_two_sides_two_sides.
        apply par_comm.
        unfold Par.
        left.
        assumption.
      assumption.
    right.
    assert(HH:=H).
    unfold 严格平行 in H.
    分离合取式.
    split.
      apply cop_nts__os; Cop.
        intro.
        apply H1.
        exists C.
        split; Col.
        intro.
        apply H1.
        exists A.
        split; Col.
    apply cop_nts__os; Cop.
      intro.
      apply H1.
      exists D.
      split; Col.
      intro.
      apply H1.
      exists B.
      split; Col.
    intro.
    apply H0.
    apply par_two_sides_two_sides.
      left.
      assumption.
    assumption.
Qed.

Lemma l12_21_b : forall A B C D,
 TS A C B D ->
 等角 B A C D C A -> Par A B C D.
Proof.
    intros.
    apply conga_distinct in H0.
    分离合取式.
    assert(~Col A B C).
      intro.
      unfold TS in H.
      分离合取式.
      apply 等价共线BAC in H5.
      assert(Col D C A).
        eapply 共线三点构成的角的等角三点也共线.
          apply H5.
        assumption.
      contradiction.
    assert(A <> B /\ C <> D).
      auto.
    分离合取式.
    assert(HH:=由一点往一方向构造等长线段_3 C D A B H7 H6).
    ex_and HH D'.
    assert(等角 B A C D' C A).
      eapply l11_10.
        apply H0.
        apply out_trivial.
        assumption.
        apply out_trivial.
        assumption.
        apply l6_6.
        assumption.
      apply out_trivial.
      assumption.
    assert(Cong D' A B C).
      eapply 等角两边等长则端点间距相等.
        apply 等角的对称性.
        apply H10.
        Cong.
      Cong.
    assert(TS A C D' B).
      eapply l9_5.
        apply l9_2.
        apply H.
        apply ABA型共线.
      assumption.
    unfold TS in H12.
    分离合取式.
    ex_and H14 M.
    assert(B <> D').
      intro.
      treat_equalities.
      contradiction.
    assert(中点 M A C /\ 中点 M B D').
      apply 四点对边等长则对角线交点平分对角线.
        assumption.
        assumption.
        Cong.
        Cong.
        Col.
      apply 中间性蕴含共线1 in H15.
      Col.
    分离合取式.
    assert(Par A B C D').
      eapply l12_17.
        assumption.
        apply H17.
      assumption.
    eapply par_col_par.
      auto.
      apply H19.
    apply out_col in H8.
    Col.
Qed.

Lemma l12_22_aux :
 forall A B C D P,
  P <> A -> A <> C -> Bet P A C -> OS P A B D ->
  等角 B A P D C P ->
  Par A B C D.
Proof.
    intros.
    assert (P<>C) by (intro; treat_equalities; auto).
    prolong B A B' B A .
    分离合取式.
    assert(等角 P A B C A B').
      apply l11_14.
        assumption.
        assumption.
        auto.
        assumption.
        unfold 等角 in H3.
        分离合取式.
        auto.
        intro.
        treat_equalities.
        unfold 等角 in H3.
        tauto.
    assert(等角 D C A D C P).
      apply out2__conga.
        apply out_trivial.
        unfold 等角 in H3.
        tauto.
      apply 中间性的对称性 in H1.
      apply bet_out in H1.
        apply l6_6.
        assumption.
      auto.
    assert(Par A B' C D).
      eapply l12_21_b.
        assert(~Col B P A).
          unfold OS in H2.
          ex_and H2 T.
          unfold TS in H2.
          tauto.
        assert(TS P A B B').
          unfold TS.
          repeat split.
            assumption.
            intro.
            apply H9.
            apply 等价共线BCA.
            eapply (共线的传递性2 _ B').
              intro.
              treat_equalities.
              unfold 等角 in H3.
              tauto.
              apply 中间性蕴含共线1 in H1.
              Col.
            Col.
          exists A.
          split.
            Col.
          assumption.
        apply l9_2.
        apply l9_8_2 with B.
          apply col_two_sides with P.
            apply 中间性蕴含共线1 in H1.
            Col.
            assumption.
          apply invert_two_sides.
          apply H10.
        apply col_one_side with P.
          apply 中间性蕴含共线1 in H1.
          Col.
          auto.
        apply invert_one_side.
        apply H2.
      eapply 角等的传递性.
        apply 等角的对称性.
        apply 等角的交换性.
        apply H7.
      eapply 角等的传递性.
        apply H3.
      apply 等角的对称性.
      assumption.
    apply par_symmetry.
    apply par_col_par with B'.
      unfold 等角 in H3.
      分离合取式.
      auto.
      apply par_symmetry.
      apply H9.
    apply 中间性蕴含共线1 in H1.
    Col.
Qed.


Lemma l12_22_b :
 forall A B C D P,
  Out P A C -> OS P A B D -> 等角 B A P D C P ->
  Par A B C D.
Proof.
    intros.
    induction(两点重合的决定性 A C).
      subst C.
      unfold Par.
      right.
      repeat split.
        unfold 等角 in H1.
        分离合取式.
        auto.
        unfold 等角 in H1.
        分离合取式.
        auto.
        Col.
      apply 等角的交换性 in H1.
      apply conga_os__out in H1; Col.
    unfold Out in H.
    分离合取式.
    induction H4.
      apply l12_22_aux with P; auto.
    apply par_symmetry.
    apply l12_22_aux with P; auto.
      apply (col_one_side _ A).
        apply 中间性蕴含共线1 in H4.
        Col.
        auto.
      apply one_side_symmetry.
      assumption.
    apply 等角的对称性.
    assumption.
Qed.

Lemma par_strict_par : forall A B C D,
 严格平行 A B C D -> Par A B C D.
Proof.
    intros.
    unfold Par.
    tauto.
Qed.

Lemma col_par : forall A B C,
 A <> B -> B <> C ->
 Col A B C -> Par A B B C.
Proof.
    intros.
    unfold Par.
    right.
    intuition Col.
Qed.

Lemma acute_col_perp__out : forall A B C A',
  为锐角 A B C -> Col B C A' -> Perp B C A A' -> Out B A' C.
Proof.
  intros A B C A' HacuteB HBCA' HPerp.
  assert(HUn := 垂直推出不共线 B C A A' HPerp).
  destruct HUn as [HNCol1|]; [|contradiction].
  assert(HB' := l10_15 B C B A).
  destruct HB' as [B' []]; Col.
  统计不重合点.
  assert(HNCol2 : ~ Col B' B C ) by (apply 成直角三点不共线; Perp).
  assert(HNCol3 : ~ Col B B' A).
  { intro.
    apply (一角不可能小于自己 A B C).
    apply acute_per__lta; auto.
    apply (l8_3_直角边共线点也构成直角1 B'); Col; Perp.
  }
  assert(HPars : 严格平行 B B' A A').
    apply (par_not_col_strict _ _ _ _ A); Col; apply (l12_9 _ _ _ _ B C); Perp; Cop.
  assert(HNCol4 := par_strict_not_col_4 B B' A A' HPars).
  apply (col_one_side_out _ B'); Col.
  apply (one_side_transitivity _ _ _ A).
    apply l12_6; Par.
  apply invert_one_side.
  apply 角内点和一端点在角另一边同侧; Col.
  apply l11_24_在角内的对称性.
  apply lea_in_angle; Side.
  apply 角度小于的交换性.
  apply acute_per__lta; Perp.
Qed.

Lemma acute_col_perp__out_1 : forall A B C A',
  为锐角 A B C -> Col B C A' -> Perp B A A A' -> Out B A' C.
Proof.
  intros A B C A' H为锐角 HCol HPerp.
  destruct (由一点往一方向构造等长线段 A B A B) as [A0 [HA1 HA2]].
  destruct (由一点往一方向构造等长线段 C B C B) as [C0 [HC1 HC2]].
  统计不重合点.
  assert (HNCol : ~ Col B A A') by (apply 成直角三点不共线; Perp).
  统计不重合点.
  apply l6_2 with C0; auto.
  apply not_out_bet.
    ColR.
  intro.
  apply (not_bet_and_out A B A0); split; trivial.
  apply acute_col_perp__out with A'; Col.
    apply 为锐角的对称性, (acute_conga__acute A B C); auto.
    apply l11_14; auto.
    apply 中间性的对称性, l6_2 with C0; Between.
    apply l6_6; assumption.
  apply 垂线共线点也构成垂直1 with A; Col; Perp.
Qed.

Lemma conga_cop_inangle_per2__inangle : forall A B C P T,
  Per A B C -> 在角内 T A B C -> 等角 P B A P B C -> Per B P T -> 共面 A B C P ->
  在角内 P A B C.
Proof.
  intros A B C P T HPer HInangle HConga HPerP HCop.
  destruct (两点重合的决定性 P T).
    subst; apply HInangle.
  统计不重合点.
  destruct (angle_bisector A B C) as [P' [HInangle' HConga']]; auto.
  统计不重合点.
  assert (H为锐角 : 为锐角 P' B A).
    apply 为锐角的对称性, conga_inangle_per__acute with C; trivial.
  apply l11_25 with P' A C; try (apply out_trivial); auto.
  assert (HNCol1 : ~ Col A B C) by (apply 成直角三点不共线; auto).
  assert (HCol : Col B P P').
    apply conga2_cop2__col with A C; trivial.
    intro; apply HNCol1; Col.
    apply coplanar_trans_1 with C; Cop; Col.
    apply coplanar_trans_1 with A; Cop.
  apply (acute_col_perp__out T); Col.
  { apply 小于等于锐角之角为锐角 with P' B A; trivial.
    assert (HNCol2 : ~ Col P' B A).
      intro.
      assert (Col P' B C) by (apply (共线三点构成的角的等角三点也共线 P' B A); assumption).
      apply HNCol1; ColR.
    assert (共面 A B T P') by (apply coplanar_trans_1 with C; Cop; Col).
    destruct (共线的决定性 T B P'); [|统计不重合点; destruct (cop__one_or_two_sides B P' A T); Col; Cop].
    - apply l11_31_1_任何角小于等于平角_Out表述; auto.
      apply col_one_side_out with A; Col.
      apply invert_one_side, 角内两点在角一边同侧 with C; Col.
      assert (~ Col B P T) by (apply 成直角三点不共线; auto).
      intro; 统计不重合点; apply HNCol2; ColR.
    - apply (l11_30_等角保持小于等于 P' B T P' B C); 等角.
      apply 角内点分角小于等于大角1, (在角内的传递性2 A); trivial.
      apply os_ts__inangle; trivial.
      apply invert_one_side, 角内两点在角一边同侧 with C; Col.
      intro; apply HNCol1, 中间性蕴含共线1, 角一边反向延长线上点在角内则该角为平角 with T; trivial.
      apply col_two_sides_bet with P'; Col.
    - apply 角度小于等于的左交换性, 角内点分角小于等于大角1.
      destruct (共线的决定性 B A T).
        apply out341__inangle; auto.
        apply col_one_side_out with P'; assumption.
      apply os2__inangle; trivial.
      apply invert_one_side, 角内两点在角一边同侧 with C; Col.
  }
  apply 垂线共线点也构成垂直1 with P; Col.
  apply 垂直的右交换性, 直角转L形垂直; auto.
Qed.

End T12_2'.

Hint Resolve col_par par_strict_par : par.

Hint Resolve l12_6 pars__os3412 : side.

(*
Ltac finish := repeat match goal with
 | |- Bet ?A ?B ?C => Between
 | |- Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => Col
 | |- Par ?A ?B ?C ?D => Par
 | |- 严格平行 ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- 垂直于 ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => Cong
 | |- 中点 ?A ?B ?C => 中点
 | |- ?A<>?B => apply 不重合的对称性;assumption
 | |- _ => try assumption
end.
*)

Section T12_3.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma perp_not_par : forall A B X Y, Perp A B X Y -> ~ Par A B X Y.
Proof.
    intros.
    assert(HH:=H).
    unfold Perp in HH.
    ex_and HH P.
    intro.
    induction H1.
      apply H1.
      exists P.
      apply 垂点是交点 in H0.
      分离合取式.
      split; Col.
    分离合取式.
    induction(两点重合的决定性 A Y).
      subst Y.
      assert(P = A).
        eapply (l8_14_2_1b_垂点是交点 P A B X A); Col.
      subst P.
      apply 垂直于的交换性 in H0.
      apply L形垂直于转直角 in H0.
      assert(~ Col B A X).
        eapply(成直角三点不共线).
          auto.
          auto.
        assumption.
      apply H5.
      Col.
    apply(l8_16_1_共线四点和一垂直推另一直角 A B X A Y); Col.
      ColR.
    ColR.
Qed.

Lemma cong_conga_perp : forall A B C P, TS B P A C -> Cong A B C B -> 等角 A B P C B P -> Perp A C B P.
Proof.
    intros.
    assert(HH:=H).
    unfold TS in HH.
    assert (~ Col A B P).
      分离合取式.
      assumption.
    分离合取式.
    ex_and H5 T.
    assert(B <> P).
      intro.
      subst P.
      apply H3.
      Col.
    assert(A <> B).
      intro.
      subst B.
      apply H3.
      Col.
    assert(C <> B).
      intro.
      subst C.
      apply H4.
      Col.
    assert(A <> C).
      intro.
      subst C.
      assert(OS B P A A).
        apply one_side_reflexivity.
        assumption.
      apply l9_9 in H.
      contradiction.
    induction (中间性的决定性 A B C).
      assert(Per P B A).
        apply(l11_18_2 P B A C); auto.
        apply 等角的交换性.
        assumption.
      eapply (直角加共线转L形垂直 _ _ _ C) in H12; auto.
        apply 垂直的右交换性.
        assumption.
      apply 中间性蕴含共线1 in H11.
      Col.
    assert(B <> T).
      intro.
      subst T.
      contradiction.
    assert(等角 T B A T B C).
      induction H5.
        eapply (l11_13 P _ _ P); Between.
        apply 等角的交换性.
        apply H1.
      assert(Out B P T).
        repeat split; auto.
        induction H5.
          left.
          Between.
        right.
        Between.
      apply 等角的交换性.
      apply (l11_10 A _ P C _ P); try (apply out_trivial); auto; apply l6_6; assumption.
    assert(Cong T A T C).
      apply (等角两边等长则端点间距相等 T B A T B C); Cong.
    assert(中点 T A C).
      split; Cong.
    assert(Per B T A).
      unfold Per.
      exists C.
      split; Cong.
    eapply (直角加共线转L形垂直 _ _ _ C) in H16; auto.
      apply 垂直的对称性.
      apply (垂线共线点也构成垂直1 _ T); Col.
      Perp.
      intro.
      subst T.
      apply A是AB中点则A与B重合 in H15.
      contradiction.
      intro.
      subst T.
      apply M是AB中点则M是BA中点 in H15.
      apply A是AB中点则A与B重合 in H15.
      apply H10.
      auto.
    apply 中间性蕴含共线1 in H6.
    Col.
Qed.

Lemma perp_inter_exists : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P.
Proof.
    intros A B C D HPerp.
    destruct HPerp as [P [_ [_ [HCol1 [HCol2]]]]].
    exists P; split; Col.
Qed.

Lemma perp_inter_perp_in : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P /\ 垂直于 P A B C D.
Proof.
    intros.
    assert(HH:=perp_inter_exists A B C D H).
    ex_and HH P.
    exists P.
    split.
      Col.
    split.
      Col.
    apply l8_14_2_1b_bis_交点是垂点; Col.
Qed.

End T12_3.

Section T12_2D.

Context `{T2D:Tarski_2D}.

Lemma l12_9_2D : forall A1 A2 B1 B2 C1 C2,
  Perp A1 A2 C1 C2 -> Perp B1 B2 C1 C2 -> Par A1 A2 B1 B2.
Proof.
  intros A1 A2 B1 B2 C1 C2.
  apply l12_9; apply all_coplanar.
Qed.

End T12_2D.