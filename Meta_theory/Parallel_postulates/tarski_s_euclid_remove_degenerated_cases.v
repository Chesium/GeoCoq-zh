Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch06_out_lines.

Section tarski_s_euclid_remove_degenerated_cases.

Context `{TnEQD:无维度中性塔斯基公理系统_带两点重合决定性}.

Lemma tarski_s_euclid_remove_degenerated_cases :
  (forall A B C D T,
   A <> B ->
   A <> C ->
   A <> D ->
   A <> T ->
   B <> C ->
   B <> D ->
   B <> T ->
   C <> D ->
   C <> T ->
   D <> T ->
   ~ Col A B C ->
   Bet A D T ->
   Bet B D C ->
   ~ Col B C T ->
   exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y) ->
  forall A B C D T,
  Bet A D T ->
  Bet B D C ->
  A <> D -> exists x y : Tpoint, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intro HGC; intros A B C D T HADT HBDC HAD.
elim (两点重合的决定性 A B); intro HAB.
subst; exists T; exists C; Between.
elim (两点重合的决定性 A C); intro HAC.
subst; exists B; exists T; Between.
elim (两点重合的决定性 A T); intro HAT.
exfalso; apply HAD; treat_equalities; reflexivity.
elim (两点重合的决定性 B C); intro HBC.
treat_equalities; exists T; exists T; Between.
elim (两点重合的决定性 B D); intro HBD.
subst; exists T; exists C; Between.
elim (两点重合的决定性 B T); intro HBT.
subst; exists T; exists C; Between.
elim (两点重合的决定性 C D); intro HCD.
subst; exists B; exists T; Between.
elim (两点重合的决定性 C T); intro HCT.
subst; exists B; exists T; Between.
elim (两点重合的决定性 D T); intro HDT.
subst; exists B; exists C; Between.
elim (共线的决定性 A B C); intro HABC.

  {
  elim HABC; clear HABC; intro HABC.

    {
    assert (H : Bet A B D) by eBetween; assert (Bet A B T) by eBetween.
    exists T; exists C; Between.
    }

    {
    elim HABC; clear HABC; intro HABC.

      {
      assert (H : Bet A C D) by eBetween; assert (Bet A C T) by eBetween.
      exists B; exists T; Between.
      }

      {
      assert (H : Bet B A D \/ Bet B D A) by (apply l5_3 with C; Between).
      elim H; clear H; intro H.

        {
        assert (H' : Bet A C T \/ Bet A T C) by (apply l5_2 with B; eBetween).
        elim H'; clear H'; intro H'.

          {
          exists B; exists T; Between.
          }

          {
          exists B; exists C; repeat split; Between; eBetween.
          }
        }
        {
        assert (H' : Bet A B T \/ Bet A T B) by (apply l5_1 with D; Between).
        elim H'; clear H'; intro H'.

          {
          exists T; exists C; Between.
          }

          {
          exists B; exists C; repeat split; Between; eBetween.
          }
        }
      }
    }
  }
  {
  assert (~ Col B C T) by (intro; apply HABC, 等价共线CAB, (共线的传递性5 D T); Col).
  apply HGC with D; assumption.
  }
Qed.

End tarski_s_euclid_remove_degenerated_cases.