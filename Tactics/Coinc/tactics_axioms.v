Require Export GeoCoq.Utils.arity.

(** Minimal set of lemmas needed to use the ColR tactic. *)
Class Col_theory (COLTpoint : Type) (CTCol: COLTpoint -> COLTpoint -> COLTpoint -> Prop) :=
{
  CTcol_trivial : forall A B : COLTpoint, CTCol A A B;
  CT等价共线BCA : forall A B C : COLTpoint, CTCol A B C -> CTCol B C A;
  CT等价共线CAB : forall A B C : COLTpoint, CTCol A B C -> CTCol A C B;
  CT共线的传递性4 : forall X Y A B C : COLTpoint,
             X <> Y -> CTCol X Y A -> CTCol X Y B -> CTCol X Y C -> CTCol A B C
}.

Class Arity :=
{
  COINCpoint : Type;
  n : nat
}.

Class Coinc_predicates (Ar : Arity) :=
{
  wd : arity COINCpoint (S (S n));
  coinc : arity COINCpoint (S (S (S n)))
}.

(** Minimal set of lemmas needed to use the Coinc tactic. *)
Class Coinc_theory (Ar : Arity) (COP : Coinc_predicates Ar) :=
{
  wd_perm_1 : forall A : COINCpoint,
              forall X : cartesianPower COINCpoint (S n),
                app_1_n wd A X -> app_n_1 wd X A;
  wd_perm_2 : forall A B : COINCpoint,
              forall X : cartesianPower COINCpoint n,
                app_2_n wd A B X -> app_2_n wd B A X;
  coinc_perm_1 : forall A : COINCpoint,
                 forall X : cartesianPower COINCpoint (S (S n)),
                   app_1_n coinc A X -> app_n_1 coinc X A;
  coinc_perm_2 : forall A B : COINCpoint,
                 forall X : cartesianPower COINCpoint (S n),
                   app_2_n coinc A B X -> app_2_n coinc B A X;
  coinc_bd : forall A : COINCpoint,
             forall X : cartesianPower COINCpoint (S n),
              app_2_n coinc A A X;
  coinc_n : forall COINC : cartesianPower COINCpoint (S (S (S n))),
            forall WD : cartesianPower COINCpoint (S (S n)),
              pred_conj coinc COINC WD ->
              app wd WD ->
              app coinc COINC
}.

(** Minimal set of lemmas needed to use the CongR tactic *)
Class Cong_theory (CONGpoint : Type)
  (CTCong: CONGpoint -> CONGpoint -> CONGpoint -> CONGpoint -> Prop) :=
{
  CTcong_refl : forall A B : CONGpoint, CTCong A B A B;
  CTcong_left_comm : forall A B C D : CONGpoint, CTCong A B C D -> CTCong B A C D;
  CTcong_sym : forall A B C D : CONGpoint, CTCong A B C D -> CTCong C D A B;
  CTcong_trans : forall A B C D E F : CONGpoint,
                          CTCong A B C D -> CTCong C D E F -> CTCong A B E F
}.