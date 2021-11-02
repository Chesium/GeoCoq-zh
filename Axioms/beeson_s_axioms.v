(** We describe here an intuitionistic version of Tarski's axiom system proposed
by Michael Beeson. *)
(* 仅仅用于与 Tarski 公理系统互转 *)
Class intuitionistic_无维度中性塔斯基公理系统 := {
 ITpoint : Type;
 IBet : ITpoint -> ITpoint -> ITpoint -> Prop;
 ICong : ITpoint -> ITpoint -> ITpoint -> ITpoint -> Prop;
 Cong_stability : forall A B C D, ~ ~ ICong A B C D -> ICong A B C D;
 Bet_stability : forall A B C, ~ ~ IBet A B C -> IBet A B C;
 IT A B C := ~ (A<>B /\ B<>C /\ ~ IBet A B C);
 ICol A B C :=  ~ (~ IT C A B /\ ~ IT A C B /\ ~ IT A B C);
 I等长的同一性 : forall A B C, ICong A B C C -> A = B;
 I等长的内传递性 : forall A B C D E F,
   ICong A B C D -> ICong A B E F -> ICong C D E F;
 I等长的伪自反性 : forall A B, ICong A B B A;
 I由一点往一方向构造等长线段 : forall A B C D,
    A<>B -> exists E, IT A B E /\ ICong B E C D;
 I五线段公理_等价SAS  : forall A A' B B' C C' D D',
    ICong A B A' B' ->
    ICong B C B' C' ->
    ICong A D A' D' ->
    ICong B D B' D' ->
    IT A B C -> IT A' B' C' -> A <> B -> ICong C D C' D';
 I中间性的同一律 : forall A B, ~ IBet A B A;
 I中间性的对称性 : forall A B C, IBet A B C -> IBet C B A;
 I中间性的内传递性1 : forall A B C D, IBet A B D -> IBet B C D -> IBet A B C;
 I帕施公理 : forall A B C P Q,
   IBet A P C -> IBet B Q C -> ~ ICol A B C ->
   exists x, IBet P x B /\ IBet Q x A;
 PA : ITpoint;
 PB : ITpoint;
 PC : ITpoint;
 I防降维公理 : ~ IT PC PA PB /\ ~ IT PA PC PB /\ ~ IT PA PB PC
}.
