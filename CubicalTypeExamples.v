Require Import HoTT.
Require Import CubicalType.


      

(* examples *)

(* true < false *)
Inductive strictly_less : s1_bound Bool -> Type :=
  | falsetrue : strictly_less (false, true).

Definition interval_CT1 : CT1 :=
  ( Bool ; strictly_less ).


Inductive pathsu {V : Type} : s1_bound V -> Type :=
  | idp {v : V} : pathsu (v , v).

Definition singular_CT1 (V : Type) : CT1 := (V ; pathsu).

Inductive squares {V : Type} : s2_bound (singular_CT1 V) -> Type :=
  | ids {v : V} : squares (@S2b (singular_CT1 V) v v v v idp idp idp idp).  
  (* for some reason we cannot leave implicit the CT1 in the argument of S2b *)

Definition singular_CT2 (V : Type) : CT2 :=
  (singular_CT1 V ; squares).

Inductive cubes {V : Type} : s3_bound (singular_CT2 V) -> Type :=
  | idc {v : V} : cubes (@S3b (singular_CT2 V) v v v v v v v v
                idp idp idp idp idp idp idp idp idp idp idp idp
                ids ids ids ids ids ids).

Definition singular_CT3 (V : Type) : CT3 :=
  (singular_CT2 V ; cubes).


Definition map (V0V1 : Type * Type) : Type := fst V0V1 -> snd V0V1.

Definition universe_CT1 : CT1 :=
  (Type ; map).


Definition commutative_square (b : s2_bound universe_CT1) : Type :=
  b.(a1x) o b.(ax0) == b.(ax1) o b.(a0x).

(* given a type we have the identity commutative square *)
Definition id_commutative_square (T : Type) :
             commutative_square (@S2b universe_CT1 T T T T idmap idmap idmap idmap) :=
  fun x => idpath x.


Definition universe_CT2 : CT2 :=
  (universe_CT1 ; commutative_square).


(*      -->
       ^   ^
       |   |
    --> -->
*)
Definition comm_sq_l_wisk {V00 V01 V10 V11 : Type}
                          {a0x : V00 -> V01} {a1x : V10 -> V11}
                          {ax0 : V00 -> V10} {ax1 : V01 -> V11}
                          {T : Type} (f : T -> V00)
                          (C : commutative_square (@S2b universe_CT1
                                                  _ _ _ _ a0x a1x ax0 ax1)) :
                            commutative_square (@S2b universe_CT1 T V01 V10 V11
                                               (a0x o f) a1x
                                               (ax0 o f) ax1) :=
  fun x => C (f x).


(*      --> -->
       ^   ^
       |   |
        -->
*)
Definition comm_sq_r_wisk {V00 V01 V10 V11 : Type}
                          {a0x : V00 -> V01} {a1x : V10 -> V11}
                          {ax0 : V00 -> V10} {ax1 : V01 -> V11}
                          (C : commutative_square (@S2b universe_CT1
                                                  _ _ _ _ a0x a1x ax0 ax1))
                          {T : Type} (f : V11 -> T) :
                            commutative_square (@S2b universe_CT1
                                               V00 V01 V10 T
                                               a0x (f o a1x)
                                               ax0 (f o ax1)) :=
  fun x => ap f (C x).


Definition commutative_cube (b : s3_bound universe_CT2) : Type :=
  forall x : b.(v000), 
    (comm_sq_r_wisk b.(fxx0) b.(a11x) x) @
    (comm_sq_l_wisk b.(a0x0) b.(fx1x) x) @
    (comm_sq_r_wisk b.(f0xx) b.(ax11) x) =
    (comm_sq_l_wisk b.(ax00) b.(f1xx) x) @
    (comm_sq_r_wisk b.(fx0x) b.(a1x1) x) @
    (comm_sq_l_wisk b.(a00x) b.(fxx1) x).

(* maybe this is easier to understand?
Proof.
  pose (ijkTOjik := comm_sq_r_wisk fxx0 a11x).
  pose (jikTOjki := comm_sq_l_wisk a0x0 fx1x).
  pose (jkiTOkji := comm_sq_r_wisk f0xx ax11).
  pose (side1 := fun x => (ijkTOjik x) @ (jikTOjki x) @ (jkiTOkji x)).
  
  pose (ijkTOikj := comm_sq_l_wisk ax00 f1xx).
  pose (ikjTOkij := comm_sq_r_wisk fx0x a1x1).
  pose (kijTOkji := comm_sq_l_wisk a00x fxx1).
  pose (side2 := fun x => (ijkTOikj x) @ (ikjTOkij x) @ (kijTOkji x)).
  
  exact (side1 == side2).
Defined.
*)


Definition universe_CT3 : CT3 :=
  (universe_CT2 ; commutative_cube).



(* given a map between types we have a vertically constant commutative square *)
Definition vert_ct_commutative_square {S T : Type} (f : S -> T) :
             commutative_square (@S2b universe_CT1 S S T T idmap idmap f f) :=
  fun x => idpath (f x).


(* given a map between types we have a vertically constant commutative cube *)
Definition vert_ct_commutative_cube {S T : Type} (f : S -> T) :
             commutative_cube (@S3b universe_CT2
               S S S S T T T T idmap idmap idmap idmap idmap idmap idmap idmap f f f f
               (id_commutative_square S) (id_commutative_square T)
               (vert_ct_commutative_square f) (vert_ct_commutative_square f)
               (vert_ct_commutative_square f) (vert_ct_commutative_square f)) :=
  fun x => idpath _.

(* given two commutative squares [A, B] such that [A]'s right edge coincides with
   [B]'s left edge, we can compose them horizontally. *)
Definition horiz_commutative_square_comp
             {V00 V01 V10 V11 V20 V21 : Type}
             {a0x : V00 -> V01} {a1x : V10 -> V11} {a2x : V20 -> V21}
             {ax0 : V00 -> V10} {ax1 : V01 -> V11}
             {ax0' : V10 -> V20} {ax1' : V11 -> V21}
             (S : commutative_square (@S2b universe_CT2 _ _ _ _ a0x a1x ax0 ax1))
             (T : commutative_square (@S2b universe_CT2 _ _ _ _ a1x a2x ax0' ax1')) :
               commutative_square (@S2b universe_CT2 _ _ _ _
                                        a0x a2x (ax0' o ax0) (ax1' o ax1)) :=
  fun x => (T (ax0 x)) @ (ap ax1' (S x)).







(* not needed *)
(*
Definition strictly_less (a b : Bool) : Type :=
  match a with
    | false => match b with
                 | true => Unit 
                 | false => Empty
               end
    | true => Empty
  end.
*)

Inductive three : Type :=
  | three0 : three
  | three1 : three
  | three2 : three.

Inductive three_edges : three * three -> Type :=
  | three01 : three_edges (three0,three1)
  | three12 : three_edges (three1,three2).
 
(* not needed *)
Definition long_interval_CT1 : CT1 :=
  ( three ; three_edges ).

