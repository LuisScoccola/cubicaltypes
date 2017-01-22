Require Import HoTT.
Require Import CubicalType.


(* true < false *)
Definition strictly_less (a b : Bool) : Type :=
  match a with
    | true => match b with
                | true => Empty 
                | false => Unit 
              end
    | false => Empty
  end.
       

(* examples *)

Definition interval_CT1 : CT1 :=
  ( Bool ; strictly_less ).


Inductive squares {V : Type} (v00 : V) : forall (v01 v10 v11 : V),
                  v00 = v01 -> v10 = v11 -> v00 = v10 -> v01 = v11 -> Type :=
  | ids : squares v00 v00 v00 v00 idpath idpath idpath idpath.  

Arguments ids {V v00}.


Inductive cubes {V : Type} (v000 : V) :
                forall (v001 v010 v011 v100 v101 v110 v111 : V),
                forall (a00x : v000 = v001), forall (a01x : v010 = v011), forall (a10x : v100 = v101), forall (a11x : v110 = v111),
                forall (a0x0 : v000 = v010), forall (a0x1 : v001 = v011), forall (a1x0 : v100 = v110), forall (a1x1 : v101 = v111),
                forall (ax00 : v000 = v100), forall (ax01 : v001 = v101), forall (ax10 : v010 = v110), forall (ax11 : v011 = v111),
                forall (f0xx : squares _ _ _ _ a00x a01x a0x0 a0x1), forall (f1xx : squares _ _ _ _ a10x a11x a1x0 a1x1),
                forall (fx0x : squares _ _ _ _ a00x a10x ax00 ax01), forall (fx1x : squares _ _ _ _ a01x a11x ax10 ax11),
                forall (fxx0 : squares _ _ _ _ a0x0 a1x0 ax00 ax10), forall (fxx1 : squares _ _ _ _ a0x1 a1x1 ax01 ax11),
                  Type :=
  | idc : cubes v000 v000 v000 v000 v000 v000 v000 v000
                idpath idpath idpath idpath idpath idpath idpath idpath idpath idpath idpath idpath
                ids ids ids ids ids ids.



Definition singular_CT1 (A : Type) : CT1 := (A ; paths).

Definition singular_CT2 (A : Type) : CT2 :=
  (A ; (paths ; squares)).

Definition singular_CT3 (A : Type) : CT3 :=
  (A ; (paths ; (squares ; cubes))).


Definition map (V0 V1 : Type) : Type := V0 -> V1.
Definition commutative_square (V00 V01 V10 V11 : Type)
                              (a0x : map V00 V01) (a1x : map V10 V11)
                              (ax0 : map V00 V10) (ax1 : map V01 V11) :=
  a1x o ax0 == ax1 o a0x.

(*      -->
       ^   ^
       |   |
    --> -->
*)
Definition comm_sq_l_wisk {V00 V01 V10 V11 : Type}
                          {a0x : map V00 V01} {a1x : map V10 V11}
                          {ax0 : map V00 V10} {ax1 : map V01 V11}
                          {T : Type} (f : T -> V00)
                          (C : commutative_square _ _ _ _ a0x a1x ax0 ax1) :
                            commutative_square T V01 V10 V11
                                               (a0x o f) a1x
                                               (ax0 o f) ax1 :=
  fun x => C (f x).

(*      --> -->
       ^   ^
       |   |
        -->
*)
Definition comm_sq_r_wisk {V00 V01 V10 V11 : Type}
                          {a0x : map V00 V01} {a1x : map V10 V11}
                          {ax0 : map V00 V10} {ax1 : map V01 V11}
                          (C : commutative_square _ _ _ _ a0x a1x ax0 ax1)
                          {T : Type} (f : V11 -> T) :
                            commutative_square V00 V01 V10 T
                                               a0x (f o a1x)
                                               ax0 (f o ax1) :=
  fun x => ap f (C x).


Definition commutative_cube
             (v000 v001 v010 v011 v100 v101 v110 v111 : Type)
             (a00x : map v000 v001) (a01x : map v010 v011) (a10x : map v100 v101) (a11x : map v110 v111)
             (a0x0 : map v000 v010) (a0x1 : map v001 v011) (a1x0 : map v100 v110) (a1x1 : map v101 v111)
             (ax00 : map v000 v100) (ax01 : map v001 v101) (ax10 : map v010 v110) (ax11 : map v011 v111)
             (f0xx : commutative_square _ _ _ _ a00x a01x a0x0 a0x1) (f1xx : commutative_square _ _ _ _ a10x a11x a1x0 a1x1)
             (fx0x : commutative_square _ _ _ _ a00x a10x ax00 ax01) (fx1x : commutative_square _ _ _ _ a01x a11x ax10 ax11)
             (fxx0 : commutative_square _ _ _ _ a0x0 a1x0 ax00 ax10) (fxx1 : commutative_square _ _ _ _ a0x1 a1x1 ax01 ax11) :
               Type :=
  forall x : v000, 
    (comm_sq_r_wisk fxx0 a11x x) @ (comm_sq_l_wisk a0x0 fx1x x) @ (comm_sq_r_wisk f0xx ax11 x) =
    (comm_sq_l_wisk ax00 f1xx x) @ (comm_sq_r_wisk fx0x a1x1 x) @ (comm_sq_l_wisk a00x fxx1 x).


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


Definition universe_CT1 : CT1 :=
  (Type ; map).

Definition universe_CT2 : CT2 :=
  (Type ; (map ; commutative_square)).

Definition universe_CT3 : CT3 :=
  (Type ; (map ; (commutative_square ; commutative_cube))).