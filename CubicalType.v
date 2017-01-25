Require Import HoTT.


(* TODO:
     - cone
     - (co)limit
     - product is commutative
     - consistent names
*)

(* 1, 2 and 3-semi-cubical types *)

Definition combinatorial_arrows (C0 : Type) : Type :=
  C0 -> C0 -> Type.

Definition combinatorial_squares {C0 : Type} (C1 : combinatorial_arrows C0) : Type :=
  forall v00 v01 v10 v11 : C0,
    C1 v00 v01 -> C1 v10 v11 ->
    C1 v00 v10 -> C1 v01 v11 -> Type.

Definition combinatorial_cubes {C0 : Type} {C1 : combinatorial_arrows C0}
                               (C2 : combinatorial_squares C1) : Type :=
  forall (v000 v001 v010 v011 v100 v101 v110 v111 : C0),
  forall (a00x : C1 v000 v001), forall (a01x : C1 v010 v011), forall (a10x : C1 v100 v101), forall (a11x : C1 v110 v111),
  forall (a0x0 : C1 v000 v010), forall (a0x1 : C1 v001 v011), forall (a1x0 : C1 v100 v110), forall (a1x1 : C1 v101 v111),
  forall (ax00 : C1 v000 v100), forall (ax01 : C1 v001 v101), forall (ax10 : C1 v010 v110), forall (ax11 : C1 v011 v111),
  forall (f0xx : C2 _ _ _ _ a00x a01x a0x0 a0x1), forall (f1xx : C2 _ _ _ _ a10x a11x a1x0 a1x1),
  forall (fx0x : C2 _ _ _ _ a00x a10x ax00 ax01), forall (fx1x : C2 _ _ _ _ a01x a11x ax10 ax11),
  forall (fxx0 : C2 _ _ _ _ a0x0 a1x0 ax00 ax10), forall (fxx1 : C2 _ _ _ _ a0x1 a1x1 ax01 ax11),
    Type.


Definition CT1 : Type :=
  { C0 : Type &
         combinatorial_arrows C0
  }.

Definition CT2 : Type :=
  { C0 : Type &
  { C1 : combinatorial_arrows C0 &
         combinatorial_squares C1
  }}.

Definition CT3 : Type :=
  { C0 : Type &
  { C1 : combinatorial_arrows C0 &
  { C2 : combinatorial_squares C1 &
         combinatorial_cubes C2
  }}}.

Definition CT2toCT1 (C : CT2) : CT1 :=
  (C.1 ; C.2.1).
Coercion CT2toCT1 : CT2 >-> CT1.

Definition CT3toCT2 (C : CT3) : CT2 :=
  (C.1 ; (C.2.1 ; C.2.2.1)).
Coercion CT3toCT2 : CT3 >-> CT2.



Definition combinatorial_arrows_morph (C D : CT1) (M0 : C.1 -> D.1) : Type :=
  forall c0 c1 : C.1, C.2 c0 c1 -> D.2 (M0 c0) (M0 c1).

Definition combinatorial_squares_morph (C D : CT2) {M0 : C.1 -> D.1}
                                       (M1 : combinatorial_arrows_morph C D M0) : Type :=
  forall v00 v01 v10 v11 : C.1,
  forall a0x : C.2.1 v00 v01, forall a1x : C.2.1 v10 v11,
  forall ax0 : C.2.1 v00 v10, forall ax1 : C.2.1 v01 v11,
    C.2.2 _ _ _ _ a0x a1x ax0 ax1 ->
    D.2.2 _ _ _ _ (M1 _ _ a0x) (M1 _ _ a1x) (M1 _ _ ax0) (M1 _ _ ax1).

Definition combinatorial_cubes_morph (C D : CT3) {M0 : C.1 -> D.1}
                                     {M1 : combinatorial_arrows_morph C D M0}
                                     (M2 : combinatorial_squares_morph C D M1) : Type :=
  forall (v000 v001 v010 v011 v100 v101 v110 v111 : C.1),
  forall (a00x : C.2.1 v000 v001), forall (a01x : C.2.1 v010 v011), forall (a10x : C.2.1 v100 v101), forall (a11x : C.2.1 v110 v111),
  forall (a0x0 : C.2.1 v000 v010), forall (a0x1 : C.2.1 v001 v011), forall (a1x0 : C.2.1 v100 v110), forall (a1x1 : C.2.1 v101 v111),
  forall (ax00 : C.2.1 v000 v100), forall (ax01 : C.2.1 v001 v101), forall (ax10 : C.2.1 v010 v110), forall (ax11 : C.2.1 v011 v111),
  forall (f0xx : C.2.2.1 _ _ _ _ a00x a01x a0x0 a0x1), forall (f1xx : C.2.2.1 _ _ _ _ a10x a11x a1x0 a1x1),
  forall (fx0x : C.2.2.1 _ _ _ _ a00x a10x ax00 ax01), forall (fx1x : C.2.2.1 _ _ _ _ a01x a11x ax10 ax11),
  forall (fxx0 : C.2.2.1 _ _ _ _ a0x0 a1x0 ax00 ax10), forall (fxx1 : C.2.2.1 _ _ _ _ a0x1 a1x1 ax01 ax11),
    C.2.2.2 _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _
            f0xx f1xx fx0x fx1x fxx0 fxx1 ->
      D.2.2.2 _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ _ _ _ _
              (M2 _ _ _ _ _ _ _ _ f0xx) (M2 _ _ _ _ _ _ _ _ f1xx)
              (M2 _ _ _ _ _ _ _ _ fx0x) (M2 _ _ _ _ _ _ _ _ fx1x)
              (M2 _ _ _ _ _ _ _ _ fxx0) (M2 _ _ _ _ _ _ _ _ fxx1).
   
Definition CT1_morphism (C D : CT1) : Type :=
  { M0 : C.1 -> D.1 &
         combinatorial_arrows_morph C D M0
  }.

Definition CT2_morphism (C D : CT2) : Type :=
  { M0 : C.1 -> D.1 &
  { M1 : combinatorial_arrows_morph C D M0 &
         combinatorial_squares_morph C D M1 
  }}.

Definition CT3_morphism (C D : CT3) : Type :=
 { M0 : C.1 -> D.1 &
 { M1 : combinatorial_arrows_morph C D M0 &
 { M2 : combinatorial_squares_morph C D M1 &
        combinatorial_cubes_morph C D M2
 }}}.