Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.


(* product of 1-semi-cubical types *)
Definition prod_zerocells (C D : CT1) : Type := C.1 * D.1.

Inductive prod_onecells (C D : CT1) : prod_zerocells C D -> prod_zerocells C D -> Type :=
  | edge_vert (i0 i1 : C.1) (ai : C.2 i0 i1) (j : D.1) : prod_onecells C D (i0, j) (i1, j)
  | vert_edge (i : C.1) (j0 j1 : D.1) (aj : D.2 j0 j1) : prod_onecells C D (i, j0) (i, j1).

Arguments edge_vert {C D i0 i1} ai j.
Arguments vert_edge {C D} i {j0 j1} aj.

Inductive prod_twocells (C D : CT1) :
                     forall v00 v01 v10 v11 : prod_zerocells C D,
                       (prod_onecells C D) v00 v01 -> (prod_onecells C D) v10 v11 ->
                       (prod_onecells C D) v00 v10 -> (prod_onecells C D) v01 v11 ->
                         Type :=
  | square (i0 i1 : C.1) (ai : C.2 i0 i1) (j0 j1 : D.1) (aj : D.2 j0 j1) :
           prod_twocells C D (i0 , j0) (i0 , j1) (i1 , j0) (i1 , j1)
                        (vert_edge i0 aj) (vert_edge i1 aj)
                        (edge_vert ai j0) (edge_vert ai j1).

Arguments square {C D} {i0 i1} ai {j0 j1} aj.


Definition CT1_product (C D : CT1) : CT2 :=
  (prod_zerocells C D ; (prod_onecells C D ; prod_twocells C D) ).
   
(* product is commutative, unfinished
Definition commute `{Univalence}
                   (C D : CT1) : CT1_product C D = CT1_product D C.
Proof.
  pose (flip_equiv := equiv_prod_symm C.1 D.1).
  pose (flip_equal := equiv_path_universe _ _ flip_equiv).
  simple refine (path_sigma _ _ _ _ _).
    - exact flip_equal.
    - simple refine (path_sigma _ _ _ _ _).
      + rewrite (transport_sigma _ _). simpl.
        simple refine (path_forall _ _ _). intro x.
        simple refine (path_forall _ _ _). intro y.
        refine (inverse _).
        simple refine (path_universe_uncurried _).
        simple refine (BuildEquiv _ _ _ _).
          * intro. induction X.
              -- rewrite (transport_arrow _ _ _).
                 rewrite (transport_arrow _ _ _). 
                 rewrite (transport_path_universe_V_uncurried flip_equiv _).
                 rewrite (transport_path_universe_V_uncurried flip_equiv _).
*)


(* 1-natural transformation: if [C] is a 1-CT and [H] is a 2-CT
   we form the 1-CT [H^C].
     - The 0-cells are 1-morphisms [C -> H.1]
     - The 1-cells are given by the fibration [Nat : (C -> H.1) -> (C -> H.1) -> Type]
*)
Definition inclusion_top {C : CT1} {H : CT2}
                         (N : CT2_morphism (CT1_product interval_CT1 C) H) :
                           CT1_morphism C (CT2toCT1 H).
Proof.
  exists ( fun c0 => N.1 (false , c0) ).
  exact (fun c0 c1 => (fun a => N.2.1 (false , c0) (false , c1) (@vert_edge interval_CT1 C false c0 c1 a))).
Defined.
  (*
  ( fun c0 => N.1 (false , c0)
  ; fun c0 c1 a => N.2.1 (false , c0) (false , c1) (@vert_edge interval_CT1 C false c0 c1 a)).
  *)
Definition inclusion_bot {C : CT1} {H : CT2}
                         (N : CT2_morphism (CT1_product interval_CT1 C) H) :
                           CT1_morphism C (CT2toCT1 H).
Proof.
  exists ( fun c0 => N.1 (true , c0) ).
  exact (fun c0 c1 => (fun a => N.2.1 (true , c0) (true , c1) (@vert_edge interval_CT1 C true c0 c1 a))).
Defined.
(* abstract the inclusions? *)


Inductive CT1_naturalt (C : CT1) (H : CT2) :
            (CT1_morphism C (CT2toCT1 H)) -> (CT1_morphism C (CT2toCT1 H)) -> Type :=
  | ct1_nat (N : CT2_morphism (CT1_product interval_CT1 C) H) :
      CT1_naturalt C H (inclusion_top N) (inclusion_bot N).