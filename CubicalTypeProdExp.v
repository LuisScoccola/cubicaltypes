Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.


(* 
Local Unset Elimination Schemes.
*)

(* product of 1-semi-cubical types *)
Definition prod11_zerocells (C D : CT1) : Type := C.1 * D.1.

Inductive prod11_onecells (C D : CT1) : combinatorial_arrows (prod11_zerocells C D) :=
  | edge_vert (i0 i1 : C.1) (ai : C.2 i0 i1) (j : D.1) : prod11_onecells C D (i0, j) (i1, j)
  | vert_edge (i : C.1) (j0 j1 : D.1) (aj : D.2 j0 j1) : prod11_onecells C D (i, j0) (i, j1).

(* Is this necessary?
Scheme prod11_onecells_ind := Induction for prod11_onecells Sort Type.
Scheme prod11_onecells_rec := Minimality for prod11_onecells Sort Type.
Definition prod11_onecells_rect := prod11_onecells_ind.
*)

Arguments edge_vert {C D i0 i1} ai j.
Arguments vert_edge {C D} i {j0 j1} aj.

Inductive prod11_twocells (C D : CT1) : combinatorial_squares (prod11_onecells C D) :=
  | square (i0 i1 : C.1) (ai : C.2 i0 i1) (j0 j1 : D.1) (aj : D.2 j0 j1) :
           prod11_twocells C D _ _ _ _ (vert_edge i0 aj) (vert_edge i1 aj)
                                       (edge_vert ai j0) (edge_vert ai j1).

Arguments square {C D} {i0 i1} ai {j0 j1} aj.


Definition CT1_product (C D : CT1) : CT2 :=
  (prod11_zerocells C D ; (prod11_onecells C D ; prod11_twocells C D) ).


(* product of a 1-CT and a 2-CT *)

  (* same 0-cells as the 1,1-product *)
Definition prod12_zerocells (C : CT1) (D : CT2) : Type := prod11_zerocells C D.

  (* same 1-cells as the 1,1-product *)
Definition prod12_onecells (C : CT1) (D : CT2) : combinatorial_arrows (prod12_zerocells C D) :=
  prod11_onecells C D.

  (* the 2-cells are already different *)
Inductive prod12_twocells (C : CT1) (D : CT2) : combinatorial_squares (prod12_onecells C D) :=
  | homsquare12 (c : C.1) (v00 v01 v10 v11 : D.1)
                (a0x : (CT2toCT1 D).2 v00 v01) (a1x : (CT2toCT1 D).2 v10 v11)
                (ax0 : (CT2toCT1 D).2 v00 v10) (ax1 : (CT2toCT1 D).2 v01 v11)
                (f : D.2.2 _ _ _ _ a0x a1x ax0 ax1) :
                  prod12_twocells C D _ _ _ _ (vert_edge c a0x) (vert_edge c a1x)
                                              (vert_edge c ax0) (vert_edge c ax1)
  | mixsquare12 (i0 i1 : C.1) (ai : C.2 i0 i1)
                (j0 j1 : (CT2toCT1 D).1) (aj : (CT2toCT1 D).2 j0 j1) :
                  prod12_twocells C D _ _ _ _ (vert_edge i0 aj) (vert_edge i1 aj)
                                              (edge_vert ai j0) (edge_vert ai j1).

Arguments homsquare12 {C D} c {v00 v01 v10 v11} {a0x a1x ax0 ax1} f.
Arguments mixsquare12 {C D} {i0 i1} ai {j0 j1} aj.

  (* the 3-cells *)
Inductive prod12_threecells (C : CT1) (D : CT2) : combinatorial_cubes (prod12_twocells C D) :=
  | cube12 (c0 c1 : C.1) (cx : C.2 c0 c1) (v00 v01 v10 v11 : D.1)
           (a0x : (CT2toCT1 D).2 v00 v01) (a1x : (CT2toCT1 D).2 v10 v11)
           (ax0 : (CT2toCT1 D).2 v00 v10) (ax1 : (CT2toCT1 D).2 v01 v11)
           (f : D.2.2 _ _ _ _ a0x a1x ax0 ax1) :
             prod12_threecells C D _ _ _ _ _ _ _ _
                                   _ _ _ _ _ _ _ _ _ _ _ _
                                   (homsquare12 c0 f)
                                   (homsquare12 c1 f)
                                   (mixsquare12 cx a0x)
                                   (mixsquare12 cx a1x)
                                   (mixsquare12 cx ax0)
                                   (mixsquare12 cx ax1).
  
Arguments cube12 {C D} {c0 c1} cx {v00 v01 v10 v11} {a0x a1x ax0 ax1} f.

Definition CT12_product (C : CT1) (D : CT2) : CT3 :=
  ( prod12_zerocells C D ;
  ( prod12_onecells C D ;
  ( prod12_twocells C D ;
    prod12_threecells C D
  ))).


(* now we want to prove that the 1,1-product is commutative *)


Definition flip0 {A B : Type} : A * B -> B * A :=
  fun ab => (snd ab , fst ab).

(* not needed *)
Definition flip0_involutive {A B : Type} (ab : A * B) : flip0 (flip0 ab) = ab :=
  idpath _.

Definition prod11_zerocells_commute `{Univalence}
                                  (C D : CT1) :
                                    prod11_zerocells C D = prod11_zerocells D C :=
  equiv_path_universe _ _ (equiv_prod_symm C.1 D.1).



(* this the 1-dimensional version of flip0 *)
Definition flip1 {C D : CT1} (x y : prod11_zerocells C D) :
                   prod11_onecells C D x y -> prod11_onecells D C (flip0 x) (flip0 y) :=
  fun X => match X with
             | edge_vert i0 i1 ai j => vert_edge j ai
             | vert_edge i j0 j1 aj => edge_vert aj i
           end.

Notation prod11_onecells_map_to := flip1.


Definition prod11_onecells_map_from {C D : CT1} (x y : prod11_zerocells C D) :
                                      prod11_onecells D C (flip0 x) (flip0 y) ->
                                        prod11_onecells C D x y :=
  flip1 (flip0 x) (flip0 y).


Definition flip1_involutive {C D : CT1} (x y : prod11_zerocells C D) :
                              (flip1 (flip0 x) (flip0 y)) o (flip1 x y) == idmap :=
  fun X => match X with
             | edge_vert _ _ _ _ => idpath _
             | vert_edge _ _ _ _ => idpath _
           end.

Notation prod11_onecells_map_to_from := flip1_involutive.


Definition prod11_onecells_map_from_to {C D : CT1} (x y : prod11_zerocells C D) :
                                     (flip1 x y) o
                                     (flip1 (flip0 x) (flip0 y)) == idmap :=
  flip1_involutive (flip0 x) (flip0 y).
                            


Definition prod11_onecells_commute `{Univalence}
             (C D : CT1) :
             (prod11_zerocells_commute C D) # (CT1_product C D).2.1 = (CT1_product D C).2.1.
Proof.
  pose (flip_equiv := equiv_prod_symm C.1 D.1).
  (* we prove it point-wise *)
  simple refine (path_forall _ _ _). intro x.
  simple refine (path_forall _ _ _). intro y.
  simple refine (path_universe_uncurried _).
  (* todo: don't use rewrite *)
  rewrite (transport_arrow _ _ _).
  rewrite (transport_arrow _ _ _). 
  rewrite transport_const.
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  simple refine (BuildEquiv _ _ _ _).
    - exact (prod11_onecells_map_from x y).
    - simple refine (isequiv_biinv _ _).
      exact ((prod11_onecells_map_to x y ; prod11_onecells_map_from_to x y) ,
             (prod11_onecells_map_to x y ; prod11_onecells_map_to_from x y) ).
Qed.


Arguments flip1 {C D} {x y} a.

(* this is the 2-dimensional version of flip0 *)
Definition flip2 {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D  v01 v11) :
               prod11_twocells C D _ _ _ _ a0x a1x ax0 ax1 ->
                 prod11_twocells D C _ _ _ _   (* the middle points are interchanged! *)
                                     (flip1 ax0) (flip1 ax1)
                                     (flip1 a0x) (flip1 a1x) :=
  fun X => match X with
             | square _ _ ai _ _ aj => square aj ai
           end.

Notation prod11_twocells_map_to := flip2.


Definition prod11_twocells_map_from {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               prod11_twocells D C _ _ _ _ (flip1 ax0) (flip1 ax1)
                                           (flip1 a0x) (flip1 a1x) ->
                 prod11_twocells C D _ _ _ _ a0x a1x ax0 ax1.
Proof.
  intro X.
    (* if things computed a lot, the following would be the answer. For example for flip0 it just works *)
  pose (t0 := flip2 (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x) X).
    (* since that's not the case we have to transport a couple of times.
       maybe there's a cleaner way to do this? *)
  pose (t1 := (flip1_involutive _ _ ax1) # t0).
  pose (t2 := transport (fun e => _ e ax1) (flip1_involutive _ _ ax0) t1).
  simpl in t2.
  pose (t3 := transport (fun e => _ e ax0 ax1) (flip1_involutive _ _ a1x) t2).
  simpl in t3.
  exact (transport (fun e => _ e a1x ax0 ax1) (flip1_involutive _ _ a0x) t3).
Defined.


Definition flip2_involutive {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               (prod11_twocells_map_from a0x a1x ax0 ax1) o
                 (prod11_twocells_map_to a0x a1x ax0 ax1) == idmap :=
  fun X => match X with
             | square _ _ _ _ _ _ => idpath _
           end.


(*
Definition prod11_twocells_map_from_to {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               (prod11_twocells_map_to a0x a1x ax0 ax1) o
                 (prod11_twocells_map_from a0x a1x ax0 ax1) == idmap.
Proof.
  intro X.
  pose (t0 := flip2_involutive (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x) X).
  

  pose (t1 := transport (fun e => _ e _ X) (flip1_involutive _ _ ax1)^ t0).
  rewrite (flip1_involutive _ _ ax0) in test.
  rewrite (flip1_involutive _ _ a1x) in test.
  rewrite (flip1_involutive _ _ a0x) in test.
  exact test.
  intro X. induction X. trivial.
*)







(* product is commutative, unfinished


Definition prod11_twocells_commute `{Univalence}
             (C D : CT1) :
             (prod11_zerocells_commute C D) # (CT1_product C D).2 = (CT1_product D C).2.
Proof.
  intros.
  simpl.
  simple refine (path_forall _ _ _). intro x.
  simple refine (path_forall _ _ _). intro y.
  simple refine (path_universe_uncurried _).
  (* todo: don't use rewrite *)
  rewrite (transport_arrow _ _ _). 
  rewrite transport_const.

Definition commute `{Univalence}
                   (C D : CT1) : CT1_product C D = CT1_product D C.
*)


(* 1-natural transformation: if [C] is a 1-CT and [H] is a 2-CT
   we form the 1-CT [H^C].
     - The 0-cells are 1-morphisms [C -> H.1]
     - The 1-cells are given by the fibration [Nat : (C -> H.1) -> (C -> H.1) -> Type]
*)
Definition inclusion_top1 {C : CT1} {H : CT2}
                          (N : CT2_morphism (CT1_product interval_CT1 C) H) :
                            CT1_morphism C H.
Proof.
  exists ( fun c0 => N.1 (false , c0) ).
  exact (fun _ _ a => N.2.1 _ _ (@vert_edge interval_CT1 C false _ _ a)).
Defined.

Definition inclusion_bot1 {C : CT1} {H : CT2}
                          (N : CT2_morphism (CT1_product interval_CT1 C) H) :
                            CT1_morphism C H.
Proof.
  exists ( fun c0 => N.1 (true , c0) ).
  exact (fun _ _ a => N.2.1 _ _ (@vert_edge interval_CT1 C true _ _ a)).
Defined.
(* abstract the inclusions? *)


Inductive CT1_naturalt (C : CT1) (H : CT2) :
            (CT1_morphism C H) -> (CT1_morphism C H) -> Type :=
  | ct1_nat (N : CT2_morphism (CT1_product interval_CT1 C) H) :
      CT1_naturalt C H (inclusion_top1 N) (inclusion_bot1 N).


(* [H^C] *)
Definition exponential12 (H : CT2) (C : CT1) : CT1 :=
  (CT1_morphism C H ; CT1_naturalt C H).


Definition inclusion_top2 {C : CT2} {H : CT3}
                          (N : CT3_morphism (CT12_product interval_CT1 C) H) :
                            CT2_morphism C H.
Proof.
  exists ( fun c0 => N.1 (false , c0) ).
  exists ( fun _ _ a => N.2.1 _ _ (@vert_edge interval_CT1 C false _ _ a)).
  exact ( fun _ _ _ _ _ _ _ _ f =>
            N.2.2.1 _ _ _ _ _ _ _ _ (@homsquare12 interval_CT1 C false _ _ _ _ _ _ _ _ f )).
Defined.
                                       
Definition inclusion_bot2 {C : CT2} {H : CT3}
                          (N : CT3_morphism (CT12_product interval_CT1 C) H) :
                            CT2_morphism C H.
Proof.
  exists ( fun c0 => N.1 (true , c0) ).
  exists ( fun _ _ a => N.2.1 _ _ (@vert_edge interval_CT1 C true _ _ a)).
  exact ( fun _ _ _ _ _ _ _ _ f =>
            N.2.2.1 _ _ _ _ _ _ _ _ (@homsquare12 interval_CT1 C true _ _ _ _ _ _ _ _ f )).
Defined.

Inductive CT2_naturalt (C : CT2) (H : CT3) :
            (CT2_morphism C H) -> (CT2_morphism C H) -> Type :=
  | ct2_nat (N : CT3_morphism (CT12_product interval_CT1 C) H) :
      CT2_naturalt C H (inclusion_top2 N) (inclusion_bot2 N).

(* [H^C] *)
Definition exponential23 (H : CT3) (C : CT2) : CT1 :=
  (CT2_morphism C H ; CT2_naturalt C H).