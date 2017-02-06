Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.


(* 
Unset Elimination Schemes.
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
                                    (C D : CT1) : prod11_zerocells C D = prod11_zerocells D C :=
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


(*
Definition prod11_onecells_commute_pointwise'' {C D : CT1} (x y : prod11_zerocells C D) :
             IsEquiv (flip1 x y).
Proof.
  simple refine
    (BuildIsEquiv _ _ (isequiv_biinv _
                         ((prod11_onecells_map_from x y ; prod11_onecells_map_to_from x y)
                         ,(prod11_onecells_map_from x y ; prod11_onecells_map_from_to x y)))).



(* we already abstracted basically everything in this Lemma, todo: organize and delete it *)
(* We know that the commutativity of the 1-cells boils down to the following
   pointwise equivalence of fibrations, so we prove this first *)
Lemma product_onecells_commute_pointwise `{Univalence} (C D : CT1) (x y : prod11_zerocells D C) :
  ((prod11_onecells C D) (flip0 x) (flip0 y)) =
    (transport combinatorial_arrows (prod11_zerocells_commute C D) (prod11_onecells C D) x y).
Proof.
  pose (flip_equiv := equiv_prod_symm C.1 D.1).

  pose (t0 := transport_arrow _ _ _ :
           (transport combinatorial_arrows (prod11_zerocells_commute C D) (prod11_onecells C D) x)
             = _ ).
  pose (t0' := ap (fun f => f y) t0).
  
  pose (t1 := transport_arrow _ _ _ :
           (transport (fun x0 : Type => x0 -> Type) (prod11_zerocells_commute C D)
             (prod11_onecells C D (transport idmap (prod11_zerocells_commute C D)^ x)) y)
             = _).
  
  pose (t2 := transport_const _ _ :
           transport (fun _ : Type => Type) (prod11_zerocells_commute C D)
             (prod11_onecells C D (transport idmap (prod11_zerocells_commute C D)^ x)
                                  (transport idmap (prod11_zerocells_commute C D)^ y))
           = prod11_onecells C D (transport idmap (prod11_zerocells_commute C D)^ x)
                                 (transport idmap (prod11_zerocells_commute C D)^ y) ).
  
  pose (t3 := transport_path_universe_V_uncurried flip_equiv _ :
           (transport idmap (prod11_zerocells_commute C D)^ x)
              = (flip_equiv^-1 x)).
  pose (t3' := ap (fun e => prod11_onecells C D e (transport idmap (prod11_zerocells_commute C D)^ y)) t3).

  pose (t4 := transport_path_universe_V_uncurried flip_equiv _ :
           (transport idmap (prod11_zerocells_commute C D)^ y)
             = (flip_equiv^-1 y)). 
  pose (t4' := ap (fun e => prod11_onecells C D (flip_equiv^-1 x) e) t4).

  exact (t0' @ t1 @ t2 @ t3' @ t4')^.
   
  (* the above is an explicit version of:
  rewrite (transport_arrow _ _ _).
  rewrite (transport_arrow _ _ _). 
  rewrite transport_const.
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  reflexivity.
  *)
Defined.


Definition prod11_onecells_commute `{Univalence}
             (C D : CT1) :
             (prod11_zerocells_commute C D) # (CT1_product C D).2.1 = (CT1_product D C).2.1.
Proof.
  (* we prove it point-wise *)
  simple refine (path_forall _ _ _). intro x.
  simple refine (path_forall _ _ _). intro y.
  simple refine (path_universe_uncurried _).

  (* this is the pointwise equivalence *)
  pose (myequiv := BuildEquiv _ _ (prod11_onecells_map_from x y)
           (isequiv_biinv _
              ((prod11_onecells_map_to x y ; prod11_onecells_map_from_to x y) ,
               (prod11_onecells_map_to x y ; prod11_onecells_map_to_from x y)
        ))).

  pose (t0 := ap (fun e => e <~> (prod11_onecells D C) x y)
                                    (product_onecells_commute_pointwise C D x y)).

  exact (transport idmap t0 myequiv).
Defined.


Definition prod11_onecells_commute' `{Univalence}
             (C D : CT1) :
             CT2toCT1 (CT1_product C D) = CT2toCT1 (CT1_product D C).
Proof.
  apply path_CT1.
  exists (@equiv_prod_symm C.1 D.1).
  unfold combinatorial_arrows_path. simpl.

*)



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





(*
  We now construct the inverse of flip2.

     ---- f2 ---->
    ^             ^ 
    |          /  |
    i    - a -    j
    |  /          |
    | ,           |
     -f2(f1(f1))->
*)


Section Flip2Inverse.

(*
  Context {A : Type} (P : A -> Type) (x y : A) (p : x = y).

  Global Instance isequiv_transport : IsEquiv (transport P p) | 0
    := BuildIsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  Definition equiv_transport : P x <~> P y
    := BuildEquiv _ _ (transport P p) _.
*)
 
Context {C D : CT1} {v00 v01 v10 v11 : prod11_zerocells C D}
        (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
        (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11).


Definition TC : Type :=
  prod11_twocells C D _ _ _ _ a0x a1x ax0 ax1.

Definition TCf : Type :=
  prod11_twocells D C _ _ _ _ (flip1 ax0) (flip1 ax1)
                              (flip1 a0x) (flip1 a1x).

Definition TCff : Type  :=
  prod11_twocells C D _ _ _ _
                     (flip1 (flip1 a0x)) (flip1 (flip1 a1x))
                     (flip1 (flip1 ax0)) (flip1 (flip1 ax1)).


Definition map_a : TCf -> TCff :=
  flip2 (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x).


Definition path_i : TCff = TC :=
    (ap _ (flip1_involutive _ _ ax1))
  @ (ap (fun e => _ e _) (flip1_involutive _ _ ax0))
  @ (ap (fun e => _ e _ _) (flip1_involutive _ _ a1x))
  @ (ap (fun e => _ e _ _ _) (flip1_involutive _ _ a0x)).


Definition map_i : TCff <~> TC.
Proof.
  exists (transport idmap path_i).
  exact (isequiv_transport _ _ _ _).
Defined.


(* aka: [i o a] *)
Definition prod11_twocells_map_from : TCf -> TC :=
  map_i o map_a.

End Flip2Inverse.


(* proof that what we constructed is a left inverse of [flip2]
   aka: [i o a] has as right inverse [flip2] *)
Definition flip2_involutive {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               (prod11_twocells_map_from a0x a1x ax0 ax1) o (flip2 a0x a1x ax0 ax1) == idmap :=
  fun X => match X with
             | square _ _ _ _ _ _ => idpath _
           end.
  (* although the inverse involves some transports, when the inhabitants are
     constructors the paths over which we transport are refl so the transport
     computes *)



(* we now want to show that [i o a] has also a left inverse *)
Section ioaInverse.
  
Context {C D : CT1} {v00 v01 v10 v11 : prod11_zerocells C D}
        (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
        (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11).


Definition map_joflip2' :=
  (prod11_twocells_map_from (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x)).


  (* aka: [a] has a left inverse: [j o flip2'] *)
Definition flip2_involutive' :
               map_joflip2' o (map_a a0x a1x ax0 ax1) == idmap :=
  flip2_involutive (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x).



  (* we now want to show that [i o a] has a left inverse: [j o flip2(f1(f1)) o i^-1] *)
  (* todo: don't use rewrite *)
  (* maybe give a name to [j o flip2(f1(f1)) o i^-1] ? *)
Definition prod11_twocells_fl :
                 (prod11_twocells_map_from _ _ _ _)
               o (map_i a0x a1x ax0 ax1)^-1
               o (prod11_twocells_map_from a0x a1x ax0 ax1) == idmap.
Proof.
  intro x.
  unfold prod11_twocells_map_from.
  simpl.
  rewrite (transport_Vp idmap (path_i a0x a1x ax0 ax1) _).
  apply flip2_involutive'.
Qed.


Definition isequiv_ioa : IsEquiv (prod11_twocells_map_from a0x a1x ax0 ax1) :=
  isequiv_biinv _
    (( ( prod11_twocells_map_from _ _ _ _) o (map_i a0x a1x ax0 ax1)^-1
       ; prod11_twocells_fl)
     , ( flip2 a0x a1x ax0 ax1 ; flip2_involutive a0x a1x ax0 ax1)).

End ioaInverse.



(* unfinished: looks like its better characterize the pathspaces in [CT2] first
Definition prod11_twocells_commute `{Univalence}
             (C D : CT1) :
             (prod11_zerocells_commute C D) # (CT1_product C D).2 = (CT1_product D C).2.
Proof.
  intros. simpl.
  rewrite (transport_sigma (prod11_zerocells_commute C D) _).
  simple refine (path_sigma _ _ _ _ _).
    - simpl.
      exact (prod11_onecells_commute C D).
    - simpl. 
      rewrite (apD011 _ _ _).
      rewrite (transport_arrow _ _ _).
      rewrite (transport_arrow _ _ _). 
      rewrite transport_const.
      rewrite (transport_path_universe_V_uncurried flip_equiv _).
      rewrite (transport_path_universe_V_uncurried flip_equiv _).
      reflexivity.




Definition commute `{Univalence}
                   (C D : CT1) : CT1_product C D = CT1_product D C.
Proof.
  simple refine (path_sigma _ _ _ _ _).
    - exact (prod11_zerocells_commute C D).
    - simple refine (path_sigma _ _ _ _ _).
        + rewrite (transport_sigma _ _).
          exact (prod11_onecells_commute C D).
        + simpl.
          
*)













(* once it works we can delete these: *)

(*
Definition map_i {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             {a0x : prod11_onecells C D v00 v01} {a1x : prod11_onecells C D v10 v11}
             {ax0 : prod11_onecells C D v00 v10} {ax1 : prod11_onecells C D v01 v11} :
               (prod11_twocells C D _ _ _ _ (flip1 (flip1 a0x)) (flip1 (flip1 a1x))
                                            (flip1 (flip1 ax0)) (flip1 (flip1 ax1))) ->
                 (prod11_twocells C D _ _ _ _ a0x a1x ax0 ax1) :=
  transport idmap (path_i a0x a1x ax0 ax1).
*)

(*
Definition map_i_inv {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               (prod11_twocells C D _ _ _ _ a0x a1x ax0 ax1) ->
                 (prod11_twocells C D _ _ _ _ (flip1 (flip1 a0x)) (flip1 (flip1 a1x))
                                              (flip1 (flip1 ax0)) (flip1 (flip1 ax1))) :=
  transport idmap (path_i a0x a1x ax0 ax1)^.
 *)


(* not needed 
Definition prod11_twocells_flip2' {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               prod11_twocells C D _ _ _ _ (flip1 (flip1 a0x)) (flip1 (flip1 a1x))
                                           (flip1 (flip1 ax0)) (flip1 (flip1 ax1)) ->
                 prod11_twocells D C _ _ _ _ (flip1 (flip1 (flip1 ax0)))
                                             (flip1 (flip1 (flip1 ax1)))
                                             (flip1 (flip1 (flip1 a0x)))
                                             (flip1 (flip1 (flip1 a1x))):=
  flip2 (flip1 (flip1 a0x)) (flip1 (flip1 a1x))
        (flip1 (flip1 ax0)) (flip1 (flip1 ax1)).
*)

(* OLD
Proof.
  intro X.
    (* If things computed a lot, the following would be the answer.
       For example for flip0 it just works *)
  pose (t0 := flip2 (flip1 ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x) X).
    (* since that's not the case we have to transport a couple of times.
       maybe there's a cleaner way to do this? *)
  pose (t1 := (flip1_involutive _ _ ax1) # t0).
  pose (t2 := transport (fun e => _ e ax1) (flip1_involutive _ _ ax0) t1).
  pose (t3 := transport (fun e => _ e ax0 ax1) (flip1_involutive _ _ a1x) t2).
  exact (transport (fun e => _ e a1x ax0 ax1) (flip1_involutive _ _ a0x) t3).
Defined.
*)
(*
Definition prod11_twocells_map_from_to {C D : CT1}
             {v00 v01 v10 v11 : prod11_zerocells C D}
             (a0x : prod11_onecells C D v00 v01) (a1x : prod11_onecells C D v10 v11)
             (ax0 : prod11_onecells C D v00 v10) (ax1 : prod11_onecells C D v01 v11) :
               (prod11_twocells_map_to a0x a1x ax0 ax1) o
                 (prod11_twocells_map_from a0x a1x ax0 ax1) == idmap.
Proof.
  intro X.
  induction X.
  pose (t0 := flip2_involutive (flip1  ax0) (flip1 ax1) (flip1 a0x) (flip1 a1x) X).
  unfold prod11_twocells_map_from in t0.
    induction X.
  rewrite (transport_arrow _ _ _) in t0.
  rewrite (flip1_involutive _ _ ax1) in t0.
  pose (t1 := transport (fun e => (_ e _) = X) (flip1_involutive _ _ ax1) t0).
  pose (t2 := transport (fun e => _ e ax1) (flip1_involutive _ _ ax0) t1).
  pose (t3 := transport (fun e => _ e ax0 ax1) (flip1_involutive _ _ a1x) t2).
  exact (transport (fun e => _ e a1x ax0 ax1) (flip1_involutive _ _ a0x) t3).
 
  unfold prod11_twocells_map_from.
  rewrite (flip1_involutive _ _ ax1).

  induction X.

  pose (t1 := (flip1_involutive _ _ ax1) # t0).
  rewrite (flip1_involutive _ _ ax1) in t0.
  rewrite (flip1_involutive _ _ a1x) in test.
  rewrite (flip1_involutive _ _ a0x) in test.
  pose (t1 := (flip1_involutive _ _ ax1)^ # t0).
  exact test.
  intro X. induction X. trivial.
  


  pose (X' := transport (fun e => prod11_twocells _ _ _ _ _ _ _ _ _
                                    (prod11_onecells_map_to _ _ e))
                        (flip1_involutive _ _ a1x)^ X).
  pose (X'' := transport (fun e => prod11_twocells _ _ _ _ _ _ _ _
                                    (prod11_onecells_map_to _ _ e) _)
                        (flip1_involutive _ _ a0x)^ X').
  pose (X''' := transport (fun e => prod11_twocells _ _ _ _ _ _ _
                                    (prod11_onecells_map_to _ _ e) _ _)
                        (flip1_involutive _ _ ax1)^ X'').
  pose (X'''' := transport (fun e => prod11_twocells _ _ _ _ _ _
                                    (prod11_onecells_map_to _ _ e) _ _ _)
                        (flip1_involutive _ _ ax0)^ X''').
  simpl in X''''.
*)

(* product is commutative, unfinished

*)

