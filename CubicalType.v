Require Import HoTT.


(* TODO:
     - (co)limit
     - composition of diagram morphisms (missing 2-diagrams)
     - product is commutative (unfinished)
     - consistent names
*)

(*** 1, 2 and 3-semi-cubical types *)

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





(***  1,2,3-CT morphisms *)

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

Coercion CT2mtoCT1m {C D : CT2} (m : CT2_morphism C D) : CT1_morphism C D :=
  (m.1 ; m.2.1).

Coercion CT3mtoCT2m {C D : CT3} (m : CT3_morphism C D) : CT2_morphism C D :=
  (m.1 ; (m.2.1 ; m.2.2.1)).



  (* composition of morphisms *)

Definition CT1_morphism_comp {C D E : CT1}
             (F : CT1_morphism C D) (G : CT1_morphism D E) : CT1_morphism C E.
Proof.
  exists (G.1 o F.1).
  intro c0. intro c1.
  exact ( (G.2 (F.1 c0) (F.1 c1)) o (F.2 _ _) ).
Defined.
(* why doesn't this work?
  exact ( (G.1 o F.1 ; fun c0 c1 => (G.2 (F.1 c0) (F.1 c1)) o (F.2 _ _)) ).
*)

Definition CT2_morphism_comp {C D E : CT2}
             (F : CT2_morphism C D) (G : CT2_morphism D E) : CT2_morphism C E.
Proof.
  exists ((CT1_morphism_comp F G).1).
  exists ((CT1_morphism_comp F G).2).
  intros v00 v01 v10 v11 ax0 ax1 a0x a1x c.
  exact (G.2.2 _ _ _ _ _ _ _ _ (F.2.2 _ _ _ _ _ _ _ _ c)).
Defined.

Definition CT3_morphism_comp {C D E : CT3}
             (F : CT3_morphism C D) (G : CT3_morphism D E) : CT3_morphism C E.
Proof.
  exists ((CT2_morphism_comp F G).1).
  exists ((CT2_morphism_comp F G).2.1).
  exists ((CT2_morphism_comp F G).2.2).
  intros v000 v001 v010 v011 v100 v101 v110 v111.
  intros a00x a01x a10x a11x a0x0 a0x1 a1x0 a1x1 ax00 ax01 ax10 ax11.
  intros f0xx f1xx fx0x fx1x fxx0 fxx1.
  intro c.
  exact (G.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (F.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c)).
Defined.






(*** identity types of [CT1] and [CT2] *)


  (* this is what we usually know how to construct *)
Definition combinatorial_arrows_path {C0 D0 : Type}
             (C1 : combinatorial_arrows C0) (D1 : combinatorial_arrows D0)
             (p0 : C0 <~> D0) : Type :=
  forall v0 v1, C1 (p0^-1 v0) (p0^-1 v1) <~> D1 v0 v1.

Definition combinatorial_squares_path {C0 D0 : Type}
             {C1 : combinatorial_arrows C0} {D1 : combinatorial_arrows D0}
             (C2 : combinatorial_squares C1) (D2 : combinatorial_squares D1)
             {p0 : C0 <~> D0} (p1 : combinatorial_arrows_path C1 D1 p0)
               : Type :=
  forall v00 v01 v10 v11 : D0,
  forall a0x : D1 v00 v01, forall a1x : D1 v10 v11,
  forall ax0 : D1 v00 v10, forall ax1 : D1 v01 v11,
    C2 _ _ _ _ ((p1 v00 v01)^-1 a0x) ((p1 v10 v11)^-1 a1x)
               ((p1 v00 v10)^-1 ax0) ((p1 v01 v11)^-1 ax1) <~>
    D2 _ _ _ _ a0x a1x ax0 ax1.

Definition CT1_combinatorial_eq (C D : CT1) : Type :=
  {p0 : C.1 <~> D.1 & combinatorial_arrows_path C.2 D.2 p0}.

Definition CT2_combinatorial_eq (C D : CT2) : Type :=
  { p0 : C.1 <~> D.1 &
  { p1 : combinatorial_arrows_path C.2.1 D.2.1 p0 &
         combinatorial_squares_path C.2.2 D.2.2 p1
  }}.


  (* How transport works for fibrations [C0 -> C0 -> Type] *)
Definition transport_arrows `{Univalence}
             (C : CT1) (D : Type) (p0 : C.1 <~> D) :
             forall x y : D,
               transport (fun C0 : Type => combinatorial_arrows C0)
                         (path_universe_uncurried p0) C.2 x y =
               C.2 (p0^-1 x) (p0^-1 y).
Proof.
    (* It would be very useful to have a rewrite-like tactic for these things *)
  pose (t0' := fun x => transport_arrow _ _ _ :
     transport (fun C0 : Type => combinatorial_arrows C0)
               (path_universe_uncurried p0) C.2 x =
     transport (fun x0 : Type => x0 -> Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x))).    
  pose (t0 := fun x y => ap (fun f => f y) (t0' x)).
  
  pose (t1 := fun x y => transport_arrow _ _ _ :
     transport (fun x0 : Type => x0 -> Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x)) y =
     transport (fun _ : Type => Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x)
               (transport idmap (path_universe_uncurried p0)^ y))).
  
  pose (t2 := fun x y => transport_const _ _ :
     transport (fun _ : Type => Type) (path_universe_uncurried p0)
     (C.2 (transport idmap (path_universe_uncurried p0)^ x)
          (transport idmap (path_universe_uncurried p0)^ y)) =
     (C.2 (transport idmap (path_universe_uncurried p0)^ x)
          (transport idmap (path_universe_uncurried p0)^ y))).

  pose (t3' := fun x => transport_path_universe_V_uncurried _ _ :
     (transport idmap (path_universe_uncurried p0)^ x) =
     (p0^-1 x)).

  pose (t3 := fun x y => ap (fun e =>
                    C.2 e (transport idmap (path_universe_uncurried p0)^ y))
                          (t3' x)).

  pose (t4' := fun y => transport_path_universe_V_uncurried _ _ :
                 (transport idmap (path_universe_uncurried p0)^ y) =
                 (p0^-1 y)).

  pose (t4 := fun x y => ap (fun e => C.2 (p0^-1 x) e) (t4' y)).

  exact (fun x y => (t0 x y) @ (t1 x y) @ (t2 x y) @ (t3 x y) @ (t4 x y)).
Defined.



  (* this is the key equivalence needed to characterize the pathspaces in [CT1] (and [CTn]) *)
  (* todo: find a better name *)
Definition arrows_path `{Univalence}
             (C D : CT1) (p0 : C.1 <~> D.1) :
               combinatorial_arrows_path C.2 D.2 p0 <~>
               transport (fun C0 : Type => combinatorial_arrows C0)
                         (path_universe_uncurried p0) C.2 = D.2.
Proof.

    (* we have to prove an equivalence [S <~> T], where [T] is an equality
       between dependent functions. We know this is equivalent to a pointwise
       equivalence *)
  pose (pointwise2 :=
  equiv_functor_forall_id (fun x => equiv_path_forall _ _) :
   (forall x : D.1,
    transport (fun C0 : Type => combinatorial_arrows C0)
      (path_universe_uncurried p0) C.2 x == D.2 x)
     <~>
       transport (fun C0 : Type => combinatorial_arrows C0)
     (path_universe_uncurried p0) C.2 == D.2
  ).
    (* [equiv_path_arrow] does the job for the first argument [x],
       then we use [pointwise2] for the second argument [y] *)
  simple refine ((equiv_path_arrow _ _) oE pointwise2 oE _).


    (* now, the [transport ...] can actually be computed, since it
       is a transport over an explicit equivalence. *)
  pose (t0 := transport_arrows C D.1 p0).

    (* [equiv_functor_forall_id] says that a two equivalent fibrations
       induce equivalent Π-types. 
       Since the transport that we know how to compute lives inside two
       [forall] so we use [equiv_functor_forall_id] twice. *)
  pose (t1 :=
    equiv_functor_forall_id (fun x =>
      equiv_functor_forall_id (fun y =>
        equiv_path _ _ (ap (fun e => e = D.2 x y) (t0 x y))))).
  
  simple refine ((equiv_inverse t1) oE _).

    (* finally, the definition of [combinatorial_arrows_path] asks us to
       give pointwise equivalences, but this is the same as pointwise
       equalities, again everything lives inside two [forall] *)
  pose (t' :=
    equiv_functor_forall_id (fun x =>
      equiv_functor_forall_id (fun y => equiv_path_universe _ _)) :
   (forall v0 v1 : D.1, C.2 (p0^-1 v0) (p0^-1 v1) <~> D.2 v0 v1) <~>
   (forall v0 v1 : D.1, C.2 (p0^-1 v0) (p0^-1 v1) = D.2 v0 v1)).
  
  exact t'.
Defined.



  (* characterization of the pathspaces of the type [1CT] *)
Definition path_CT1 `{Univalence} (C D : CT1) :
             CT1_combinatorial_eq C D <~> (C = D).
Proof.
    (* [CT1] is a sigma type, so its pathspace can be described as a sigma *)
  simple refine ((equiv_path_sigma _ C D) oE _).
    (* an equivalence between sigma types [sigT A P <~> sigT B Q] can be given by
       an equivalence [e : A <~> B] and a fiberwise equivalence [Q <~> P] *)
  simple refine (equiv_functor_sigma' (equiv_path_universe C.1 D.1) _).

  exact (arrows_path C D).
Defined.
           


  (* todo: find a better name *)
Definition squares_path `{Univalence}
  (C D : CT2) {p0 : C.1 <~> D.1} (p1 : combinatorial_arrows_path C.2.1 D.2.1 p0) :
     combinatorial_squares_path (C.2).2 (D.2).2 p1 <~>
     transport (fun C1 : combinatorial_arrows D.1 => combinatorial_squares C1)
               (arrows_path C D p0 p1)
               (transportD combinatorial_arrows (@combinatorial_squares)
                           (path_universe_uncurried p0) (C.2).1 (C.2).2) = (D.2).2.
Proof.
  admit.
  (* unfinished *)
  (* 
  rewrite (transport_arrow _ _ _).
  rewrite (transport_arrow _ _ _).
  rewrite transport_const.
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  rewrite (transport_path_universe_V_uncurried flip_equiv _).
  reflexivity.
  *)
Admitted.


  
Definition path_CT2 `{Univalence} (C D : CT2) :
             CT2_combinatorial_eq C D <~> (C = D).
Proof.
    (* idem *)
  simple refine ((equiv_path_sigma _ C D) oE _).
    (* idem *)
  simple refine (equiv_functor_sigma' (equiv_path_universe C.1 D.1) _).
  intro p0. simpl.
    (* again, the RHS is a sigma *)
  simple refine ((equiv_path_sigma _ _ _) oE _).
    (* we have to give an equivalence between the base types (of the simgas).
       This is what we needed in the CT1 case. But first, in the RHS we
       have to use a lemma about transport in sigmas *)
  (* -> *) rewrite (transport_sigma _ _). simpl.
  simple refine (equiv_functor_sigma' (arrows_path C D p0) _).
  exact (squares_path C D).
Qed.






(* OLD: this gives us a way to construct equalities in [CT1], the fact
        that this is an equivalence is the proof above 

  (* given a [combinatorial_arrows_path] we get an equality in CT1 *)
Definition path_CT1 `{Univalence} (C D : CT1)
             (p0p1 : {p0 : C.1 <~> D.1 & combinatorial_arrows_path C.2 D.2 p0}) :
               (C = D).
Proof.
  destruct p0p1 as (p0, p1).
  simple refine (path_sigma_uncurried _ _ _ _).
  exists (path_universe_uncurried p0).
  (* we prove it point-wise *)
  simple refine (path_forall _ _ _). intro x.
  simple refine (path_forall _ _ _). intro y.
  simple refine (path_universe_uncurried _).

  pose (t0' := transport_arrow _ _ _ :
     transport (fun C0 : Type => combinatorial_arrows C0)
               (path_universe_uncurried p0) C.2 x =
     transport (fun x0 : Type => x0 -> Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x))).    
  pose (t0 := ap (fun f => f y) t0').
  
  pose (t1 := transport_arrow _ _ _ :
     transport (fun x0 : Type => x0 -> Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x)) y =
     transport (fun _ : Type => Type) (path_universe_uncurried p0)
               (C.2 (transport idmap (path_universe_uncurried p0)^ x)
               (transport idmap (path_universe_uncurried p0)^ y))).
  
  pose (t3 := transport_const _ _ :
     transport (fun _ : Type => Type) (path_universe_uncurried p0)
     (C.2 (transport idmap (path_universe_uncurried p0)^ x)
          (transport idmap (path_universe_uncurried p0)^ y)) =
     (C.2 (transport idmap (path_universe_uncurried p0)^ x)
          (transport idmap (path_universe_uncurried p0)^ y))).

  pose (t4' := transport_path_universe_V_uncurried _ _ :
     (transport idmap (path_universe_uncurried p0)^ x) =
     (p0^-1 x)).

  pose (t4 := ap (fun e =>
                    C.2 e (transport idmap (path_universe_uncurried p0)^ y)) t4').

  pose (t5' := transport_path_universe_V_uncurried _ _ :
     (transport idmap (path_universe_uncurried p0)^ y) =
     (p0^-1 y)).

  pose (t5 := ap (fun e => C.2 (p0^-1 x) e) t5').

  pose (t' := t0 @ t1 @ t3 @ t4 @ t5).
  
  pose (t := ap (fun e => e <~> D.2 x y) t'). simpl in t.
  exact (transport idmap t^ (p1 x y)).
Defined.

*)
