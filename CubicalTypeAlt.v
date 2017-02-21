Require Import HoTT.


Definition s1_bound (C0 : Type) : Type :=
  C0 * C0.

Definition s1 (C0 : Type) : Type :=
  s1_bound C0 -> Type.

Definition CT1 : Type :=
  { C0 : Type & s1 C0}.

Coercion CT1toCT0 (C : CT1) : Type := C.1.

Coercion CT1tos1 (C : CT1) : s1 C.1 := C.2.


Record s2_bound (C : CT1) : Type :=
 S2b
  { v00 : C.1
  ; v01 : C.1
  ; v10 : C.1
  ; v11 : C.1
  ; ax0 : C.2 (v00 , v10)
  ; ax1 : C.2 (v01 , v11)
  ; a0x : C.2 (v00 , v01)
  ; a1x : C.2 (v10 , v11)
}.

(*
Arguments s1_bound {C0} C1.
*)


Arguments S2b {C} v00 v01 v10 v11 ax0 ax1 a0x a1x.
Arguments v00 {C} s.
Arguments v01 {C} s.
Arguments v10 {C} s.
Arguments v11 {C} s.
Arguments ax0 {C} s.
Arguments ax1 {C} s.
Arguments a0x {C} s.
Arguments a1x {C} s.


Definition s2 (C : CT1) :=
  s2_bound C -> Type.

Definition CT2 : Type :=
  { C : CT1 & s2 C}.

Coercion CT2toCT1 (C : CT2) : CT1 := C.1.

Coercion CT2tos2 (C : CT2) : s2 C.1 := C.2.

Record s3_bound (C : CT2) : Type :=
 S3b
  { v000 : C.1.1
  ; v001 : C.1.1
  ; v010 : C.1.1
  ; v011 : C.1.1
  ; v100 : C.1.1
  ; v101 : C.1.1
  ; v110 : C.1.1
  ; v111 : C.1.1
  ; a00x : C.1.2 (v000 , v001)
  ; a01x : C.1.2 (v010 , v011)
  ; a10x : C.1.2 (v100 , v101)
  ; a11x : C.1.2 (v110 , v111)
  ; a0x0 : C.1.2 (v000 , v010)
  ; a0x1 : C.1.2 (v001 , v011)
  ; a1x0 : C.1.2 (v100 , v110)
  ; a1x1 : C.1.2 (v101 , v111)
  ; ax00 : C.1.2 (v000 , v100)
  ; ax01 : C.1.2 (v001 , v101)
  ; ax10 : C.1.2 (v010 , v110)
  ; ax11 : C.1.2 (v011 , v111)
  ; f0xx : C.2 (S2b _ _ _ _ a00x a01x a0x0 a0x1)
  ; f1xx : C.2 (S2b _ _ _ _ a10x a11x a1x0 a1x1)
  ; fx0x : C.2 (S2b _ _ _ _ a00x a10x ax00 ax01)
  ; fx1x : C.2 (S2b _ _ _ _ a01x a11x ax10 ax11)
  ; fxx0 : C.2 (S2b _ _ _ _ a0x0 a1x0 ax00 ax10)
  ; fxx1 : C.2 (S2b _ _ _ _ a0x1 a1x1 ax01 ax11) }.


Arguments S3b {C} v000 v001 v010 v011 v100 v101 v110 v111
                  a00x a01x a10x a11x a0x0 a0x1 a1x0 a1x1 ax00 ax01 ax10 ax11
                  f0xx f1xx fx0x fx1x fxx0 fxx1.
 
Definition s3 (C : CT2) : Type :=
   s3_bound C -> Type.

Definition CT3 : Type :=
  { C : CT2 & s3 C }.


Coercion CT3toCT2 (C : CT3) : CT2 := C.1.
Coercion CT3tos3 (C : CT3) : s3 C.1 := C.2.



  (* identity types *)

Definition s1b_map {C0 D0 : Type} (M0 : C0 -> D0)
             (v : s1_bound C0) : s1_bound D0 :=
  let (v0 , v1) := v in (M0 v0 , M0 v1).


(* are these useful? *)
Definition s1b_Dmap {C0 : Type} {D0 : C0 -> Type}
             (M0 : forall c : C0, D0 c)
             (v : s1_bound C0) : s1_bound (sigT D0) :=
  ((fst v ; M0 (fst v)),
   (snd v ; M0 (snd v))). 

Definition s1b_map_funct_comp {C0 D0 E0 : Type}
             (M0 : C0 -> D0) (N0 : D0 -> E0) :
             (s1b_map N0) o (s1b_map M0) == (s1b_map (N0 o M0)) :=
  fun v => match v with
             | _ => idpath _
           end.

Definition s1b_map_htpy_invariant {C0 D0 : Type}
             {M0 N0 : C0 -> D0} (h : M0 == N0) :
               s1b_map M0 == s1b_map N0 :=
  fun v => let (v0, v1) := v in
               (path_prod (M0 v0, M0 v1) (N0 v0, N0 v1) (h v0) (h v1)).


(*
Definition s1b_map_ap {C0 D0 : Type}
             (M0 : C0 -> D0) {b1 b2 : s1_bound C0}
             (p : b1 = b2) : ap (s1b_map M0) p =
*)


(* is this useful? *)
Definition s1b_equiv `{Univalence}
             {C0 D0 : Type} (M0 : C0 <~> D0) :
             IsEquiv (s1b_map M0).
Proof.
  destruct M0 as (M0,eM0).
  destruct eM0 as (inv,retr,sect,adj).
  refine (isequiv_biinv _ _).
    - refine ((s1b_map inv ; _), (s1b_map inv ; _) ).
      * intro. refine (s1b_map_funct_comp _ _ _ @ _).
        exact (s1b_map_htpy_invariant sect x).
      * intro. refine (s1b_map_funct_comp _ _ _ @ _).
        exact (s1b_map_htpy_invariant retr x).
Defined.
 (* *)


Definition s1_morph {C0 D0 : Type}
             (C1 : s1 C0) (D1 : s1 D0)
             (M0 : C0 -> D0) : Type :=
  forall v : s1_bound C0, C1 v -> D1 (s1b_map M0 v).


(* is this useful? *)
Definition s1_morph' {C0 : Type} (C1 D1 : s1 C0) : Type :=
  forall v : s1_bound C0, C1 v -> D1 v.


Definition CT1_morph (C D : CT1) : Type :=
  {p0 : C.1 -> D.1 & s1_morph C.2 D.2 p0}.


Definition s1_equiv {C0 D0 : Type}
             (C1 : s1 C0) (D1 : s1 D0)
             (M0 : C0 -> D0) : Type :=
  forall v : s1_bound C0, C1 v <~> D1 (s1b_map M0 v).


(* is this useful? *)
Definition s1_equiv' {C0 : Type} (C1 D1 : s1 C0) : Type :=
  forall v : s1_bound C0, C1 v <~> D1 v.


Definition CT1_equiv (C D : CT1) :=
  { p0 : C.1 <~> D.1 & s1_equiv C D p0 }.


Coercion CT1_equiv_to_morph {C D : CT1} :
          CT1_equiv C D -> CT1_morph C D.
Proof.
  intro e. exists e.1. exact e.2.
Defined.



Definition s2b_map {C D : CT1} (M : CT1_morph C D)
             (a : s2_bound C) : s2_bound D :=
  S2b (M.1 a.(v00)) (M.1 a.(v01)) (M.1 a.(v10)) (M.1 a.(v11))
      (M.2 _ a.(ax0)) (M.2 _ a.(ax1)) (M.2 _ a.(a0x)) (M.2 _ a.(a1x)).


Definition s2_morph (C D : CT2) (p1 : CT1_morph C.1 D.1) : Type :=
  forall a : s2_bound C,
    C.2 a -> D.2 ((s2b_map p1) a).
 
Definition s2_equiv (C D : CT2) (p1 : CT1_equiv C.1 D.1) : Type :=
  forall a : s2_bound C,
    C.2 a <~> D.2 ((s2b_map (CT1_equiv_to_morph p1)) a).
  (* for some reason we have to coerce manually there *)
 

Definition CT2_equiv (C D : CT2) : Type :=
  { p1 : CT1_equiv C D & s2_equiv C D p1}.



  (* find better name *)
Definition transport_s1 `{Univalence}
             (C : Type) (D : CT1) (p0 : C <~> D.1) (v : s1_bound C) :
               transport s1 (path_universe_uncurried p0)^ D.2 v =
               D.2 (s1b_map p0 v).
Proof.
  destruct D as (D0, D1). revert p0. equiv_intro (equiv_path C D0) p.
  pose (t0 := ap (fun e => transport s1 e^ D1 v) (eta_path_universe_uncurried p)).
  refine (t0 @ _).
  induction p.
  reflexivity.
Defined.
(*
  pose (t0 := fun v => transport_arrow _ _ _ :
     transport (fun C0 : Type => s1 C0)
               (path_universe_uncurried p0)^ D.2 v =
     transport (fun x0 : Type => Type) (path_universe_uncurried p0)^
               (D.2 (transport _ (path_universe_uncurried p0)^^ v))).    

 
  pose (t1 := fun v => transport_const _ _ :
     transport (fun _ : Type => Type) (path_universe_uncurried p0)^
               (D.2 (transport s1_bound ((path_universe_uncurried p0)^)^ v)) =
               (D.2 (transport s1_bound ((path_universe_uncurried p0)^)^ v))).
  
  pose (t2 := fun v => ap (fun e => D.2 (transport s1_bound e v))
                                        (inv_V (path_universe_uncurried p0))).
 
  pose (t3 := fun v => ap D.2 (transport_s1_bound C D p0 v)).

  exact (t0 v @ t1 v @ t2 v @ t3 v).
*)


Definition transport_s1_on_id `{Univalence}
             (C : CT1) (v : s1_bound C) :
               transport_s1 C C (equiv_path C.1 C.1 1) v =
                 ap (fun e => transport s1 e^ C.2 v)
                   (eta_path_universe_uncurried (idmap _)).
Proof.
  destruct C as (C0 , C1).
  unfold transport_s1.
  unfold equiv_ind. simpl.
  unfold eta_path_universe_uncurried.
Admitted.
(*
  generalize (path_universe_uncurried (equiv_path C.1 C.1 1)).
  intro p.
  induction p.
  simpl.
*)



Definition transport_s1'
             (C : Type) (D : CT1) (p0 : D.1 = C) (v : s1_bound C) :
               transport s1 p0 D.2 v =
               D.2 (s1b_map (transport idmap p0^) v).
Proof.
  by induction p0.
Defined.

Definition transport_s1'' `{Univalence}
             (C : Type) (D : CT1) (p0 : C <~> D.1) (v : s1_bound C) :
               transport s1 (path_universe_uncurried p0)^ D.2 v =
               D.2 (s1b_map p0 v).
Proof.
  pose (t0 := transport_s1' C D (path_universe_uncurried p0)^ v).
  refine (t0 @ _).
  clear t0.
  refine (ap D.2 _).
  refine (ap (fun e => (s1b_map (transport idmap e) v)) (inv_V _) @ _ ).
  revert v.
  exact (s1b_map_htpy_invariant (transport_path_universe_uncurried p0)).
Defined.




Definition transport_s1''_on_id `{Univalence}
             (C : CT1) (v : s1_bound C) :
               transport_s1'' C C (equiv_path C.1 C.1 1) v =
                 ap (fun e => transport s1 e^ C.2 v)
                   (eta_path_universe_uncurried (idmap _)).
Proof.
  unfold transport_s1''.
  unfold transport_path_universe_uncurried.
  unfold eta_path_universe_uncurried.
  simpl.
Admitted.


(*
Definition transport_s1''_on_id `{Univalence}
             (C : Type) (D : CT1) (p : C = D.1) (v : s1_bound C) :
               transport_s1'' C D (equiv_path C D.1 p) v =
                 ap (fun e => transport s1 e^ D.2 v)
                   (eta_path_universe_uncurried p) @
                 transport_arrow _ _ _.
*)
 


(*** the rest is OK. todo: rewrite -> transport ***)

Definition s1_equiv_is_path `{Univalence}
             (C D : CT1) (p0 : C.1 <~> D.1) :
               s1_equiv C D p0 <~>
               (C.2 = transport s1 (path_universe_uncurried p0)^ D.2).
Proof.
    (* we have to prove an equiv [S <~> T], where [T] is an equality
       between dependent functions. We know this is equivalent to a pointwise
       equiv *)
  simple refine ((equiv_path_arrow _ _) oE _).
  
    (* now, the [transport ...] can actually be computed, since it
       is a transport over an explicit equivalence. *)
  pose (t0 := transport_s1'' C D p0).

    (* [equiv_functor_forall_id] says that a two equivalent fibrations
       induce equivalent Π-types. *)
  pose (t1 :=
    equiv_functor_forall_id (fun v =>
      equiv_path _ _ (ap (fun e => C.2 v = e) (t0 v)))).
  simple refine (t1^-1 oE _).

  exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
Defined.



Definition CT1_equiv_is_path `{Univalence} (C D : CT1) :
             CT1_equiv C D <~> (C = D).
Proof.
    (* [CT1] is a sigma type, so its pathspace can be described as a sigma *)
  simple refine ((equiv_path_sigma_contra _ C D) oE _).
    (* an equivalence between sigma types [sigT A P <~> sigT B Q] can be given by
       an equivalence [e : A <~> B] and a fiberwise equivalence [Q <~> P] *)
  simple refine (equiv_functor_sigma' (equiv_path_universe C.1 D.1) _).

  exact (s1_equiv_is_path C D).
Defined.


(* the trivial equivalence *)
Definition CT1_idequiv (C : CT1) : CT1_equiv C C :=
  ( equiv_idmap C.1 ; fun v => match v with
                                 | _ => equiv_idmap
                               end ).

(* find a better name or just put this inside the proof below *)
Lemma cancel_ `{Univalence} (C : CT1) (v : s1_bound C.1)
                 (T : (equiv_path C.1 C.1)^-1 (equiv_path C.1 C.1 1) = idpath _) :
  transport idmap
    (ap (fun e : Type => C.2 v = e) (ap (fun e : C.1 = C.1 => transport s1 e^ C.2 v) T))
        (apD10 (transport (fun p : C.1 = C.1 => C.2 = transport s1 p^ C.2)
                          T^ (idpath _)) v) = idpath.
Proof.
  rewrite <- (inv_V T).
  induction T^.
  reflexivity.
Qed.


Definition test (C : Type) : equiv_path C C idpath = 1%equiv := idpath.

(* find better name *)
Definition CT1_equiv_is_path_on_id `{Univalence} (C : CT1) :
             ((CT1_equiv_is_path C C)^-1 (idpath _)) = CT1_idequiv C.
Proof.
  simple refine (path_sigma _ _ _ _ _).
    - reflexivity.
    - unfold transport.
      refine (path_forall _ _ _).
      intro v. simpl.
      unfold functor_forall.
      
      (* how to rewrite as? something like:
        rewrite (1%equiv) as (equiv_path (C v) (C v) 1).
      *)
      rewrite (test _)^.
      refine (ap (equiv_path _ _) _).
      rewrite concat_1p.
      rewrite transport_s1''_on_id.
      unfold eta_path_universe_uncurried.
      apply cancel_.
Qed.


Definition transport_s2_bound `{Univalence}
             (C : CT1) (D : CT1) (D2 : s2 D) (p1 : CT1_equiv C D) (a : s2_bound C) :
               transport s2_bound ((CT1_equiv_is_path C D) p1) a =
               s2b_map (CT1_equiv_to_morph p1) a.
Proof.
  revert p1. equiv_intro (CT1_equiv_is_path C D)^-1 p. induction p.
  rewrite eisretr.
  rewrite CT1_equiv_is_path_on_id.
  destruct a.
  reflexivity.
Qed.

 
Definition transport_s2 `{Univalence}
             (C : CT1) (D : CT2)
             (p1 : CT1_equiv C D) (a : s2_bound C) :
    transport s2 (CT1_equiv_is_path C D p1)^ D.2 a =
    D.2 (s2b_map (CT1_equiv_to_morph p1) a).
Proof.
  rewrite transport_arrow. rewrite transport_const.
  rewrite (inv_V _).
  refine (ap D.2 _).
  exact (transport_s2_bound C D.1 D.2 _ a).
Qed.


Definition s2_equiv_is_path `{Univalence}
  (C D : CT2) (p1 : CT1_equiv C D) :
   s2_equiv C D p1 <~>
   (C.2 = transport s2 (CT1_equiv_is_path C.1 D.1 p1)^ D.2).
Proof.
    (* idem *)
  simple refine ((equiv_path_forall _ _) oE _).

  pose (t0 := transport_s2 C D p1).
  pose (t1 :=
    equiv_functor_forall_id (fun a =>
      equiv_path _ _ (ap (fun e => C.2 a = e) (t0 a)))).
  simple refine (t1^-1 oE _).

    (* idem *)
  exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
Defined.


Definition CT2_equiv_is_path `{Univalence} (C D : CT2) :
             CT2_equiv C D <~> (C = D).
Proof.
    (* idem *)
  simple refine ((equiv_path_sigma_contra _ C D) oE _).
    (* idem *)
  simple refine (equiv_functor_sigma' (CT1_equiv_is_path C.1 D.1) _).
  intro p1.
  apply s2_equiv_is_path.
Defined.





































(********************************************* *)

(** these are some auxiliar functions that might help proving
   the characterization of paths in [CT2] *)

Definition uncurryD {A : Type} {B : A -> Type} (C : forall a : A, B a -> Type) :
                      sigT B -> Type :=
  fun ab => match ab with
              | (a ; b) => C a b
            end.


Definition transportD_is_transport_uncurried 
           {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
           (x1 x2:A) (p:x1=x2) (y:B x1) (z:C x1 y)
: transportD B C p y z
  = transport (uncurryD C) (path_sigma' B p 1) z.
Proof.
  destruct p. reflexivity.
Defined.

Definition transp_proj1_commute {A : Type} (B : A -> Type) (C : forall a, B a -> Type)
                     {x y : A} (p : x = y) (s : {b : B x & C x b}) :
                       (transport (fun a => {b : B a & C a b }) p s).1 =
                        transport B p s.1.
Proof.
  destruct p. reflexivity.
Defined.

Definition transportD_arrow_toconst
  {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type} {D : Type}
  {a1 a2 : A} (p : a1 = a2) (b1 : B a1) (f : C a1 b1 -> D) (y : C a2 (p # b1))
  : (transportD B (fun a b => C a b -> D) p b1 f) y =
    f ((transport_Vp B p b1) # transportD _ _ p^ _ y).
Proof.
  destruct p; simpl; auto.
Defined.


(**)


Local Open Scope path_scope.


Definition path_universe_1_ `{Univalence} {A : Type} 
: (path_universe_uncurried 1)^ = (1 : A = A).
Proof.
  rewrite (eta_path_universe_uncurried 1).
  reflexivity.
Defined.




(*
Definition transport_s2_bound `{Univalence}
  {C : CT1} (D : CT2)
  (p0 : C.1 <~> D) (p1 : s1_equiv C D p0)
  (a : s2_bound C.2) :
    (transport s2_bound ((s1_equiv_is_path C D p0) p1) a) =
    (transportD _ (@s2_bound) (path_universe_uncurried p0)^ _ (s2b_map p1 a)).
Proof.
  destruct D as (D0 , D1).
  revert p1. revert p0. equiv_intro (equiv_path C.1 D0) p. induction p.
  intro p1.
  simpl.
  simple refine (_ @ (ap (fun e => transportD s1 (@s2_bound) e^ (C.1 ; D1).2
                                (s2b_map p1 a))
                         (path_universe_uncurried_equiv_path _)^)).

  rewrite (path_universe_uncurried_equiv_path _).

  pose (t0 := (path_forall C.2
        (transport s1
           (path_universe_uncurried p0)^
           (D.2).1)
        (functor_forall idmap
           (fun (x : s1_bound C.1)
              (y : C.2 x =
                   (D.2).1
                     (s1b_map p0 x)) =>
            transport idmap
              (ap
                 (fun e : Type =>
                  C.2 x = e)
                 (ap10
                    (transport_s1 C D p0)
                    x))^ y)
           (functor_forall idmap
              (fun a0 : s1_bound C.1 =>
               path_universe_uncurried)
              p1)))).

  refine (s1_equiv_induction' C (fun D0 p0 D1 p1 => 
                   (transport s2_bound ((s1_equiv_is_path C (D0 ; D1) p0) p1) a) =
                   (transportD _ (@s2_bound) (path_universe_uncurried p0)^ _ (s2b_map p1 a))) _ D.1 p0 D.2.1 p1).
  clear p1 p0 D.
  intros.
  simpl.
  rewrite transport_forall.
  destruct a.
  simpl.
  rewrite (eta_path_universe_uncurried 1).
  rewrite path_universe_1_.
  simpl.
 

(*
  refine (_ @ (ap (fun e => transportD s1 (@s2_bound) e C.2 _ _) (path_universe_1_)^)).
  rewrite path_universe_uncurried_
  destruct a.
  unfold s2b_map.
  simpl.
  rewrite ap_functor_forall.
  rewrite transport_arrow.
  rewrite transport_const.
  destruct a.
  unfold s2b_map.
  simpl.
  rewrite transportD_arrow_toconst.

  revert a. revert D2. revert p1. revert D1. revert p0. revert D0.
  refine (s1_equivalence_induction C (fun D0 p0 D1 p1 => _) _).
  intros.
  refine (ap D2 _). simpl. 
  rewrite transport_forall.

  rewrite path_universe_uncurried_equiv_path.
  

  revert p1. revert p0. equiv_intro (equiv_path C.1 D0) p. induction p.
  intro p1.

  rewrite transportD_arrow_toconst.
  rewrite transport_arrow.
  rewrite transport_const.
  
  pose (test' := transportD s1 (@s2) (path_universe_uncurried p0)^ D1 D2).
  
  pose (test :=(transport s2_bound ((s1_equivalence_is_path C (D0; D1) p0) p1) a)).
  
  rewrite transportD_is_transport_uncurried.
  (*
  rewrite (transport_s1 C (D0 ; D1)).
  *)
  simpl.
*)


Admitted.


(* this is the key lemma I still don't know how to prove *)

Definition transport_s1_equiv_is_path `{Univalence}
  {C : CT1} (D : CT2)
  (p0 : C.1 <~> D) (p1 : s1_equiv C D p0)
  (a : s2_bound C.2) :
   transport s2_bound
     (transport_Vp s1 (path_universe_uncurried p0)^ (D.2).1)
     (transportD s1 (@s2_bound) ((path_universe_uncurried p0)^)^
        (transport s1 (path_universe_uncurried p0)^ (D.2).1)
        (transport s2_bound ((s1_equiv_is_path C D p0) p1) a)) =
   s2b_map p1 a.
Proof.
  rewrite transport_s2_bound.
  (*
  rewrite transport_s2_bound. 
  pose (test :=(transport s2_bound ((s1_equivalence_is_path C D p0) p1) a)).
  pose (test'' := s2b_map p1 a).
  pose (test''' := transportD _ (@s2_bound) (path_universe_uncurried p0)^ _ (s2b_map p1 a)).
  pose (test' :=(transportD s1 (@s2_bound) ((path_universe_uncurried p0)^)^
        (transport s1 (path_universe_uncurried p0)^ (D.2).1)
        (transport s2_bound ((s1_equivalence_is_path C D p0) p1) a))).
  *)
Admitted.





(* the rest is OK, assuming the lemma *)



*)




(********************************************* *)








(*
Coercion s1_equivalence'_equivalence {C0 : Type} (C1 D1 : s1 C0)
           (p1 : s1_equivalence' C1 D1) :
             s1_equivalence (C0 ; C1) (C0 ; D1) (equiv_idmap C0) := p1.

Coercion s1_equivalence_equivalence' (C : CT1) (D1 : s1 C.1)
           (p1 : s1_equivalence C (C.1; D1) (equiv_path C.1 C.1 1)) :
             s1_equivalence' C.2 D1 := p1.
*)


(*
(* the trivial equivalence *)
Definition s1_idpath (C : CT1) : s1_equivalence C C equiv_idmap.
Proof.
  intro. simpl. destruct v.
  unfold s1b_map.
  exact equiv_idmap.
Defined.
*)

(*
Definition s1_equivalence_induction' `{Univalence}
  (C : CT1)
  (P : forall (D0 : Type),
       forall (p0 : C.1 <~> D0), forall (D1 : s1 D0),
       forall (p1 : s1_equivalence C (D0; D1) p0), Type) :
  (forall D1 : s1 C.1, forall p1 : s1_equivalence' C.2 D1,
   P C.1 equiv_idmap D1 p1) ->
    forall D0, forall p0, forall D1, forall p1, P D0 p0 D1 p1.
Proof.
  intro P_id.
  intro D0.
  equiv_intro (equiv_path C.1 D0) p. induction p.
  exact P_id.
Defined.
*)



(*
Definition s1_equivalence_induction' `{Univalence}
  (C : CT1)
  (P : forall (D0 : Type),
       forall (p0 : C.1 <~> D0), forall (D1 : s1 D0),
       forall (p1 : s1_equivalence C (D0; D1) p0), Type) :
  P C.1 equiv_idmap C.2 (s1_idpath C) ->
    forall D0, forall p0, forall D1, forall p1, P D0 p0 D1 p1.
Proof.
  intro P_id.
  intros.
  revert p1.
  revert p0.
  equiv_intro (equiv_path C.1 D0) p. induction p.
  intro p1.
  pose (t0 := fun v => p1 v).
Admitted.
(*
  destruct p1.
  revert p0. equiv_intro (equiv_path C D.1) p. induction p.
  simple refine (ap (fun e => transport s1_bound e v)
                    (path_universe_uncurried_equiv_path _) @ _).
  by induction v.
*)
*)



(*********************************************** ************************************)



(*
Definition transport_s1_bound `{Univalence}
             (C D : Type) (p0 : C <~> D) (v : s1_bound C) :
               (transport s1_bound (path_universe_uncurried p0) v) = s1b_map p0 v.
Proof.
  revert p0. equiv_intro (equiv_path C D) p. induction p.
  simple refine (ap (fun e => transport s1_bound e v)
                    (path_universe_uncurried_equiv_path _) @ _).
  by induction v.
Defined.

Definition transport_s1_bound_on_id `{Univalence}
             (C : Type) (v : s1_bound C) :
               transport_s1_bound C C (equiv_path C C 1) v =
               ap (fun e => transport s1_bound e v)
               (eta_path_universe_uncurried (idmap _)).
Proof.
Admitted.
(*
  unfold transport_s1_bound.
  unfold equiv_ind.
  rewrite (eissect (equiv_path C C)).
  simpl.
*)
*)


(*
Definition test' `{Univalence}
             (C : CT1) (v : s1_bound C) :
               s1b_map (equiv_path C.1 C.1 1) v = v.
Proof. reflexivity. Defined.
*)


(*
Definition transport_s1_on_path `{Univalence}
             (C : CT1) (D0 : Type) (D1 : s1 D0) (p : C.1 = D0) (v : s1_bound C) :
               transport_s1 C (D0 ; D1) (equiv_path C.1 D0 p) v =
                 ap (fun e => transport s1 e^ C.2 v)
                   (eissect (equiv_path C.1 D0) p).
*)



















(*
Definition transport_s1_on_id_ `{Univalence}
             (C : CT1) (v : s1_bound C) :
   ((transport_arrow (path_universe_uncurried (equiv_path C.1 C.1 1))^ C.2 v @
     transport_const (path_universe_uncurried (equiv_path C.1 C.1 1))^
       (C.2
          (transport s1_bound
             ((path_universe_uncurried (equiv_path C.1 C.1 1))^)^ v))) @
    ap (fun e : C.1 = C.1 => C.2 (transport s1_bound e v))
      (inv_V (path_universe_uncurried (equiv_path C.1 C.1 1))))
    =
   ap (fun e : C.1 = C.1 => transport s1 e^ C.2 v) (eta_path_universe_uncurried 1) @
   (ap C.2 (ap (fun e : C.1 = C.1 => transport s1_bound e v)
           (eta_path_universe_uncurried 1)))^.
Proof.
  pose (t0 :=((transport_arrow (path_universe_uncurried (equiv_path C.1 C.1 1))^ C.2 v @
     transport_const (path_universe_uncurried (equiv_path C.1 C.1 1))^
       (C.2
          (transport s1_bound
             ((path_universe_uncurried (equiv_path C.1 C.1 1))^)^ v))) @
    ap (fun e : C.1 = C.1 => C.2 (transport s1_bound e v))
      (inv_V (path_universe_uncurried (equiv_path C.1 C.1 1))))).
  unfold path_universe_uncurried.
  unfold eta_path_universe_uncurried.
Admitted.
(*
  rewrite (eissect (equiv_path C.1 C.1)).
  rewrite eta_path_universe_uncurried.
*)
*)

  
(*
Definition lemma'' `{Univalence}
             (C : CT1) (v : s1_bound C) (p : C = C) :
((transport_arrow (path_universe_uncurried (equiv_path C.1 C.1 1))^ C.2 v @
     transport_const (path_universe_uncurried (equiv_path C.1 C.1 1))^
       (C.2
          (transport s1_bound
             ((path_universe_uncurried (equiv_path C.1 C.1 1))^)^ v))) @
    ap (fun e : C.1 = C.1 => C.2 (transport s1_bound e v))
      (inv_V (path_universe_uncurried (equiv_path C.1 C.1 1)))) = idpath _.

*)

