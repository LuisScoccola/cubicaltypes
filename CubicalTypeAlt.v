Require Import HoTT.


Definition s1_bound (C0 : Type) : Type :=
  C0 * C0.

Definition s1 (C0 : Type) : Type :=
  s1_bound C0 -> Type.

Record s2_bound {C0 : Type} (C1 : s1 C0) : Type :=
 S2b
  { v00 : C0
  ; v01 : C0
  ; v10 : C0
  ; v11 : C0
  ; ax0 : C1 (v00 , v10)
  ; ax1 : C1 (v01 , v11)
  ; a0x : C1 (v00 , v01)
  ; a1x : C1 (v10 , v11)
}.

(*
Arguments s1_bound {C0} C1.
*)


Arguments S2b {C0} {C1} v00 v01 v10 v11 ax0 ax1 a0x a1x.

Arguments v00 {C0} {C1} s.
Arguments v01 {C0} {C1} s.
Arguments v10 {C0} {C1} s.
Arguments v11 {C0} {C1} s.
Arguments ax0 {C0} {C1} s.
Arguments ax1 {C0} {C1} s.
Arguments a0x {C0} {C1} s.
Arguments a1x {C0} {C1} s.


Definition s2 {C0 : Type} (C1 : s1 C0) :=
  s2_bound C1 -> Type.

Record s3_bound {C0 : Type} {C1 : s1 C0} (C2 : s2 C1) : Type :=
 S3b
  { v000 : C0
  ; v001 : C0
  ; v010 : C0
  ; v011 : C0
  ; v100 : C0
  ; v101 : C0
  ; v110 : C0
  ; v111 : C0
  ; a00x : C1 (v000 , v001)
  ; a01x : C1 (v010 , v011)
  ; a10x : C1 (v100 , v101)
  ; a11x : C1 (v110 , v111)
  ; a0x0 : C1 (v000 , v010)
  ; a0x1 : C1 (v001 , v011)
  ; a1x0 : C1 (v100 , v110)
  ; a1x1 : C1 (v101 , v111)
  ; ax00 : C1 (v000 , v100)
  ; ax01 : C1 (v001 , v101)
  ; ax10 : C1 (v010 , v110)
  ; ax11 : C1 (v011 , v111)
  ; f0xx : C2 (S2b _ _ _ _ a00x a01x a0x0 a0x1)
  ; f1xx : C2 (S2b _ _ _ _ a10x a11x a1x0 a1x1)
  ; fx0x : C2 (S2b _ _ _ _ a00x a10x ax00 ax01)
  ; fx1x : C2 (S2b _ _ _ _ a01x a11x ax10 ax11)
  ; fxx0 : C2 (S2b _ _ _ _ a0x0 a1x0 ax00 ax10)
  ; fxx1 : C2 (S2b _ _ _ _ a0x1 a1x1 ax01 ax11) }.


Arguments S3b {C0} {C1} {C2} v000 v001 v010 v011 v100 v101 v110 v111
                             a00x a01x a10x a11x a0x0 a0x1 a1x0 a1x1 ax00 ax01 ax10 ax11
                             f0xx f1xx fx0x fx1x fxx0 fxx1.
 
Definition s3 {C0 : Type} {C1 : s1 C0} (C2 : s2 C1) : Type :=
   s3_bound C2 -> Type.


Definition CT1 : Type :=
  { C0 : Type &
         s1 C0
  }.

Definition CT2 : Type :=
  { C0 : Type &
  { C1 : s1 C0 &
         s2 C1
  }}.

Definition CT3 : Type :=
  { C0 : Type &
  { C1 : s1 C0 &
  { C2 : s2 C1 &
         s3 C2
  }}}.


Coercion CT1toCT0 (C : CT1) : Type :=
  C.1.

Coercion CT2toCT1 (C : CT2) : CT1 :=
  (C.1 ; C.2.1).

Coercion CT3toCT2 (C : CT3) : CT2 :=
  (C.1 ; (C.2.1 ; C.2.2.1)).



  (* identity types *)

Definition s1b_map {C0 D0 : Type} (M0 : C0 -> D0)
             (v : s1_bound C0) : s1_bound D0 :=
  let (v0 , v1) := v in (M0 v0 , M0 v1).

Definition s1_morph (C D : CT1) (M0 : C.1 -> D.1) : Type :=
  forall v : s1_bound C.1, C.2 v -> D.2 (s1b_map M0 v).


Definition s1_path (C D : CT1) (p0 : C.1 <~> D.1) : Type :=
  forall v : s1_bound C.1, C.2 v <~> D.2 (s1b_map p0 v).


Definition CT1_equivalence (C D : CT1) :=
  { p0 : C.1 <~> D.1 &
    s1_path C D p0 }.


Definition s2b_map {C D : CT1} {M0 : C.1 -> D.1} (M1 : s1_morph C D M0) 
             (a : s2_bound C.2) : s2_bound D.2 :=
  S2b (M0 a.(v00)) (M0 a.(v01)) (M0 a.(v10)) (M0 a.(v11))
      (M1 _ a.(ax0)) (M1 _ a.(ax1)) (M1 _ a.(a0x)) (M1 _ a.(a1x)).


Definition s2_morph (C D : CT2) {p0 : C.1 -> D.1}
                        (p1 : s1_morph C D p0) : Type :=
  forall a : s2_bound C.2.1,
    C.2.2 a -> D.2.2 ((s2b_map p1) a).
 

Definition s2_path (C D : CT2) {p0 : C.1 <~> D.1}
                        (p1 : s1_path C D p0) : Type :=
  forall a : s2_bound C.2.1,
    C.2.2 a <~> D.2.2 ((s2b_map p1) a).


  (* equivalences coerce to maps automatically thanks to the coercion
     [<~>] to [->] *)
Definition test_path_to_map (C D : CT2) {p0 : C.1 <~> D.1}
             (p1 : s1_path C D p0) : s1_morph C D p0 := p1.
  

Definition CT2_equivalence (C D : CT2) : Type :=
  { p0 : C.1 <~> D.1 &
  { p1 : s1_path C D p0 &
         s2_path C D p1
  }}.



Definition transport_s1_bound `{Univalence}
             (C : Type) (D : CT1) (p0 : C <~> D.1) (v : s1_bound C) :
               (transport s1_bound (path_universe_uncurried p0) v) = s1b_map p0 v.
Proof.
  revert p0. equiv_intro (equiv_path C D.1) p. induction p.
  simple refine (ap (fun e => transport s1_bound e v)
                    (path_universe_uncurried_equiv_path _) @ _).
  by induction v.
Defined.



  (* find better name *)
Definition transport_s1 `{Univalence}
             (C : Type) (D : CT1) (p0 : C <~> D.1) :
               transport s1 (path_universe_uncurried p0)^ D.2 =
               D.2 o (s1b_map p0).
Proof.
  apply path_arrow.
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

  exact (fun v => t0 v @ t1 v @ t2 v @ t3 v).
Defined.



(* An idea: we can try to prove this by induction on [p0]. This means
   convert it into a path an then do path induction. In that case [C0]
   and [D0] are definitionally equal and the transports happen over
   refl. The thing is that we don't have refl exactly, but something
   like [path_universe idmap]. So it seems that we have to apply essentially
   the same arguments.
   Also even if we do not do induction on [p0] here, we end up doing it 
   in [transport_s1_bound]. *)

  (* todo: find a better name *)
Definition s1_path_is_path `{Univalence}
             (C D : CT1) (p0 : C.1 <~> D.1) :
               s1_path C D p0 <~>
               (C.2 = transport s1 (path_universe_uncurried p0)^ D.2).
Proof.
    (* we have to prove an equivalence [S <~> T], where [T] is an equality
       between dependent functions. We know this is equivalent to a pointwise
       equivalence *)
  simple refine ((equiv_path_arrow _ _) oE _).
  
    (* now, the [transport ...] can actually be computed, since it
       is a transport over an explicit equivalence. *)
  pose (t0 := ap10 (transport_s1 C D p0)).

    (* [equiv_functor_forall_id] says that a two equivalent fibrations
       induce equivalent Π-types. 
       Since the transport that we know how to compute lives inside two
       [forall] so we use [equiv_functor_forall_id] twice. *)

  pose (t1 :=
    equiv_functor_forall_id (fun v =>
      equiv_path _ _ (ap (fun e => C.2 v = e) (t0 v)))).
  simple refine (t1^-1 oE _).

    (* finally, the definition of [combinatorial_arrows_path] asks us to
       give pointwise equivalences, but this is the same as pointwise
       equalities, again everything lives inside two [forall] *)
  exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
Defined.


  (* todo: find better name *)
Definition CT1_equivalence_is_path `{Univalence} (C D : CT1) :
             CT1_equivalence C D <~> (C = D).
Proof.
    (* [CT1] is a sigma type, so its pathspace can be described as a sigma *)
  simple refine ((equiv_path_sigma_contra _ C D) oE _).
    (* an equivalence between sigma types [sigT A P <~> sigT B Q] can be given by
       an equivalence [e : A <~> B] and a fiberwise equivalence [Q <~> P] *)
  simple refine (equiv_functor_sigma' (equiv_path_universe C.1 D.1) _).

  exact (s1_path_is_path C D).
Defined.



(* untill here everything is fine *)



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


Definition s1_idpath (C : CT1) : s1_path C C equiv_idmap.
Proof.
  intro. simpl. destruct v.
  unfold s1b_map.
  exact equiv_idmap.
Defined.

Definition s1_path_induction
  (C : CT1)
  (P : forall (D0 : Type),
       forall (p0 : C.1 <~> D0), forall (D1 : s1 D0),
       forall (p1 : s1_path C (D0; D1) p0), Type) :
  P C.1 equiv_idmap C.2 (s1_idpath C) ->
  forall D0, forall p0, forall D1, forall p1, P D0 p0 D1 p1.
Proof.
Admitted.

(**)






(* this is the key lemma I still don't know how to prove *)

Definition transport_s1_path_is_path `{Univalence}
  {C : CT1} {D0 : Type}
  (p0 : C.1 <~> D0) {D1 : s1 D0} (p1 : s1_path C (D0; D1) p0) (D2 : s2 D1) 
  (a : s2_bound C.2) :
    (transportD s1 (@s2) (path_universe_uncurried p0)^ D1 D2)
      (transport s2_bound ((s1_path_is_path C (D0; D1) p0) p1) a) =
    D2 (s2b_map (fun v : s1_bound C.1 => p1 v) a).
Proof.
Admitted.
(*
  destruct a.
  unfold s2b_map.
  simpl.
  rewrite transportD_arrow_toconst.

  revert a. revert D2. revert p1. revert D1. revert p0. revert D0.
  refine (s1_path_induction C (fun D0 p0 D1 p1 => _) _).
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
  
  pose (test :=(transport s2_bound ((s1_path_is_path C (D0; D1) p0) p1) a)).
  
  rewrite transportD_is_transport_uncurried.
  (*
  rewrite (transport_s1 C (D0 ; D1)).
  *)
  simpl.
*)



(* the rest is OK, assuming the lemma *)

Definition transport_s1_bound `{Univalence}
             (C : Type) (D : CT1) (p0 : C <~> D.1) (v : s1_bound C) :
               (transport s1_bound (path_universe_uncurried p0) v) = s1b_map p0 v.
Proof.
  revert p0. equiv_intro (equiv_path C D.1) p. induction p.
  simple refine (ap (fun e => transport s1_bound e v)
                    (path_universe_uncurried_equiv_path _) @ _).
  by induction v.
Defined.



Definition transport_s2 `{Univalence}
             (C : CT1) (D : CT2)
             (p0 : C.1 <~> D.1)
             (p1 : s1_path C D p0) (a : s2_bound C.2) :
    transport s2 ((s1_path_is_path C D p0) p1)^
      (transportD s1 (@s2) (path_universe_uncurried p0)^ D.2.1 D.2.2) a =
    D.2.2 (s2b_map p1 a).
Proof.
  rewrite transport_arrow. rewrite transport_const.
  rewrite (inv_V _).
  apply transport_s1_path_is_path.
Qed.


Definition s2_path_is_path `{Univalence}
  (C D : CT2) {p0 : C.1 <~> D.1} (p1 : s1_path C D p0) :
   s2_path C D p1 <~>
    (C.2).2 =
    transport s2 ((s1_path_is_path C D p0) p1)^
      (transportD s1 (@s2) (path_universe_uncurried p0)^ (D.2).1 (D.2).2).
Proof.
    (* idem *)
  simple refine ((equiv_path_forall _ _) oE _).

  pose (t0 := transport_s2 C D p0 p1).
  pose (t1 :=
    equiv_functor_forall_id (fun a =>
      equiv_path _ _ (ap (fun e => C.2.2 a = e) (t0 a)))).
  simple refine (t1^-1 oE _).

    (* idem *)
  exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
Defined.



Definition path_CT2 `{Univalence} (C D : CT2) :
             CT2_equivalence C D <~> (C = D).
Proof.
    (* idem *)
  simple refine ((equiv_path_sigma_contra _ C D) oE _).
    (* idem *)
  simple refine (equiv_functor_sigma' (equiv_path_universe C.1 D.1) _).
  intro p0. simpl.
  
  pose (t := transport_sigma (path_universe_uncurried p0)^ D.2).
  pose (t' := equiv_transport (fun e => C.2 = e) _ _ t).
  refine (t'^-1 oE _).

  simple refine ((equiv_path_sigma_contra _ _ _) oE _).
  simple refine (equiv_functor_sigma' _ _).
    - exact (s1_path_is_path C D p0).
    - exact (s2_path_is_path C D).
Defined.



