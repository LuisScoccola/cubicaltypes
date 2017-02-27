Require Import HoTT.


(* 1,2,3-semi cubical types *)
Section BasicDefs.

  (* boundaries of 1-squares (aka: arrows) *)
  Definition s1_bound (C0 : Type) : Type :=
    C0 * C0.
  
  (* 1-squares over a type *)
  Definition s1 (C0 : Type) : Type :=
    s1_bound C0 -> Type.
  
  (* a 1-cubical type is a type together with 1-squares. it is a graph *)
  Definition CT1 : Type :=
    { C0 : Type & s1 C0}.
  
  
  Coercion CT1toCT0 (C : CT1) : Type := C.1.
  (* Coercion CT1tos1 (C : CT1) : s1 C.1 := C.2. *)
  
  
  (* boundaries of 2-squares *)
  Record s2_bound (C : CT1) : Type :=
   S2b
    { v00 : C.1
    ; v01 : C.1
    ; v10 : C.1
    ; v11 : C.1
    ; a0x : C.2 (v00 , v01)
    ; a1x : C.2 (v10 , v11)
    ; ax0 : C.2 (v00 , v10)
    ; ax1 : C.2 (v01 , v11)
  }.
  
    (* we don't want to write the underlying type each time *)
  Global Arguments S2b {C} v00 v01 v10 v11 a0x a1x ax0 ax1.
  Global Arguments v00 {C} s.
  Global Arguments v01 {C} s.
  Global Arguments v10 {C} s.
  Global Arguments v11 {C} s.
  Global Arguments a0x {C} s.
  Global Arguments a1x {C} s.
  Global Arguments ax0 {C} s.
  Global Arguments ax1 {C} s.
  
  
  (* 2-squares over a 1-cubical type *)
  Definition s2 (C : CT1) :=
    s2_bound C -> Type.
  
  (* a 2-cubical type is a 1-cubical type together with 2-squares *)
  Definition CT2 : Type :=
    { C : CT1 & s2 C}.
  
  Coercion CT2toCT1 (C : CT2) : CT1 := C.1.
  (* Coercion CT2tos2 (C : CT2) : s2 C.1 := C.2. *)
  
  
  (* boundaries of 3-squares (aka: cubes) *)
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
  
  
  Global Arguments S3b {C} v000 v001 v010 v011 v100 v101 v110 v111
                    a00x a01x a10x a11x a0x0 a0x1 a1x0 a1x1 ax00 ax01 ax10 ax11
                    f0xx f1xx fx0x fx1x fxx0 fxx1.
  
  Global Arguments v000 {C} s.
  Global Arguments v001 {C} s.
  Global Arguments v010 {C} s.
  Global Arguments v011 {C} s.
  Global Arguments v100 {C} s.
  Global Arguments v101 {C} s.
  Global Arguments v110 {C} s.
  Global Arguments v111 {C} s.
  Global Arguments a00x {C} s.
  Global Arguments a01x {C} s.
  Global Arguments a10x {C} s.
  Global Arguments a11x {C} s.
  Global Arguments a0x0 {C} s.
  Global Arguments a0x1 {C} s.
  Global Arguments a1x0 {C} s.
  Global Arguments a1x1 {C} s.
  Global Arguments ax00 {C} s.
  Global Arguments ax01 {C} s.
  Global Arguments ax10 {C} s.
  Global Arguments ax11 {C} s.
  Global Arguments f0xx {C} s.
  Global Arguments f1xx {C} s.
  Global Arguments fx0x {C} s.
  Global Arguments fx1x {C} s.
  Global Arguments fxx0 {C} s.
  Global Arguments fxx1 {C} s.

   
  (* 3-squares over a 2-cubical type *)
  Definition s3 (C : CT2) : Type :=
     s3_bound C -> Type.
  
  (* a 3-cubical type is a 2-cubical type together with 3-squares *)
  Definition CT3 : Type :=
    { C : CT2 & s3 C }.
  
  Coercion CT3toCT2 (C : CT3) : CT2 := C.1.
  Coercion CT3tos3 (C : CT3) : s3 C.1 := C.2.

  
End BasicDefs.



(* morphisms between 1,2,3-cubical types *)
Section Morphisms.

    (* CT1 *)
  (* functoriality of 1-boundaries (map should be understood as
     the map function in Haskell) *)
  Definition s1b_map {C0 D0 : Type} (M0 : C0 -> D0)
               (v : s1_bound C0) : s1_bound D0 :=
    let (v0 , v1) := v in (M0 v0 , M0 v1).

  Definition s1b_map_funct_comp {C0 D0 E0 : Type}
               (M0 : C0 -> D0) (N0 : D0 -> E0) :
               (s1b_map N0) o (s1b_map M0) == (s1b_map (N0 o M0)) :=
    fun v => match v with
               | _ => idpath _
             end.
 
  (* homotopy invariance of 1-boundaries *)
  Definition s1b_map_htpy_invariant {C0 D0 : Type}
               {M0 N0 : C0 -> D0} (h : M0 == N0) :
                 s1b_map M0 == s1b_map N0 :=
    fun v => let (v0, v1) := v in
                 (path_prod (M0 v0, M0 v1) (N0 v0, N0 v1) (h v0) (h v1)).
  
  Definition s1_morph {C0 D0 : Type}
               (C1 : s1 C0) (D1 : s1 D0)
               (M0 : C0 -> D0) : Type :=
    forall v : s1_bound C0, C1 v -> D1 (s1b_map M0 v).
  
  Definition CT1_morph (C D : CT1) : Type :=
    {p0 : C.1 -> D.1 & s1_morph C.2 D.2 p0}.
  
  Definition CT1_morph_comp {C D E : CT1}
               (M : CT1_morph C D) (N : CT1_morph D E) :
                 CT1_morph C E.
  Proof.
    exists (N.1 o M.1).
    intro b.
    exact (N.2 _ o M.2 b).
  Defined.
    (* if we try to define this directly it does not type check *)
  
  (* pointwise homotopy between CT1_morph *)
  Definition CT1_morph_homotopy {C D : CT1} (M N : CT1_morph C D) : Type :=
    {h0 : M.1 == N.1 &
     forall b,
       M.2 b == (fun v => ((s1b_map_htpy_invariant h0 b)^ # (N.2 b v)))}.
  
    (* CT2 *)
  Definition s2b_map {C D : CT1} (M : CT1_morph C D)
               (a : s2_bound C) : s2_bound D :=
    S2b (M.1 a.(v00)) (M.1 a.(v01)) (M.1 a.(v10)) (M.1 a.(v11))
        (M.2 _ a.(a0x)) (M.2 _ a.(a1x)) (M.2 _ a.(ax0)) (M.2 _ a.(ax1)).

  Definition s2b_map_funct_comp {C D E : CT1}
               (M : CT1_morph C D) (N : CT1_morph D E) :
               (s2b_map N) o (s2b_map M) == (s2b_map (CT1_morph_comp M N)) :=
    fun b => match b with
               | _ => idpath _
             end.
 

  (*
  Definition s2b_map_htpy_invariant `{Funext} {C D : CT1}
               {M N : CT1_morph C D} (h : CT1_morph_homotopy M N) :
                 s2b_map M == s2b_map N.
  Proof. 
    destruct M as (M0 , M1). destruct N as (N0 , N1).
    destruct h as (h0 , h1). simpl in h1.
    pose (h0p := path_arrow _ _ h0).
    simpl in h0p.
    intro b.
    induction (s1b_map_htpy_invariant h0 b)^.
    unfold s1b_map_htpy_invariant in h1.
    induction h0p.
    pose (h1p' := fun v => path_arrow _ _ (h1 v)).
    pose (h1p := path_forall _ _ h1p').
    intro b.
    destruct b.
    unfold s2b_map.
    simpl.
    induction h1p.
    induction h0.
    rewrite (h0 v02).
    fun v => let (v0, v1) := v in
                 (path_prod (M0 v0, M0 v1) (N0 v0, N0 v1) (h v0) (h v1)).
  *)
 
  
  Definition s2_morph (C D : CT2) (p1 : CT1_morph C.1 D.1) : Type :=
    forall a : s2_bound C,
      C.2 a -> D.2 ((s2b_map p1) a).
    

  Definition CT2_morph (C D : CT2) : Type :=
    { p1 : CT1_morph C D & s2_morph C D p1}.
  

  Definition s3b_map {C D : CT2} (M : CT2_morph C D)
               (a : s3_bound C) : s3_bound D :=
    S3b (M.1.1 a.(v000)) (M.1.1 a.(v001)) (M.1.1 a.(v010)) (M.1.1 a.(v011))
        (M.1.1 a.(v100)) (M.1.1 a.(v101)) (M.1.1 a.(v110)) (M.1.1 a.(v111))
        (M.1.2 _ a.(a00x)) (M.1.2 _ a.(a01x)) (M.1.2 _ a.(a10x)) (M.1.2 _ a.(a11x))
        (M.1.2 _ a.(a0x0)) (M.1.2 _ a.(a0x1)) (M.1.2 _ a.(a1x0)) (M.1.2 _ a.(a1x1))
        (M.1.2 _ a.(ax00)) (M.1.2 _ a.(ax01)) (M.1.2 _ a.(ax10)) (M.1.2 _ a.(ax11))
        (M.2 _ a.(f0xx)) (M.2 _ a.(f1xx)) (M.2 _ a.(fx0x))
        (M.2 _ a.(fx1x)) (M.2 _ a.(fxx0)) (M.2 _ a.(fxx1)).

  Definition s3_morph (C D : CT3) (p2 : CT2_morph C.1 D.1) : Type :=
    forall a : s3_bound C,
      C.2 a -> D.2 ((s3b_map p2) a).
 
  Definition CT3_morph (C D : CT3) : Type :=
    { p2 : CT2_morph C D & s3_morph C D p2}.


End Morphisms.
 


(** identity types of [CT1] and [CT2] *)
Section IdentityTypes.
  
    (* definitions *)
  Definition s1_equiv {C0 D0 : Type}
               (C1 : s1 C0) (D1 : s1 D0)
               (M0 : C0 -> D0) : Type :=
    forall v : s1_bound C0, C1 v <~> D1 (s1b_map M0 v).
  
  
  Definition CT1_equiv (C D : CT1) :=
    { p0 : C.1 <~> D.1 & s1_equiv C.2 D.2 p0 }.
  
  Coercion CT1_equiv_to_morph {C D : CT1} :
            CT1_equiv C D -> CT1_morph C D.
  Proof.
    intro e. exists e.1. exact e.2.
  Defined.
  
  
  Definition s2_equiv (C D : CT2) (p1 : CT1_equiv C.1 D.1) : Type :=
    forall a : s2_bound C,
      C.2 a <~> D.2 ((s2b_map (CT1_equiv_to_morph p1)) a).
    (* for some reason we have to coerce manually there *)
  
  Definition CT2_equiv (C D : CT2) : Type :=
    { p1 : CT1_equiv C D & s2_equiv C D p1}.
  
  
  
  Definition transport_s1_actiononpath
               (C : Type) (D : CT1) (p0 : D.1 = C) (v : s1_bound C) :
                 transport s1 p0 D.2 v =
                 D.2 (s1b_map (equiv_path _ _ p0^) v).
  Proof.
    by induction p0.
  Defined.
  
  
    (* proofs *)
  Definition transport_s1_actiononequiv `{Univalence}
               (C : Type) (D : CT1) (p0 : C <~> D.1) (v : s1_bound C) :
                 transport s1 (path_universe_uncurried p0)^ D.2 v =
                 D.2 (s1b_map p0 v).
  Proof.
    pose (t0 := transport_s1_actiononpath C D (path_universe_uncurried p0)^ v).
    refine (t0 @ _) ; clear t0.
    refine (ap D.2 _).
    refine (ap (fun e => (s1b_map (transport idmap e) v)) (inv_V _) @ _ ).
    revert v.
    refine (s1b_map_htpy_invariant _).
    intro v.
    refine (apD10 _ v).
    exact (transport_idmap_path_universe_uncurried p0).
  Defined.
  
  
  Definition cancel__ (C : CT1) (v : s1_bound C)
               (p : C.1 = C.1) (pp : p = idpath) :
     transport_s1_actiononpath C C p^ v @
     ap C.2 (ap (fun e : C.1 = C.1 => s1b_map (transport idmap e) v) (inv_V p) @
        s1b_map_htpy_invariant (fun v0 : C =>
           apD10 (ap equiv_fun (ap (equiv_path C.1 C.1) pp)) v0) v) =
     ap (fun e : C.1 = C.1 => transport s1 e^ C.2 v) pp.
  Proof.
    destruct C as (C0 , C1). rewrite <- (inv_V pp). induction pp^. simpl.
    reflexivity.
  Qed.
  
  
  
  Definition transport_s1_actiononequiv_on_id `{Univalence}
               (C : CT1) (v : s1_bound C) :
                 transport_s1_actiononequiv C C (equiv_path C.1 C.1 1) v =
                   ap (fun e => transport s1 e^ C.2 v)
                     (eta_path_universe_uncurried (idmap _)).
  Proof.
    unfold transport_s1_actiononequiv.
    unfold transport_idmap_path_universe_uncurried.
    unfold eta_path_universe_uncurried.
    simpl.
    rewrite eisadj.
    rewrite cancel__.
    reflexivity.
  Qed.
  
  
  
  Definition s1_equiv_is_path `{Univalence}
               (C D : CT1) (p0 : C.1 <~> D.1) :
                 s1_equiv C.2 D.2 p0 <~>
                 (C.2 = transport s1 (path_universe_uncurried p0)^ D.2).
  Proof.
      (* we have to prove an equiv [S <~> T], where [T] is an equality
         between dependent functions. We know this is equivalent to a pointwise
         equiv *)
    simple refine ((equiv_path_arrow _ _) oE _).
    
      (* now, the [transport ...] can actually be computed, since it
         is a transport over an explicit equivalence. *)
    pose (t0 := transport_s1_actiononequiv C D p0).
  
      (* [equiv_functor_forall_id] says that a two equivalent fibrations
         induce equivalent Π-types. *)
    pose (t1 :=
      equiv_functor_forall_id (fun v =>
        equiv_path _ _ (ap (fun e => C.2 v = e) (t0 v)))).
    simple refine (t1^-1 oE _).
  
    exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
  Defined.
  
  
  (* characterization of identity types of [CT1] *)
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
  
  Definition CT1_equiv_is_path_actiononid `{Univalence} (C : CT1) :
               ((CT1_equiv_is_path C C)^-1 (idpath _)) = CT1_idequiv C.
  Proof.
    simple refine (path_sigma _ _ _ _ _).
      - reflexivity.
      - unfold transport.
        refine (path_forall _ _ _).
        intro v. simpl.
        unfold functor_forall.
        
        (* how to rewrite as? something like:
          rewrite (1%equiv) as (equiv_path (C v) (C v) 1). *)
        rewrite (test _)^.
        refine (ap (equiv_path _ _) _).
        rewrite concat_1p.
        rewrite transport_s1_actiononequiv_on_id.
        unfold eta_path_universe_uncurried.
        apply cancel_.
  Qed.
  
  
  
   
  Definition transport_s2_actiononequiv `{Univalence}
               (C : CT1) (D : CT2)
               (p1 : CT1_equiv C D) (a : s2_bound C) :
      transport s2 (CT1_equiv_is_path C D p1)^ D.2 a =
      D.2 (s2b_map (CT1_equiv_to_morph p1) a).
  Proof.
    destruct D as (D , D2). 
    revert p1. equiv_intro (CT1_equiv_is_path C D)^-1 p. induction p.
    rewrite eisretr.
    rewrite CT1_equiv_is_path_actiononid.
    reflexivity.
  Qed.
  
  
  Definition s2_equiv_is_path `{Univalence}
    (C D : CT2) (p1 : CT1_equiv C D) :
     s2_equiv C D p1 <~>
     (C.2 = transport s2 (CT1_equiv_is_path C.1 D.1 p1)^ D.2).
  Proof.
    simple refine ((equiv_path_forall _ _) oE _).
  
    pose (t0 := transport_s2_actiononequiv C D p1).
    pose (t1 :=
      equiv_functor_forall_id (fun a =>
        equiv_path _ _ (ap (fun e => C.2 a = e) (t0 a)))).
    simple refine (t1^-1 oE _).
  
    exact (equiv_functor_forall_id (fun v => equiv_path_universe _ _)).
  Defined.
  
  
  Definition CT2_equiv_is_path `{Univalence} (C D : CT2) :
               CT2_equiv C D <~> (C = D).
  Proof.
    simple refine ((equiv_path_sigma_contra _ C D) oE _).
    simple refine (equiv_functor_sigma' (CT1_equiv_is_path C.1 D.1) _).
    intro p1.
    apply s2_equiv_is_path.
  Defined.

End IdentityTypes.




(*** opposites:
       - given a 1-CT (graph) we can consider its opposite
       - given a 2-CT we can consider its 1-opposite or its 2-opposite.
         the former flips all the arrows (and the squares accordingly),
         while the latter flips only the squares
 *)
Section Opposites.
 
  Definition flip {A B : Type} : A * B -> B * A :=
    fun ab => (snd ab , fst ab).

  Definition s1b_flip {C : Type} : s1_bound C -> s1_bound C := flip.
  
  Definition CT1_opposite (C : CT1) : CT1 :=
    (C.1 ; C.2 o s1b_flip).
  

  Definition s2b_flip {C : CT1} (b : s2_bound C) : s2_bound C :=
    S2b b.(v00) b.(v10) b.(v01) b.(v11) (* middle points are interchanged *)
        b.(ax0) b.(ax1) b.(a0x) b.(a1x).

  Definition CT2_opposite_2 (C : CT2) : CT2 :=
    (C.1 ; C.2 o s2b_flip).

End Opposites.






(* EXTRAS *)
Definition s1b_Dmap {C0 : Type} {D0 : C0 -> Type}
             (M0 : forall c : C0, D0 c)
             (v : s1_bound C0) : s1_bound (sigT D0) :=
  ((fst v ; M0 (fst v)),
   (snd v ; M0 (snd v))). 


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


Definition s1_morph' {C0 : Type} (C1 D1 : s1 C0) : Type :=
  forall v : s1_bound C0, C1 v -> D1 v.

Definition s1_equiv' {C0 : Type} (C1 D1 : s1 C0) : Type :=
  forall v : s1_bound C0, C1 v <~> D1 v.

(* END EXTRAS *)
