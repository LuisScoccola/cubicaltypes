Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.
Require Import CubicalTypeProduct.



(* 1-natural transformation: if [C] is a 1-CT and [H] is a 2-CT
   we form the 1-CT [H^C].
     - The 0-cells are 1-morphisms [C -> H.1]
     - The 1-cells are given by the fibration [Nat : (C -> H.1) -> (C -> H.1) -> Type]
*)
Definition inclusion_top1 {C : CT1} {H : CT2}
                          (N : CT2_morph (CT1_product interval_CT1 C) H) :
                            CT1_morph C H.
Proof.
  exists ( fun c0 => N.1.1 (false , c0) ).
  exact (fun _ a => N.1.2 _ (@vert_edge interval_CT1 C false _ _ a)).
Defined.

Definition inclusion_bot1 {C : CT1} {H : CT2}
                          (N : CT2_morph (CT1_product interval_CT1 C) H) :
                            CT1_morph C H.
Proof.
  exists ( fun c0 => N.1.1 (true , c0) ).
  exact (fun _ a => N.1.2 _ (@vert_edge interval_CT1 C true _ _ a)).
Defined.
(* abstract the inclusions? *)


Inductive CT1_naturalt (C : CT1) (H : CT2) :
            (CT1_morph C H * CT1_morph C H) -> Type :=
  | ct1_nat (N : CT2_morph (CT1_product interval_CT1 C) H) :
      CT1_naturalt C H (inclusion_top1 N , inclusion_bot1 N).

(* underlying morphism, not needed *)
Definition underlying_morphism_nt1 {C : CT1} {H : CT2}
                                   {fg : CT1_morph C H * CT1_morph C H}
                                   (N : CT1_naturalt C H fg) :
                                     CT2_morph (CT1_product interval_CT1 C) H :=
  match N with
    | ct1_nat N' => N'
  end.

(* The following functions return the components of natural transformations.
   In 1-category theory the components of a natural transformation consists
   of one arrow for each object in the source category. In our case we have
   also the higher dimensional components, for example we have a square for each
   arrow in the source, etc *)
   
Definition component_arrows_nt1 {C : CT1} {H : CT2}
                                {fg : CT1_morph C H * CT1_morph C H}
                                (N : CT1_naturalt C H fg) (c : C.1) :
                                  H.1.2 (((fst fg).1 c), ((snd fg).1 c)) :=
  match N with
    | ct1_nat NN => NN.1.2 _ (@edge_vert interval_CT1 C _ _ falsetrue c)
  end.

Definition component_squares_nt1 {C : CT1} {H : CT2}
             {fg : CT1_morph C H * CT1_morph C H}
             (N : CT1_naturalt C H fg) {v : s1_bound C.1} (a : C.2 v) :
               H.2 (@S2b H.1 _ _ _ _ ((fst fg).2 _ a) ((snd fg).2 _ a)
                                     (component_arrows_nt1 N (fst v))
                                     (component_arrows_nt1 N (snd v))) :=
  match N with
    | ct1_nat NN => NN.2 _ (@square interval_CT1 C _ _ falsetrue _ _ a)
  end.


(* [H^C] *)
Definition exponential12 (H : CT2) (C : CT1) : CT1 :=
  (CT1_morph C H ; CT1_naturalt C H).


Definition inclusion_top2 {C : CT2} {H : CT3}
                          (N : CT3_morph (CT12_product interval_CT1 C) H) :
                            CT2_morph C H.
Proof.
  simple refine ( _ ; _).
    - exists ( fun c0 => N.1.1.1 (false , c0) ).
      exact ( fun _ a => N.1.1.2 _ (@vert_edge interval_CT1 C false _ _ a)).
    - exact ( fun _ f => N.1.2 _ (@homsquare12 interval_CT1 C false _ _ _ _ _ _ _ _ f )).
Defined.
                                       
Definition inclusion_bot2 {C : CT2} {H : CT3}
                          (N : CT3_morph (CT12_product interval_CT1 C) H) :
                            CT2_morph C H.
Proof.
  simple refine (_ ; _).
    - exists ( fun c0 => N.1.1.1 (true , c0) ).
      exact ( fun _ a => N.1.1.2 _ (@vert_edge interval_CT1 C true _ _ a)).
    - exact ( fun _ f => N.1.2 _ (@homsquare12 interval_CT1 C true _ _ _ _ _ _ _ _ f )).
Defined.

Inductive CT2_naturalt (C : CT2) (H : CT3) :
            (CT2_morph C H * CT2_morph C H) -> Type :=
  | ct2_nat (N : CT3_morph (CT12_product interval_CT1 C) H) :
      CT2_naturalt C H (inclusion_top2 N , inclusion_bot2 N).

(* the following would be nice, but we have to show that
   the underlying 2CT of [I x C] is the same as the product
   of [I] and the underlying 1CT of [C]. It looks like eventually
   we will need to prove a compatibility of this sort
Coercion CT1NTtoCT2NT {C : CT2} {H : CT3} {f g : CT2_morphism C H} :
                      CT2_naturalt _ _ f g -> CT1_naturalt _ _ f g.
Proof.
  intros N. induction N.
  exact (ct1_nat C H N).
*)

(* underlying morphism *)
Definition underlying_morphism_nt2 {C : CT2} {H : CT3}
                                   {fg :  CT2_morph C H * CT2_morph C H}
                                   (N : CT2_naturalt C H fg) :
                                     CT3_morph (CT12_product interval_CT1 C) H :=
  match N with
    | ct2_nat N' => N'
  end.


(* [H^C] *)
Definition exponential23 (H : CT3) (C : CT2) : CT1 :=
  (CT2_morph C H ; CT2_naturalt C H).