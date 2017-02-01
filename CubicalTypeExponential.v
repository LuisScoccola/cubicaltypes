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

(* underlying morphism *)
Definition underlying_morphism_nt1 {C : CT1} {H : CT2} {f g : CT1_morphism C H}
                                   (N : CT1_naturalt C H f g) :
                                     CT2_morphism (CT1_product interval_CT1 C) H :=
  match N with
    | ct1_nat N' => N'
  end.

  (* todo: find better name *)
Definition underlying_arrows_nt1 {C : CT1} {H : CT2} {f g : CT1_morphism C H}
                                 (N : CT1_naturalt C H f g) (c : C.1) :
                                   H.2.1 (f.1 c) (g.1 c) :=
  match N with
    | ct1_nat NN => NN.2.1 _ _ (@edge_vert interval_CT1 C _ _ falsetrue c)
  end.

Definition underlying_squares_nt1 {C : CT1} {H : CT2} {f g : CT1_morphism C H}
                                  (N : CT1_naturalt C H f g) {c c' : C.1} (a : C.2 c c') :
                                    H.2.2 _ _ _ _ (f.2 _ _ a) (g.2 _ _ a)
                                                  (underlying_arrows_nt1 N c)
                                                  (underlying_arrows_nt1 N c') :=
  match N with
    | ct1_nat NN => NN.2.2 _ _ _ _ _ _ _ _ (@square interval_CT1 C _ _ falsetrue _ _ a)
  end.


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
Definition underlying_morphism_nt2 {C : CT2} {H : CT3} {f g : CT2_morphism C H}
                                   (N : CT2_naturalt C H f g) :
                                     CT3_morphism (CT12_product interval_CT1 C) H :=
  match N with
    | ct2_nat N' => N'
  end.


(* [H^C] *)
Definition exponential23 (H : CT3) (C : CT2) : CT1 :=
  (CT2_morphism C H ; CT2_naturalt C H).

