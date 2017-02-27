Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.
Require Import CubicalTypeProduct.
Require Import CubicalTypeExponential.


(* diagrams *)
Definition CT1_diagram (C : CT1) : Type :=
  CT1_morph C universe_CT1.

Definition CT2_diagram (C : CT2) : Type :=
  CT2_morph C universe_CT2.

Definition CT3_diagram (C : CT3) : Type :=
  CT3_morph C universe_CT3.


(* diagram morphism (just natural transformations) *)

Definition CT1_diagram_morph {C : CT1} :
             CT1_diagram C * CT1_diagram C -> Type :=
  CT1_naturalt C universe_CT2.

Definition CT2_diagram_morph {C : CT2} :
             CT2_diagram C * CT2_diagram C -> Type :=
  CT2_naturalt C universe_CT3.


(* constant diagrams.
   Looks like everything about diagrams generalizes to morphisms to arbitrary
   CTs with denegeracies (identities) and composition *)

Definition CT1_const_diagram
             (C : CT1) (T : Type) : 
               CT1_diagram C.
Proof.
  exists (const T).
  exact (fun _ _ => idmap).
Defined.
  (* the following is the reasonable way,
     but it does not work:
    := (fun _ => T ; fun _ _ _ => idmap).
     it seems that [a : (fun _ => T) x]
     is not the same as [a : T] *)

Definition idcommutativesquare {V : Type} :
             commutative_square (@S2b universe_CT1 V V V V
                                                   idmap idmap idmap idmap) :=
  fun _ => idpath.

Definition idcommutativecube {V : Type} :
             commutative_cube
               (@S3b universe_CT2 V V V V V V V V
                                  idmap idmap idmap
                                  idmap idmap idmap
                                  idmap idmap idmap
                                  idmap idmap idmap
                                  idcommutativesquare idcommutativesquare idcommutativesquare
                                  idcommutativesquare idcommutativesquare idcommutativesquare) :=
  fun _ => idpath.


Definition CT2_const_diagram
             (C : CT2) (T : Type) : 
               CT2_diagram C.
Proof.
  simple refine ( _ ; _ ).
    - exists (const T).
      exact (fun _ _ => idmap).
    - exact (fun _ _ => idcommutativesquare).
Defined.


Definition CT3_const_diagram
             (C : CT3) (T : Type) : 
               CT3_diagram C.
Proof.
  simple refine ( _ ; _ ).
    - simple refine ( _ ; _ ).
      + exists (const T).
        exact (fun _ _ => idmap).
      + exact (fun _ _ => idcommutativesquare).
    - exact (fun _ _ => idcommutativecube).
Defined.




(* Now we want to prove that a map between types induces a natural
   transformation between constant diagrams (over some 1-CT [C]).
   For this we start by constructing a 2-diagram over [I x C].
*)
(* 0-cells of the diagram *)
Definition CT1_const_diagram_morph0 (C : CT1) {S T : Type} (f : S -> T)
            (x : (CT1_product interval_CT1 C).1) : Type :=
  let (fst,snd) := x in
  match fst with
    | false => S
    | true => T
  end.


(* 1-cells of the diagram *)
Definition CT1_const_diagram_morph1 (C : CT1) {S T : Type} (f : S -> T) :
             CT1_morph (CT1_product interval_CT1 C)
                       universe_CT1.
Proof.
  exists (CT1_const_diagram_morph0 C f).
  intros xy X.
  induction X.
    - cut ((fun x => map (s1b_map (CT1_const_diagram_morph0 C f)
                        (fst x, j, (snd x, j)))) (i0, i1)).
        + exact idmap.
        + induction ai. exact f.
    - exact idmap.
Defined.
(* we want to use the following. But the induction on [ai] does not match
   [i0] with [false] and [i1] with [true], so we rewrite [i0] as [fst (i0, i1)],
   there's probably a nicer way to do this.
  fun xy X =>
    match X with
      | edge_vert i0 i1 ai j =>
          match ai with
            | falsetrue => f
          end
      | vert_edge i j0 j1 aj =>
          match i with
            | _ => idmap
          end
    end
*)


(* 2-cells of the diagram *)
Definition CT1_const_diagram_morph2 (C : CT1) {S T : Type} (f : S -> T) :
             CT2_morph (CT1_product interval_CT1 C)
                       universe_CT2.
Proof.
  exists (CT1_const_diagram_morph1 C f).
  intros b c.
  induction c. 
  cut ((fun x y => universe_CT2.2 (s2b_map (CT1_const_diagram_morph1 C f)
        (@S2b (CT1_product interval_CT1 C)
        (fst x, j0) (fst x, j1) (snd x, j0) (snd x, j1)
        (vert_edge (fst x) aj) (vert_edge (snd x) aj)
        (edge_vert y j0) (edge_vert y j1) ))) (i0, i1) ai).
    - exact idmap.
    - induction ai.
      exact (vert_ct_commutative_square f).
Defined.


Definition CT1_const_diagram_morph (C : CT1) {S T : Type} (f : S -> T) :
             CT1_diagram_morph (CT1_const_diagram C S , CT1_const_diagram C T) :=
  ct1_nat _ _ (CT1_const_diagram_morph2 C f).


(* Now, same as before, but for a 2-CT [C] *)
 (* 0-cells of the diagram *)
Definition CT2_const_diagram_morph0 (C : CT2) {S T : Type} (f : S -> T)
            (x : (CT12_product interval_CT1 C).1) : Type :=
  let (fst,snd) := x in
  match fst with
    | false => S
    | true => T
  end.


(* 1-cells of the diagram *)
Definition CT2_const_diagram_morph1 (C : CT2) {S T : Type} (f : S -> T) :
             CT1_morph (CT12_product interval_CT1 C)
                                        universe_CT1.
Proof.
  exists (CT2_const_diagram_morph0 C f). 
  intros xy X.
  induction X.
    - cut ((fun x => map (s1b_map (CT1_const_diagram_morph0 C f)
                        (fst x, j, (snd x, j)))) (i0, i1)).
        + exact idmap.
        + induction ai. exact f.
    - exact idmap.
Defined.

(* 2-cells of the diagram *)
Definition CT2_const_diagram_morph2 (C : CT2) {S T : Type} (f : S -> T) :
             CT2_morph (CT12_product interval_CT1 C)
                       universe_CT2.
Proof.
  exists (CT2_const_diagram_morph1 C f).
  intros b c.
  induction c. 
    - destruct c.
        + exact (id_commutative_square _).
        + exact (id_commutative_square _).
    - cut ((fun x y => universe_CT2.2 (s2b_map (CT1_const_diagram_morph1 C f)
             (@S2b (CT12_product interval_CT1 C)
               (fst x, j0) (fst x, j1) (snd x, j0) (snd x, j1)
               (vert_edge (fst x) aj) (vert_edge (snd x) aj)
               (edge_vert y j0) (edge_vert y j1) ))) (i0, i1) ai).
        + exact idmap.
        + induction ai.
          exact (vert_ct_commutative_square f).
Defined.


(* 3-cells of the diagram *)
Definition CT2_const_diagram_morph3 (C : CT2) {S T : Type} (f : S -> T) :
             CT3_morph (CT12_product interval_CT1 C)
                      universe_CT3.
Proof.
  exists (CT2_const_diagram_morph2 C f).
  intros b c.
  induction c.
  cut ((fun x y =>
   universe_CT3.2
     (s3b_map (CT2_const_diagram_morph2 C f)
       (@S3b (CT12_product interval_CT1 C)
        (fst x, v00) (fst x, v01) (fst x, v10) (fst x, v11)
        (snd x, v00) (snd x, v01) (snd x, v10) (snd x, v11)
        (vert_edge (fst x) a0x) (vert_edge (fst x) a1x)
        (vert_edge (snd x) a0x) (vert_edge (snd x) a1x)
        (vert_edge (fst x) ax0) (vert_edge (fst x) ax1)
        (vert_edge (snd x) ax0) (vert_edge (snd x) ax1)
        (edge_vert y v00) (edge_vert y v01)
        (edge_vert y v10) (edge_vert y v11)
        (homsquare12 (fst x) f0) (homsquare12 (snd x) f0)
        (mixsquare12 y a0x) (mixsquare12 y a1x)
        (mixsquare12 y ax0) (mixsquare12 y ax1)) )) (c0, c1) cx).
    - exact idmap.
    - induction cx.
      exact (vert_ct_commutative_cube f).
Defined.
 


Definition CT2_const_diagram_morph (C : CT2) {S T : Type} (f : S -> T) :
             CT2_diagram_morph (CT2_const_diagram C S, CT2_const_diagram C T) :=
  ct2_nat _ _ (CT2_const_diagram_morph3 C f).



(* composition of diagram morphisms *)

  (* given two composable natural transformations (which can be seen
     as diagrams over [I x C]) we want to construct a diagram over
     [lI x C], where [lI] is the long interval
   *)

Definition CT1_diagram_morph_comp0 {C : CT1} {D E F : CT1_diagram C}
             (f : CT1_diagram_morph (D,E)) (g : CT1_diagram_morph (E,F))
             (x : (CT1_product interval_CT1 C).1) : Type :=
  let (xi, xc) := x in
  match xi with
    | false => D.1 xc
    | true => F.1 xc
  end.

Definition CT1_diagram_morph_comp1 {C : CT1} {D E F : CT1_diagram C}
             (f : CT1_diagram_morph (D,E)) (g : CT1_diagram_morph (E,F)) :
               CT1_morph (CT1_product interval_CT1 C)
                         universe_CT1.
Proof.
  exists (CT1_diagram_morph_comp0 f g).
  intros xy X.
  induction X.
    - cut ((fun x => map (s1b_map (CT1_diagram_morph_comp0 f g)
                        (fst x, j, (snd x, j)))) (i0, i1)).
      + exact idmap.
      + induction ai.
        exact ((component_arrows_nt1 g j) o (component_arrows_nt1 f j)).
    - simple refine (match i with
               | false => _ (* D.2 _ aj*)
               | true => _ (* F.2 _ aj*)
             end).
        + simpl. exact (F.2 _ aj).
        + simpl. exact (D.2 _ aj).
Defined.


Definition CT1_diagram_morph_comp2 {C : CT1} {D E F : CT1_diagram C}
             (f : CT1_diagram_morph (D,E)) (g : CT1_diagram_morph (E,F)) :
               CT2_morph (CT1_product interval_CT1 C)
                         universe_CT2.
Proof.
  exists (CT1_diagram_morph_comp1 f g).
  intros b c.
  induction c.
  cut ((fun x y => universe_CT2.2 (s2b_map (CT1_diagram_morph_comp1 f g)
        (@S2b (CT1_product interval_CT1 C)
        (fst x, j0) (fst x, j1) (snd x, j0) (snd x, j1)
        (vert_edge (fst x) aj) (vert_edge (snd x) aj)
        (edge_vert y j0) (edge_vert y j1) ))) (i0, i1) ai).
    - exact idmap.
    - induction ai.
      exact (horiz_commutative_square_comp (component_squares_nt1 f aj)
                                           (component_squares_nt1 g aj)).
Defined.


Definition CT1_diagram_morph_comp {C : CT1} {D E F : CT1_diagram C}
             (f : CT1_diagram_morph (D,E)) (g : CT1_diagram_morph (E,F)) :
               CT1_diagram_morph (D,F) :=
  ct1_nat _ _ (CT1_diagram_morph_comp2 f g).
 
 

(* cones *)
Definition cone1 {C : CT1} (D : CT1_diagram C) (d : Type) :=
  CT1_diagram_morph (D, CT1_const_diagram C d).

Definition cone2 {C : CT2} (D : CT2_diagram C) (d : Type) :=
  CT2_diagram_morph (D, CT2_const_diagram C d).


(* universal cone. *)

Definition induced_cone1 {C : CT1}
           (D : CT1_diagram C) (d : Type)
           (cd : cone1 D d) (d' : Type) (f : d -> d') : cone1 D d' :=
  CT1_diagram_morph_comp cd (CT1_const_diagram_morph C f).
