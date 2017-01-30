Require Import HoTT.
Require Import CubicalType.
Require Import CubicalTypeExamples.
Require Import CubicalTypeProdExp.


(* diagrams *)
Definition CT1_diagram (C : CT1) : Type :=
  CT1_morphism C universe_CT1.

Definition CT2_diagram (C : CT2) : Type :=
  CT2_morphism C universe_CT2.

Definition CT3_diagram (C : CT3) : Type :=
  CT3_morphism C universe_CT3.


(* diagram morphism (just natural transformations) *)

Notation CT1_diagram_morph := CT1_naturalt.

Notation CT2_diagram_morph := CT2_naturalt.


(* constant diagrams *)
Definition CT1_const_diagram
             (C : CT1) (T : Type) : 
               CT1_diagram C.
Proof.
  exists (const T).
  exact (fun _ _ _ => idmap).
Defined.
  (* the following is the reasonable way,
     but it does not work:
    := (fun _ => T ; fun _ _ _ => idmap).
     it seems that [a : (fun _ => T) x]
     is not the same as [a : T] *)

Definition idcommutativesquare {V : Type} :
             commutative_square V V V V
                                idmap idmap idmap idmap :=
  fun _ => idpath.

Definition idcommutativecube {V : Type} :
             commutative_cube V V V V V V V V
                              idmap idmap idmap
                              idmap idmap idmap
                              idmap idmap idmap
                              idmap idmap idmap
                              idcommutativesquare idcommutativesquare idcommutativesquare
                              idcommutativesquare idcommutativesquare idcommutativesquare :=
  fun _ => idpath.


Definition CT2_const_diagram
             (C : CT2) (T : Type) : 
               CT2_diagram C.
Proof.
  exists (const T).
  exists (fun _ _ _ => idmap).
  exact (fun _ _ _ _ _ _ _ _ _ => idcommutativesquare).
Defined.


Definition CT3_const_diagram
             (C : CT3) (T : Type) : 
               CT3_diagram C.
Proof.
  exists (const T).
  exists (fun _ _ _ => idmap).
  exists (fun _ _ _ _ _ _ _ _ _ => idcommutativesquare).
  unfold combinatorial_cubes_morph.
  intros. exact idcommutativecube.
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
             combinatorial_arrows_morph (CT1_product interval_CT1 C)
                                        universe_CT1 
                                        (CT1_const_diagram_morph0 C f) :=
  fun x y X =>
    match X with
      | edge_vert i0 i1 ai j =>
          match ai with
            | falsetrue => f
          end
      | vert_edge i j0 j1 aj =>
          match i with
            | _ => idmap
          end
    end.
(* OLD (uses the non inductive family definition of the interval)
  (* the idea here is simple, but the final proof is too verbose, it would be
     nicer if we could use some pattern matching *)
  intros x y. destruct x as (xi,xj). destruct y as (yi,yj).
  intro X. induction X.
  generalize i0 i1 ai.
  simple refine (Bool_ind _ _ _).
    - simple refine (Bool_ind _ _ _).
        + exact (Empty_ind _).
        + exact (Empty_ind _).
    - simple refine (Bool_ind _ _ _).
        + exact (const f).
        + exact (Empty_ind _).
    - exact (match i with
               | _ => idmap
             end).
Defined.
*)


(* 2-cells of the diagram *)
Definition CT1_const_diagram_morph2 (C : CT1) {S T : Type} (f : S -> T) :
             combinatorial_squares_morph (CT1_product interval_CT1 C)
                                        universe_CT2 
                                        (CT1_const_diagram_morph1 C f) :=
  fun v00 v01 v10 v11 ax0 ax1 a0x a1x c =>
    match c with
      | square i0 i1 ai j0 j1 aj =>
          match ai with
            | falsetrue => vert_ct_commutative_square f 
          end
    end.


Definition CT1_const_diagram_morph' (C : CT1) {S T : Type} (f : S -> T) :
             CT2_diagram (CT1_product interval_CT1 C) :=
  (CT1_const_diagram_morph0 C f ; (CT1_const_diagram_morph1 C f ; CT1_const_diagram_morph2 C f)).


Definition CT1_const_diagram_morph (C : CT1) {S T : Type} (f : S -> T) :
             CT1_diagram_morph _ universe_CT2
               (CT1_const_diagram C S) (CT1_const_diagram C T) :=
  ct1_nat _ _ (CT1_const_diagram_morph' C f). (* <- this computes! *)


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
             combinatorial_arrows_morph (CT12_product interval_CT1 C)
                                        universe_CT1 
                                        (CT2_const_diagram_morph0 C f) :=
  fun x y X =>
    match X with
      | edge_vert i0 i1 ai j =>
          match ai with
            | falsetrue => f
          end
      | vert_edge i j0 j1 aj =>
          match i with
            | _ => idmap
          end
    end.

(* 2-cells of the diagram *)
Definition CT2_const_diagram_morph2 (C : CT2) {S T : Type} (f : S -> T) :
             combinatorial_squares_morph (CT12_product interval_CT1 C)
                                        universe_CT2 
                                        (CT2_const_diagram_morph1 C f) :=
  fun v00 v01 v10 v11 ax0 ax1 a0x a1x c =>
    match c with
      | homsquare12 c' v00' v01' v10' v11'
                    a0x' a1x' ax0' ax1' f => 
          match c' with
            | _ => id_commutative_square _ 
          end
      | mixsquare12 i0 i1 ai j0 j1 aj =>
          match ai with
            | falsetrue => vert_ct_commutative_square f 
          end
    end.

(* 3-cells of the diagram *)
Definition CT2_const_diagram_morph3 (C : CT2) {S T : Type} (f : S -> T) :
             combinatorial_cubes_morph (CT12_product interval_CT1 C)
                                        universe_CT3
                                        (CT2_const_diagram_morph2 C f) :=
  fun v000 v001 v010 v011 v100 v101 v110 v111
      a00x a01x a10x a11x a0x0 a0x1 a1x0 a1x1 ax00 ax01 ax10 ax11
      f0xx f1xx fx0x fx1x fxx0 fxx1 c =>
  match c with
    | cube12 c0 c1 cx v00 v01 v10 v11 a0x a1x ax0 ax1 f' =>
        match cx with
          | falsetrue => vert_ct_commutative_cube f
        end
  end.
 

Definition CT2_const_diagram_morph' (C : CT2) {S T : Type} (f : S -> T) :
             CT3_diagram (CT12_product interval_CT1 C) :=
  (CT2_const_diagram_morph0 C f ;
  (CT2_const_diagram_morph1 C f ;
  (CT2_const_diagram_morph2 C f ;
   CT2_const_diagram_morph3 C f
  ))).


Definition CT2_const_diagram_morph (C : CT2) {S T : Type} (f : S -> T) :
             CT2_diagram_morph _ universe_CT3
               (CT2_const_diagram C S) (CT2_const_diagram C T) :=
  ct2_nat _ _ (CT2_const_diagram_morph' C f). (* <- this computes! *)

 

(* cones *)
Definition cone1 {C : CT1} (D : CT1_diagram C) (d : Type) :=
  CT1_diagram_morph _ universe_CT2 D (CT1_const_diagram C d).

Definition cone2 {C : CT2} (D : CT2_diagram C) (d : Type) :=
  CT2_diagram_morph _ universe_CT3 D (CT2_const_diagram C d).