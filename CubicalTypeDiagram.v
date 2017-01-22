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