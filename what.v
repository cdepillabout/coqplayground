Theorem my_first_proof : (forall A : Prop, forall value_of_A: A, A).
Proof.
  intros A.
  (* intros proof_of_A.
  exact proof_of_A. *)
  intros value_of_B.
  exact value_of_B.
  (* case value_of_B. *)
  (* elim value_of_B. *)
Qed.

Theorem my_second_proof : (forall A : Prop, A -> A).
trivial.
Qed.

Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A B.
 (* intros B. *)
 intros proof_of_A A_implies_B.
 (* intros A_implies_B. *)
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem lalal : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  exact (A_implies_B proof_of_A).
Qed.

Theorem forward_small_2 :
 (forall A B : Prop,
  (forall value_of_A: A,
   (forall A_implies_B: A->B, B))).
Proof.
 intros A B.
 (* intros B. *)
 intros proof_of_A A_implies_B.
 (* intros A_implies_B. *)
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem forward_small_3 : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A B.
 (* intros B. *)
 intros proof_of_A A_implies_B.
 (* intros A_implies_B. *)
 exact (A_implies_B proof_of_A).
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
 intros A B.
 intros proof_of_A A_implies_B.
 (* refine (A_implies_B _). *)
 refine (A_implies_B proof_of_A).
 (*  exact proof_of_A. *)
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _).
  exact proof_of_A.

  refine (A_implies_B _).
   exact proof_of_A.
Show Proof.
Qed.

Theorem backward_huge2 : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 exact (A_imp_B_imp_C proof_of_A (A_implies_B proof_of_A)).
Show Proof.
Qed.


Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 pose (proof_of_B := A_implies_B proof_of_A).
 pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
Show Proof.
 (*exact proof_of_C.*)
 refine proof_of_C.
Show Proof.
Qed.
Extraction forward_huge.


(* Inductive False : Prop := . *)


(* Inductive True : Prop :=
  | I : True.
*)

(*
Inductive bool : Set :=
  | true : bool
  | false : bool.
*)

(*
Definition not (A:Prop) := A -> False.
*)

(* Notation "~ x" := (not x) : type_scope. *)


Theorem False_cannot_be_proven : ~False.
Proof.
  (* unfold not. *)
  (*unfold "~ _".*)
  (* simpl. *)
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven2 : ~False.
Proof.
  intros proof_of_False.
  elim proof_of_False.
Qed.


Theorem thm_true_imp_true : True -> True.
Proof.
  intros proof_of_True.
  exact I.
Qed.


Theorem thm_false_imp_false : False -> False.
Proof.
  intros.
  case H.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  unfold not.
  intros True_implies_False.
  case (True_implies_False I).
Qed.

Theorem thm_true_imp_false_2 : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F _).
    case I.
    case I.
    elim I.
    exact I.
Qed.

Theorem thm_true_imp_false_3 : ~(True -> False).
Proof.
  intros T_implies_F.
  pose (f := T_implies_F I).
  exact f.
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A.
  intros not_A.
  unfold not in not_A.
  pose (f := not_A proof_of_A). 
  (* unfold not.
  intros A_implies_False.
  pose (f := A_implies_False proof_of_A). *)
  case f.
Qed.


Theorem absurd2_2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A.
  intros not_A.
  pose (f := not_A proof_of_A). 
  case f.
Qed.

Require Import Bool.

Definition eqb' (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition Is_true' (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

(*
Theorem llala2 : forall b1 b2 : bool, eqb' b1 b2 = eqb b1 b2.
Proof.
  intros b1 b2.
  simpl.
  case b1.
    case b2.
      pose (resEqb' := eqb' b1 b2).
      pose (resEqb := eqb b1 b2).
      exact (eqb' true true = eqb true true).
*)

Theorem true_is_True: Is_true true.
Proof.
  unfold Is_true.
  simpl.
  exact I.
Qed.

Theorem not_true_is_True: not (Is_true false).
  unfold "~".
  intros is_true_false.
  simpl is_true_false.
  unfold Is_true.
  case is_true_false.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  (*
  unfold "~".
  intros proof_of_False.
  exact proof_of_False.
  *)
  exact False_cannot_be_proven.
Qed.


Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    unfold Is_true.
    simpl.
    exact I.
 
    simpl.
    exact I. Qed.


Theorem thm_eqb_a_t: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    simpl.
    intros.
    exact I.

    simpl.
    intros.
    case H.
Qed.

(* Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B
where "A \/ B" := (or A B) : type_scope. *)


Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
