Theorem my_first_proof : (forall A : Prop, forall value_of_A: A, A).
Proof.
  intros A.
  (* intros proof_of_A.
  exact proof_of_A. *)
  intros value_of_B.
  exact value_of_B.
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
Qed.