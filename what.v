Theorem my_first_proof : (forall A : Prop, forall value_of_A: A, A).
Proof.
  intros A.
  (* intros proof_of_A.
  exact proof_of_A. *)
  intros value_of_A.
  exact value_of_A.
Qed.

Theorem my_second_proof : (forall A : Prop, A -> A).
trivial.
Qed.
