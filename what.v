Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem my_second_proof : (forall A : Prop, A -> A).
trivial.
Qed.
