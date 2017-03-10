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


(*
Theorem thm_eqb_a_t_2: (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  simpl.
  intros H.
  case a.
    simpl. trivial.
    
    simpl. simpl in H. 

Qed.
*)

(* Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B
where "A \/ B" := (or A B) : type_scope. *)


Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  (* exact (or_introl proof_of_A). *)
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.


Theorem right_or : (forall A B : Prop, B -> A \/ B).
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem right_or2 : (forall A B : Prop, B -> A \/ B).
  intros A B.
  intros proof_of_B.
  refine (or_intror proof_of_B).
Qed.

Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    intros proof_of_A.
    exact (or_intror proof_of_A).
  
    intros proof_of_B.
    exact (or_introl proof_of_B).
Qed.

(*
Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.
*)

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
    exact proof_of_A.
    exact proof_of_B.
Qed.
Extraction both_and.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
    intros proof_of_A.
    intros proof_of_B.
    exact (conj proof_of_B proof_of_A).
Qed.


Theorem and_commutes__again : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B].
  refine (conj _ _).
    exact proof_of_B.
    exact proof_of_A.
Qed.


(*
Infix "&&" := andb : bool_scope.
Infix "" := orb : bool_scope.
*)

(*
Definition iff (A B:Prop) := (A -> B) /\ (B -> A).
Notation "A <-> B" := (iff A B) : type_scope.
*)

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  
  refine (conj _ _).
    intros H.
    case a, b.
      simpl. exact (or_introl I).
      simpl. exact (or_introl I).
      simpl. exact (or_intror I).
      simpl. simpl in H. (* exact (or_introl H). *) case H.

    intros H.
    case a, b.
      simpl. exact I.
      simpl. exact I.
      simpl. exact I.
      simpl. simpl in H. case H. trivial. trivial.

  (*
  case a.
    case b.
      simpl.
      refine (conj _ _).
        intros.
        exact (or_introl I).

        intros.
        exact I.

       
      simpl.
      refine (conj _ _).
        intros.
        exact (or_introl I).

        intros.
        exact I.

    case b.
      simpl.
      refine (conj _ _).
        intros.
        exact (or_intror I).
 
        intros _.
        exact I.

      simpl.
      refine (conj _ _).
        intros f.
        exact (or_introl f).

        intros f_or_f.
        case f_or_f.
          intros f.
          exact f.

          intros f.
          exact f.
  *)
Qed.
        
Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      simpl. exact (conj I I).
      simpl. simpl in H. case H.
      simpl. simpl in H. case H.
      simpl. simpl in H. case H.

    intros lala.
    case a,b.
      simpl. trivial.
      simpl in lala. destruct lala as [ A B]. case B. (* case lala. intros _ f. exact f. *)
      simpl. simpl in lala. case lala. intros f _. case f.
      simpl. simpl in lala. case lala. intros f _. case f.
Qed.


Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  unfold "<->".
  unfold not.
  (* case a. *)
  refine (conj _ _).
    case a.
      simpl. intros f _. case f.
      simpl. intros _ f. case f.

    case a.
      simpl. intros True_implies_False. exact (True_implies_False I).
      simpl. intros _. exact I.
Qed.

Print ex.

Print or.

(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  ex_intro : forall x : A, P x -> ex (A) P.
*)



(*

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
*)

Definition basic_predicate : bool -> Prop
:=
  (fun a => Is_true (andb a true))
.

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  (*
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    unfold basic_predicate.
    simpl.
    exact I.
  *)
(*
Unset Printing Notations.
  simpl.
SearchAbout .
Locate "exists".
Print ex.
Check ex.
Extraction ex.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    simpl.
    exact I.
    intros H.
    Check basic_predicate.
    exact (basic_predicate true).  
*)
(*
refine (ex_intro basic_predicate true _).
  simpl.
  unfold basic_predicate.
  simpl.
  unfold Is_true.
  exact (I).
*)

refine (ex_intro _ true I).
 
Qed.

 Theorem thm_exists_basics__again : (exists a, Is_true (andb a true)).
Proof.
  pose (witness := true).
(*
  refine (ex_intro _ _ _).
  exact (Is_true (andb true true)).
*)
  refine (ex_intro _ witness _).
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  case b.
    refine (ex_intro _ true I).
    refine (ex_intro _ false I).
Qed.

Theorem thm_forall_exists__again : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _). 
     exact (eqb_a_a b).
Qed.

Theorem thm_forall_exists__again2 : (forall (b : bool), (exists (a : bool), Is_true(eqb a b))).
Proof.
  intros b.
  refine ((ex_intro _) b _).
    case b.
      simpl.
      exact I.

      simpl.
      exact I.
Qed.


Theorem forall_exists : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros p.
  intros lala.
  unfold not.
  unfold not in lala.
  intros existsbaba.
  destruct existsbaba as [ ].
  pose (haha := lala x).
  pose (gaga := haha H).
  case gaga.
Qed.



Theorem forall_exists_2 : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P forallXNotPX notExistsPX.
  unfold not in forallXNotPX, notExistsPX.
  case notExistsPX.
  intros x.
  intros Px.
  case (forallXNotPX x Px).
  
  (*
  intros P forallXNotPX notExistsPX.
  unfold not in forallXNotPX, notExistsPX.
  destruct notExistsPX.
  exact (forallXNotPX x H).
  *)
Qed.

Theorem exists_forall : (forall P : Set->Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
  intros.
  unfold not.
  unfold not in H.
  intros Px.
  case H.
  exact (ex_intro P x Px).
Qed.

Theorem lalala_eq : (forall (A : Set) (x : A), eq x x).
Proof.
  intros.
  exact (eq_refl : eq x x).
Qed.


Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
intros x y.
intros eq_x_y.
(*
case eq_x_y.
exact eq_refl.
*)
destruct eq_x_y.
exact eq_refl.
Qed.

Theorem thm_eq_trans : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
intros.
destruct H, H0.
exact eq_refl.
Qed.

(*Require Coq.*)
Require Coq.Setoids.Setoid.
Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
intros.
rewrite H.
rewrite <- H0.
exact eq_refl.
Qed.

Theorem andb_sym : (forall a b, a && b = b && a).
Proof.
intros.
case a,b.
  simpl. exact eq_refl.
  simpl. exact eq_refl. 
  simpl. exact eq_refl.
  simpl. exact eq_refl.
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
intros.
unfold not.
case a.
  unfold negb. discriminate.
  unfold negb. intros. discriminate H.
Qed.


Theorem plus_2_3 : (S (S O)) + (S (S (S O))) = (S (S (S (S (S O))))).
Proof.
  simpl.
  (* exact (eq_refl 5). *)
  exact (eq_refl (S (S (S (S (S O)))))).
Qed.

Theorem plus_O_n : (forall n, O + n = n).
Proof.
  intros.
  simpl.
  exact (eq_refl n).
Qed.


Theorem associativity_of_plus : (forall (n : nat) (m : nat), n + m = m + n).
Proof.
  admit.
Qed.

Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros.
  (* case n. *)
  (*
  induction n.
    exact eq_refl.
  
    simpl.
    rewrite IHn.
    exact eq_refl.
  *)
  (* apply nat_ind with (n := n). *)
  elim n.
    (* apply eq_refl. *)
    exact eq_refl.

    intros m H.
    simpl.
    rewrite H.
    exact (eq_refl).
Qed.


Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
  intros n.
  elim n.
    intros m.
    elim m.
      simpl. exact (eq_refl).

      intros.
      simpl.
      rewrite <- H.
      simpl.
      exact (eq_refl (S n0)).

    intros.
    simpl.
    simpl H.
    rewrite (H m).
    elim m.
      simpl. exact (eq_refl).

      intros.
      simpl.
      rewrite H0.
      exact (eq_refl).
Qed.

Require Import List.

Theorem cons_adds_one_to_length :
   (forall A:Type, (forall (x : A) (lst : list A),
    length (x :: lst) = (S (length lst)))
   ).
Proof.
  intros.
  simpl.
  exact (eq_refl).
Qed.


(*
Definition hd (A : Type) (default : A) (l : list A) : A
:=
  match l with
    | nil => default
    | h :: _ => h
  end.
*)


Definition my_hd_for_nat_lists : list nat -> nat
:=
  hd 0.

Compute my_hd_for_nat_lists nil.

Compute my_hd_for_nat_lists (5 :: 4 :: nil).

Theorem correctness_of_hd :
   (forall A:Type,
   (forall (default : A) (x : A) (lst : list A),
   (hd default nil) = default /\ (hd default (x :: lst)) = x)).
Proof.
  intros.
  simpl.
  refine (conj _ _).
    exact eq_refl.
    exact eq_refl.
Qed.


Definition hd_error (A : Type) (l : list A)
:=
  match l with
    | nil => None
    | x :: _ => Some x
  end.

Compute hd_error nat nil.

Compute hd_error nat (5 :: 4 :: nil).

Theorem correctness_of_hd_error :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (hd_error A nil) = None /\ (hd_error A (x :: lst)) = Some x)).
Proof.
  intros.
  simpl.
  refine (conj _ _).
    exact eq_refl.
    exact eq_refl.
Qed.

Definition hd_never_fail (A : Type) (lst : list A) (safety_proof : lst <> nil)
  : A
:=
  (match lst as b return (lst = b -> A) with
    | nil => (fun foo : lst = nil =>
                   match (safety_proof foo) return A with
                   end
                )
    | x :: _ => (fun foo : lst = x :: _ =>
                   x
                )
  end) eq_refl.

Theorem cons_cant_equal_nil : (forall (A: Type), (forall (x : A) (rest : list A),
  (x :: rest) <> nil)).
Proof.
  unfold not.
  intros.
  discriminate H.
Qed.

Goal forall A B C:Prop, A /\ B /\ C \/ B /\ C \/ C /\ A -> C.
  intros.
  decompose [and or] H.
    assumption.
    assumption.
    assumption.
Qed.

Theorem correctness_of_hd_never_fail :
   (forall A:Type,
   (forall (x : A) (rest : list A),
   (exists safety_proof : ((x :: rest) <> nil),
      (hd_never_fail A (x :: rest) safety_proof) = x))).
Proof.
  unfold not.
  intros.
  assert (witness : ((x :: rest) = nil -> False)).
    exact (cons_cant_equal_nil A x rest).
  
  refine (ex_intro _ witness _).
  simpl.
  exact (eq_refl).
Qed.

Definition tl_error (A : Type) (l : list A) 
  : option (list A) 
:= match l with
   | nil => None
   | _ :: tail => Some tail
   end.

Theorem correctness_of_tl_error :
   (forall A:Type,
   (forall (x : A) (lst : list A),
   (tl_error A nil) = None /\ (tl_error A (x :: lst)) = Some lst)).
Proof.
  intros.
  refine (conj _ _).
    simpl.  trivial.
    simpl.  trivial.
Qed.

Theorem hd_tl :
   (forall A:Type,
   (forall (default : A) (x : A) (lst : list A),
   (hd default (x::lst)) :: (tl (x::lst)) = (x :: lst))).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, l ++ nil = l)).
Proof.
  intros.
  elim l.
    simpl. trivial.
 
    intros.
    simpl.
    rewrite H.
    trivial.
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros.
  simpl.
  trivial.
Qed.


Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  simpl.
  case l,m,n.
    simpl. trivial.
    
    simpl. trivial.

    simpl. trivial.

    simpl. trivial.

    simpl.
    replace (app l nil) with (l).
    replace (app l nil) with (l).
    trivial.

    pose (witness := app_nil_r A l).
    rewrite (witness).
    trivial.

    pose (witness := app_nil_r A l).
    rewrite (witness).
    trivial.

    simpl.
    replace (app l nil) with (l).
    trivial.

    pose (witness := app_nil_r A l).
    rewrite (witness).
    trivial.

    simpl.

    admit.
    
    admit.
Qed.

Theorem app_cons_not_nil : forall A (x y:list A) (a:A), nil <> x ++ a :: y.
Proof.
  intros.
  unfold not.
  intros.
  case x, y.
    simpl in H.
    discriminate H.

    discriminate H.
    
    discriminate H.

    discriminate H.
Qed.
    
