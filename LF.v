(*** Functional Programming in Coq (Basics) ***)
(** Data and Functions **)
(* Days of the Week *)
Inductive day : Type :=
    monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
    monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(** Homework Submission Guidelines **)
(* I have read it. *)

(* Booleans *)
Inductive bool : Type :=
    true
  | false.

Definition negb (b:bool) : bool :=
  match b with
    true  => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    true  => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    true  => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
    true, true, true => true
  | _, _, _          => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Types *)
Check true.
Check (negb true).
Check negb.

(* New Types from Old *)
Inductive rgb : Type :=
    red
  | green
  | blue.

Inductive colour : Type :=
    black
  | white
  | primary (p : rgb).

Definition monochrome (c : colour) : bool :=
  match c with
    black     => true
  | white     => true
  | primary q => false
  end.

Definition isblue (c : colour) : bool :=
  match c with
    black        => false
  | white        => false
  | primary blue => true
  | primary _    => false
  end.

(* Tuples *)
Inductive bit : Type :=
    B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0).

Definition all_zero (nb : nybble) : bool :=
  match nb with
      (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _)     => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).

(* Modules *)
Module NatPlayground.
(* Numbers *)
Inductive nat : Type :=
    O
  | S (n : nat).
Inductive nat' : Type :=
    stop
  | tick (foo : nat').

Definition pred (n : nat) : nat :=
  match n with
      O    => O
    | S n => n
  end.
Check (S (S (S (S O)))).
End NatPlayground.
Check (S (S (S (S O)))).

Definition minusTwo (n : nat) : nat :=
  match n with
      O        => O
    | S O      => O
    | S (S n) => n
  end.
  Compute (minusTwo 4).

Check S.
Check pred.
Check minusTwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    O        => true
  | S O      => false
  | S (S n) => evenb n
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
      O    => m
    | S n => S (plus n m)
  end.

Compute (plus 3 2).
(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)
Fixpoint mult (n m : nat) : nat :=
  match n with
      O    => O
    | S n => plus m (mult n m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
    O , _      => O
  | S _ , O    => n
  | S n, S m => minus n m
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
      O   => S O
    | S p => mult base (exp base p)
  end.

Fixpoint 
(** Proof by Simplification **)

(** Proof by Rewriting **)
(** Proof by Case Analysis **)
(* More on Notation (Optional) *)
(* Fixpoints and Structural Recursion (Optional) *)
(** More Exercises **)


(*** Proof by Induction (Induction) ***)
(** Proof by Induction **)
(** Proofs Within Proofs **)
(** Formal vs. Informal Proof **)
(** More Exercises **)


(*** Working with Structured Data (Lists) ***)
(** Pairs of Numbers **)
(** Lists of Numbers **)
(** Reasoning About Lists **)
(* Induction on Lists *)
(* Search *)
(* List Exercises, Part 1 *)
(* List Exercises, Part 2 *)
(** Options **)
(** Partial Maps **)


(*** Polymorphism and Higher-Order Functions (Poly) ***)
(** Polymorphism **)
(* Polymorphic Lists *)
(* Polymorphic Pairs *)
(* Polymorphic Options *)
(** Functions as Data **)
(* Higher-Order Functions *)
(* Filter *)
(* Anonymous Functions *)
(* Map *)
(* Fold *)
(* Functions That Construct Functions *)
(** Additional Exercises **)


(*** More Basic Tactics (Tactics) ***)
(** The apply Tactic **)
(** The apply with Tactic **)
(** The injection and discriminate Tactics **)
(** Using Tactics on Hypotheses **)
(** Varying the Induction Hypothesis **)
(** Unfolding Definitions **)
(** Using destruct on Compound Expressions **)
(** Review **)
(** Additional Exercises **)


(*** Logic in Coq (Logic) ***)
(** Logical Connectives **)
(* Conjunction *)
(* Disjunction *)
(* Falsehood and Negation *)
(* Truth *)
(* Logical Equivalence *)
(* Existential Quantification *)
(** Programming with Propositions **)
(** Applying Theorems to Arguments **)
(** Coq vs. Set Theory **)
(* Functional Extensionality *)
(* Propositions and Booleans *)
(* Classical vs. Constructive Logic *)


(*** Inductively Defined Propositions (IndProp) ***)
(** Inductively Defined Propositions **)
(* Inductive Definition of Evenness *)
(** Using Evidence in Proofs **)
(* Inversion on Evidence *)
(* Induction on Evidence *)
(** Inductive Relations **)
(** Case Study: Regular Expressions **)
(* The remember Tactic *)
(** Case Study: Improving Reflection **)
(** Additional Exercises **)
(* Extended Exercise: A Verified Regular-Expression Matcher *)


(*** Total and Partial Maps (Maps) ***)
(** The Coq Standard Library **)
(** Identifiers **)
(** Total Maps **)
(** Partial maps **)


(*** The Curry-Howard Correspondence (ProofObjects) ***)
(** Proof Scripts **)
(** Quantifiers, Implications, Functions **)
(** Programming with Tactics **)
(** Logical Connectives as Inductive Types **)
(* Conjunction *)
(* Disjunction *)
(* Existential Quantification *)
(* True and False *)
(** Equality **)
(* Inversion, Again *)


(*** Induction Principles (IndPrinciples) ***)
(** Basics **)
(** Polymorphism **)
(** Induction Hypotheses **)
(** More on the induction Tactic **)
(** Induction Principles in Prop **)
(** Formal vs. Informal Proofs by Induction **)
(* Induction Over an Inductively Defined Set *)
(* Induction Over an Inductively Defined Proposition *)


(*** Properties of Relations (Rel) ***)
(** Relations **)
(** Basic Properties **)
(** Reflexive, Transitive Closure **)



(*** Simple Imperative Programs (Imp) ***)
(** Arithmetic and Boolean Expressions **)
(* Syntax *)
(* Evaluation *)
(* Optimization *)
(** Coq Automation **)
(* Tacticals *)
(* Defining New Tactic Notations *)
(* The omega Tactic *)
(* A Few More Handy Tactics *)
(** Evaluation as a Relation **)
(* Inference Rule Notation *)
(* Equivalence of the Definitions *)
(* Computational vs. Relational Definitions *)
(** Expressions With Variables **)
(* States *)
(* Syntax *)
(* Notations *)
(* Evaluation *)
(** Commands **)
(* Syntax *)
(* Desugaring notations *)
(* The Locate command *)
(* More Examples *)
(** Evaluating Commands **)
(* Evaluation as a Function (Failed Attempt) *)
(* Evaluation as a Relation *)
(* Determinism of Evaluation *)
(** Reasoning About Imp Programs **)
(** Additional Exercises **)


(*** Lexing and Parsing in Coq (ImpParser) ***)
(** Internals **)
(* Lexical Analysis *)
(* Parsing *)
(** Examples **)


(*** An Evaluation Function for Imp (ImpCEvalFun) ***)
(** A Broken Evaluator **)
(** A Step-Indexed Evaluator **)
(** Relational vs. Step-Indexed Evaluation **)
(** Determinism of Evaluation Again **)


(*** Extracting ML from Coq (Extraction) ***)
(** Basic Extraction **)
(** Controlling Extraction of Specific Types **)
(** A Complete Example **)
(** Discussion **
(* *Going Further **)

(*** More Automation (Auto) ***)
(** The auto Tactic **)
(** Searching For Hypotheses **)
(* The eapply and eauto variants *)


(*** Postscript ***)