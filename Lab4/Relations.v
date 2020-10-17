Require Import List.
Import ListNotations.

(** Relations **)

(* A relation over a type `A` is a function `A -> A -> Prop` *)
Definition relation (A: Type) : Type := A -> A -> Prop.

Definition equivalent_relations {A: Type} (r1 r2: relation A) :=
  forall x y, r1 x y <-> r2 x y.

Notation "r1 == r2" := (equivalent_relations r1 r2) (at level 30).

Definition compose {A: Type} (r1 r2: relation A): relation A :=
  fun x y => (exists z, r1 x z /\ r2 z y).

Notation "r1 ** r2" := (compose r1 r2) (at level 20).

(* destruct existentials in context *)
Ltac destruct_exists :=
  match goal with
  | H: exists x, _ |- _ => let freshX := fresh x in destruct H as [ freshX ]
  end.

Lemma compose_assoc:
  forall A (r1 r2 r3: relation A),
    r1 ** (r2 ** r3) == (r1 ** r2) ** r3.
Proof.
  intros. 
  unfold compose. unfold equivalent_relations. split.
    + intros. destruct H. destruct H. destruct H0. destruct H0. exists x1. split. 
      - exists x0. split.
        * apply H.
        * apply H0.
      - apply H1.
    + intros. destruct H. destruct H. destruct H. destruct H. exists x1. split.
      - apply H.
      - exists x0. split.
        * apply H1.
        * apply H0.
Qed.

Fixpoint rel_pow {A: Type} (r: relation A) (n: nat): relation A :=
  match n with
  | 0 => fun a1 a2 => a1 = a2
  | S n => compose r (rel_pow r n)
  end.

Notation "r ^^ n" := (rel_pow r n) (at level 15).

Fixpoint is_path {A: Type} (r: relation A) (x: A) (p: list A) (y: A): Prop :=
  match p with
  | [] => x = y
  | z :: zs => r x z /\ is_path r z zs y
  end.

Lemma path_to_power: forall A (r: relation A) (p: list A) (y x: A),
    is_path r x p y -> (r ^^ (length p)) x y.
Proof.
   induction p. 
    + intros. simpl. simpl in H. apply H.
    + simpl. intros. unfold compose. destruct H.  exists a.  split.
      - apply H.
      - pose proof IHp y a. apply H1. apply H0. 
Qed.

Lemma is_path_cons:
  forall A (r: relation A) (x y z: A) (p: list A),
    r x y ->
    is_path r y p z ->
    is_path r x (y :: p) z.
Proof.
  intros. simpl. split.
    + apply H.
    + apply H0.
Qed.

Lemma power_to_path:
  forall A (r: relation A) (n: nat) (x y: A),
    (r ^^ n) x y ->
    exists p: list A, is_path r x p y /\ length p = n.
Proof.
Admitted.

Lemma path_compose:
  forall (A: Type) (r: relation A) (p1 p2: list A) (x y z: A),
    is_path r x p1 y ->
    is_path r y p2 z ->
    is_path r x (p1 ++ p2) z.
Proof.
Admitted.

Lemma power_compose:
  forall A (r : relation A) (n1 n2: nat),
    (r ^^ n1) ** (r ^^ n2) == r ^^ (n1 + n2).
Proof.
Admitted.

(* `star r` is the reflexive and transitive closure of the relation `R` *)
Definition star { A } (r : relation A): A -> A -> Prop :=
  fun x y => (exists n, (r ^^ n) x y).

(* The reflexive and transitive closure of a relation is reflexive *)
Lemma star_refl:
  forall A (r: relation A) x,
    star r x x.
Proof.
Admitted.

(* The reflexive and transitive closure of a relation is transitive *)
Lemma star_trans:
  forall A (r : relation A) x y z,
    star r x y ->
    star r y z ->
    star r x z.
Proof.
Admitted.

(* The transitive closure of a relation "contains" the relation *)
Lemma star_step:
  forall A (r: relation A) x y,
    r x y ->
    star r x y.
Proof.
Admitted.

Lemma star_1n:
  forall A (r: relation A) x y z,
    r x y ->
    star r y z ->
    star r x z.
Proof.
Admitted.


(** Transition Systems and Reachability **)

(* A transition system with states `Q` and alphabet `A` is a pair with:                *)
(* - An `initial` function of type `Q -> Prop` that says which states are initial      *)
(* - A function `r` of type `Q -> A -> Q -> Prop` such that `r q1 a q2` holds when the *)
(*   transition system has a transition from state `q1` to `q2` labelled by `a`        *)
Record Transition_System (Q A : Type) := new_Transition_System {
  initial : Q -> Prop;
  r : Q -> A -> Q -> Prop
}.

Arguments initial { Q A }.
Arguments r { Q A }.
Arguments new_Transition_System { Q A }.


(* Example *)
Definition ex_Q := nat.
Inductive ex_A := inc (n : nat) | dec (n : nat).

Definition ex_Counter_1 := {|
  initial := fun q => q = 0;
  r := fun q1 a q2 => match a with
               | inc 1 => q2 = q1 + 1
               | dec 1 => q2 = q1 - 1
               | _ => False
               end
  |}.

Definition ex_Counter_n := {|
  initial := fun q => q = 0;
  r := fun q1 a q2 => match a with
               | inc n => q2 = q1 + n
               | dec n => q2 = q1 - n
               end
  |}.

Notation "ts |- q1 ~ a '~>' q2" := (r ts q1 a q2) (at level 20).
Notation "ts |- q1 '~>' q2" := (exists a, ts |- q1 ~a~> q2) (at level 20).
Notation "ts |- q1 '~>*' q2" := (star (fun p q => ts |- p ~> q) q1 q2) (at level 20).
Notation "ts |- q1 '~>^' n q2" := (((fun p q => ts |- p ~> q) ^^ n) q1 q2) (at level 20, n at level 1).

Definition reachable { Q A } (ts : Transition_System Q A) (q: Q) : Prop :=
  exists q_i, initial ts q_i  /\  ts |- q_i ~>* q.


(** Traces of Transition Systems **)

(* A trace an a starting state `start` and sequences of states and labels *)
Record Trace (Q A : Type) := new_Trace {
  start: Q;
  states : list Q;
  labels : list A
}.

Arguments start { Q A }.
Arguments states { Q A }.
Arguments labels { Q A }.
Arguments new_Trace { Q A }.

Definition in_trace { Q A } q (tr : Trace Q A) : Prop :=
  q = start tr \/ In q (states tr).

(* `is_trace_aux ts q0 xs` holds when there are transition in `ts`   *)
(* starting from (not necessarily initial) state `q0`, going through *)
(* the states in `qs` and with labels in `xs`                        *)
Fixpoint is_trace_aux { Q A } (ts : Transition_System Q A)
  (q0 : Q) (qs : list Q) (xs : list A) : Prop :=
  match qs, xs with
  | nil, nil => True
  | q :: qs', x :: xs' => r ts q0 x q /\ is_trace_aux ts q qs' xs'
  | _, _ => False
  end.

(* A `trace` of `ts` starts with an initial state and then has valid transitions *)
Definition is_trace { Q A } (ts: Transition_System Q A) (tr: Trace Q A) : Prop :=
  is_trace_aux ts (start tr) (states tr) (labels tr) /\
  initial ts (start tr).

Lemma is_trace_aux_nil:
  forall Q A (ts : Transition_System Q A) q, is_trace_aux ts q nil nil.
Proof.
Admitted.

(* A trace can be extended from the front with another transition *)
Lemma is_trace_aux_cons:
  forall A Q (ts : Transition_System Q A) q1 q2 qs x xs,
    ts |- q1 ~x~> q2 ->
    is_trace_aux ts q2 qs xs ->
    is_trace_aux ts q1 (q2 :: qs) (x :: xs).
Proof.
Admitted.


(** Equivalence between reachability and traces **)

(* All the states `q` that appear in the states of a trace are reachable *)
Lemma in_trace_reachable:
  forall A Q (ts : Transition_System Q A) (tr : Trace Q A) q,
    is_trace ts tr ->
    in_trace q tr ->
    reachable ts q.
Proof.
Admitted.

(* Conversely, if a state `q` is reachable, there exists a trace containing it *)
Lemma reachable_in_trace:
  forall A Q (ts : Transition_System Q A) q,
    reachable ts q ->
    exists tr,
      is_trace ts tr /\
      in_trace q tr.
Proof.
Admitted.


(** Simulation Relations **)

Definition simulates { QC QA A }
  (tsc : Transition_System QC A) (tsa : Transition_System QA A) (R : QC -> QA -> Prop) :=

  (forall qc, initial tsc qc -> exists qa, R qc qa /\ initial tsa qa) /\
  (forall qc1 a qc2 qa1, tsc |- qc1 ~a~> qc2 -> R qc1 qa1 -> exists qa2, R qc2 qa2 /\ tsa |- qa1 ~a~> qa2).

(* The counter with `inc 1` and `dec 1` simulates the counter with `inc n` and `dec n`. *)
(* The relation used to show the simulation is the diagonal or identity relation.       *)
Lemma simulates_counter_1_n: simulates ex_Counter_1 ex_Counter_n (fun qc qa => True).
Proof.
Admitted.

(* If a transition system `tsc` simulates a transition system `tsa`, then for every trace of *)
(* `tsc`, there exists a trace of `tsa` with the same labels.                                *)
Lemma simulates_inclusion_observable:
  forall QC QA A (tsc : Transition_System QC A) (tsa : Transition_System QA A) (R : QC -> QA -> Prop) trc,
    simulates tsc tsa R ->
    is_trace tsc trc ->
    exists tra,
      is_trace tsa tra /\
      labels trc = labels tra.
Proof.
Admitted.
