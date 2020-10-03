Require Import Coq.Lists.List.
Import ListNotations.

Definition queue (T : Type) : Type := list T * list T.

Definition empty_queue (T : Type) : queue T := (@nil T, @nil T).

Definition enqueue { T } (x : T) (q : queue T) : queue T := (fst q, cons x (snd q)).

Definition dequeue_helper { T } (l : list T) : option (T * queue T) :=
  match l with
  | nil => @None (T * queue T)
  | cons x xs => @Some (T * queue T) (x, (xs, nil))
end.

Definition dequeue { T } (q : queue T) : option (T * queue T) := 
  match q with
  | (nil, l) => dequeue_helper (rev l)
  | (cons x xs, l) => @Some (T * queue T) (x, (xs, l))
end.

Definition toList { T } (q : queue T) : list T := fst q ++ rev (snd q).

Lemma enqueue_correct:
  forall T (x : T) (q : queue T),
    toList (enqueue x q) = toList q ++ [x].
Proof.
  intros.
  unfold enqueue.
  unfold toList.
  simpl.
  apply app_assoc.
Qed.

Lemma dequeue_some_sound:
  forall T (x : T) (q q' : queue T),
    dequeue q = Some (x, q') ->
    toList q = x :: toList q'.
Proof.
  intros.
  destruct q eqn:Eqb.
  + inversion H. unfold toList. simpl.
Qed.

Lemma dequeue_none_sound:
  forall T (q : queue T),
    dequeue q = None ->
    toList q = [].
Proof.
  (* TO BE COMPLETED *)
Qed.

Lemma dequeue_some_complete:
  forall T (x : T) (xs : list T) (q : queue T),
  toList q = x :: xs ->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  (* TO BE COMPLETED *)
Qed.

Lemma dequeue_none_complete:
  forall T (q : queue T),
    toList q = [] ->
    dequeue q = None.
Proof.
  (* TO BE COMPLETED *)
Qed.

Theorem dequeue_none_correct:
  forall T (q : queue T),
    toList q = [] <->
    dequeue q = None.
Proof.
  (* TO BE COMPLETED *)
Qed.

Theorem dequeue_some_correct:
forall T (q : queue T) (x : T) (xs : list T),
  toList q = x :: xs <->
  exists (q' : queue T),
    dequeue q = Some (x, q') /\
    toList q' = xs.
Proof.
  (* TO BE COMPLETED *)
Qed.
