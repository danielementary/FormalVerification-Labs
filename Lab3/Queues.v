Require Import Coq.Lists.List.
Import ListNotations.

Definition queue (T : Type) : Type := list T * list T.

Definition empty_queue (T : Type) : queue T := (@nil T, @nil T).

Definition enqueue { T } (x : T) (q : queue T) : queue T := (fst q, cons x (snd q)).

Definition dequeue { T } (q : queue T) : option (T * queue T) := 
  match q with
  | (nil, l) => match rev l with
                | nil => @None (T * queue T)
                | cons x xs => @Some (T * queue T) (x, (xs, nil))
                end
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

Lemma super_lemma:
  forall T (q : queue T),
    q = (@nil T, @nil T) ->
    toList q = [].
Proof.
  intros.
  rewrite -> H.
  unfold toList.
  simpl.
  reflexivity.
Qed.


Lemma dequeue_none_complete:
  forall T (q : queue T),
    toList q = [] ->
    dequeue q = None.
Proof.
  intros.
  unfold dequeue. destruct q. destruct l.
  + unfold toList in H. unfold fst in H. unfold snd in H. simpl in H. rewrite -> H. trivial.
  + destruct Some. 
    - discriminate.
    - trivial.
Qed.

Lemma options_equal_inl_equal:
  forall (T A : Type) (t1 t2: T)(a1 a2: A),
      Some(t1, a1) = Some(t2, a2) ->
      (t1,a1) = (t2, a2).
Proof.
  intros.
  inversion H.
  apply injective_projections.
  + unfold fst. trivial.
  + unfold snd. trivial.
Qed.

Lemma add_parenthesis_to_cons:
  forall T (x: T)(l: list T),
    x::l++[] = (x::l) ++ [].
Proof.
  intros.
  simpl.
  trivial.
Qed.

Lemma add_empty_does_nothing:
  forall T (x: T)(l: list T),
    (x::l)++[] = (x::l).
Proof.
  intros.
  induction (x::l).
  + trivial.
  + simpl. rewrite -> IHl0. trivial.
Qed.

Lemma dequeue_some_sound:
  forall T (x : T) (q q' : queue T),
    dequeue q = Some (x, q') ->
    toList q = x :: toList q'.
Proof.
  intros.
  destruct q.
  destruct q'.
  destruct l.
  + destruct l0.
    - destruct l1.
      * destruct l2.
        ** unfold toList. unfold fst. unfold snd. unfold rev. simpl. discriminate.
        ** unfold toList. unfold fst. unfold snd. simpl. discriminate.
      * unfold toList. unfold fst. unfold snd. simpl. discriminate.
    - unfold toList. unfold fst. unfold snd. simpl. unfold dequeue in H. simpl in H. destruct (rev l0 ++ [t]).
                                                                                     * discriminate.
                                                                                     * inversion H. simpl.
                                                                                       pose proof add_parenthesis_to_cons as X. 
                                                                                       rewrite -> X.
                                                                                       pose proof add_empty_does_nothing as Y.
                                                                                       rewrite -> Y. trivial.
  + unfold dequeue in H. inversion H. unfold toList. unfold fst. unfold snd. simpl. trivial.
Qed.

Lemma cons_app_same:
  forall T (l: list T)(t: T),
    t::l = [t] ++ l.
Proof.
  intros.
  simpl.
  trivial.
Qed.

Lemma blabla_not_empty:
  forall T (l: list T)(t: T),
    l++ [t] <> [].
Proof.
  intros.
  simpl.
  trivial.
  induction l.
  + trivial. simpl. discriminate.
  + pose proof app_cons_not_nil. trivial. simpl. discriminate.
Qed.

Lemma rev_empty:
  forall T (l: list T),
  rev l = [] ->
  l = [].
Proof.
  intros.
  rewrite <- H. induction l.
  + trivial.
  +  pose proof rev_app_distr. pose proof cons_app_same. pose proof rev_app_distr. 
      rewrite -> H1. rewrite -> H0. simpl. unfold rev in H. pose proof blabla_not_empty. apply H3 in H. contradiction.
 Qed.

Lemma dequeue_none_sound:
  forall T (q : queue T),
    dequeue q = None ->
    toList q = [].
Proof.
  intros.
  destruct q. destruct l.
  + destruct l0.
    - unfold toList. unfold fst. unfold snd. unfold rev. simpl. trivial.
    - unfold toList. unfold fst. unfold snd. simpl. destruct (rev l0) eqn:Eqb.
                                                    * simpl. inversion H. inversion H1. pose proof rev_empty. apply H0. rewrite -> Eqb in H1. simpl in H1. discriminate.
                                                    * inversion H. rewrite Eqb in H1. simpl in H1. discriminate.
  + unfold dequeue in H. discriminate.
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
