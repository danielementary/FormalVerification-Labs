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
  + trivial. simpl. discriminate.
Qed.

Lemma rev_empty:
  forall T (l: list T),
  rev l = [] ->
  l = [].
Proof.
  intros.
  rewrite <- H.
  induction l.
  + trivial.
  + pose proof rev_app_distr. pose proof cons_app_same. rewrite -> H1. rewrite -> H0. simpl.
    unfold rev in H. pose proof blabla_not_empty. apply H2 in H. contradiction.
 Qed.

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

Lemma dequeue_none_complete:
  forall T (q : queue T),
    toList q = [] ->
    dequeue q = None.
Proof.
  intros.
  unfold dequeue.
  destruct q.
  destruct l.
  + unfold toList in H. unfold fst in H. unfold snd in H. simpl in H. rewrite -> H. trivial.
  + destruct Some.
    - discriminate.
    - trivial.
Qed.

Lemma dequeue_none_sound:
  forall T (q : queue T),
    dequeue q = None ->
    toList q = [].
Proof.
  intros.
  destruct q.
  destruct l.
  + destruct l0.
    - unfold toList. unfold fst. unfold snd. unfold rev. simpl. trivial.
    - unfold toList. unfold fst. unfold snd. simpl. destruct (rev l0) eqn:Eqb.
                                                    * simpl. inversion H. pose proof rev_empty. apply H0. rewrite -> Eqb in H1. simpl in H1. discriminate.
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
  intros.
  destruct q.
  unfold toList in H.
  unfold fst in H.
  unfold snd in H.
  simpl in H.
  destruct l.
  destruct l0.
    - discriminate.
    - simpl in H. unfold dequeue. simpl. rewrite -> H. exists (xs, []). split.
      + trivial.
      + unfold toList. unfold fst. unfold snd. simpl. apply app_nil_r. 
    - unfold dequeue. exists (l, l0). inversion H. split.
      + trivial.
      + unfold toList. unfold fst. unfold snd.  trivial.
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

Theorem dequeue_none_correct:
  forall T (q : queue T),
    toList q = [] <->
    dequeue q = None.
Proof.
  intros.
  split.
  + apply dequeue_none_complete.
  + apply dequeue_none_sound.
Qed.

Theorem dequeue_some_correct:
  forall T (q : queue T) (x : T) (xs : list T),
    toList q = x :: xs <->
    exists (q' : queue T),
      dequeue q = Some (x, q') /\
      toList q' = xs.
Proof.
  intros.
  split.
  + pose proof dequeue_some_complete. apply H.
  +  intros. inversion H. pose proof dequeue_some_sound T x q x0. destruct H0. rewrite -> H2 in H1. apply H1. apply H0.
Qed.
