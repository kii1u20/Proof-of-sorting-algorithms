Require Import Utf8.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From Coq Require Export Bool.Bool.
Import ListNotations.
From Coq Require Import Lia.

(* From the labs, we have seen some Notations used:
Notation "( x , y )" := (pair x y).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

But I found that those exist in the Coq Standard Library, so I use them directly.
*)

(* ------------ Definitions from the Perm.v file, straight copy ------------ *)
Definition geb (n m : nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.
Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.
Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.
Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(* ------------  Definition or sorted, is_a_sorting_algorithm, insert and sort ------------ *)

Inductive sorted : list nat -> Prop :=
    | sorted_nil:
        sorted []
    | sorted_1 : forall x,
        sorted [x]
    | sorted_cons : forall x y l,
        x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).
    (* Again, I am using the Coq Standard library for the definition of Permutation *)

Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.
Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

(* ------------ Proving theorems ------------ *)

(* when a is bigger than y, y will always be the head of the list *)
Lemma insert_preserves_order :
  forall a y l, a > y -> insert a (y :: l) = y :: insert a l.
Proof.
  intros a y l Hgt. simpl.
  bdestruct (a <=? y).
  - lia. (* This contradicts the hypothesis a > y, so this case is impossible. *)
  - reflexivity.
Qed.

(* Here, I have slit every sub proof into its own bullet level for ease of understanding *)
Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl. (* apply simpl to all branches, else this adds a lot of unecessary steps *)
  - apply sorted_1. (* case when the list has only one element, proved by a contructor from sorted *)
  - bdestruct (a <=? x).
    + apply sorted_cons. (* case when a <= x. *)
      * exact H. (* in the context *)
      * apply sorted_1.
    + apply sorted_cons. (* case when a > x. *)
      * lia. (* proved by the lia tactic *)
      * apply sorted_1.
  - bdestruct (a <=? x). (* a <= x <= y *)
   (* Here I get (a :: x :: y :: l). First I prove that a:: is correct by proving that a <= x.
      Then I prove that x:: is correct by proving that x <= y. 
      Lastly y::l is proved because it's already in the context *)
    + apply sorted_cons.
      * exact H0. (* in the context *) 
      * apply sorted_cons. 
        -- exact H. 
        -- exact S.
    + bdestruct (a <=? y). (* x < a <= y *)
     (* Here I get (x :: a :: y :: l). First I prove that x:: is correct by proving that x <= a.
        Then I prove that a:: is correct by proving that a <= y. 
        Lastly y::l is proved because it's already in the context *)
      * apply sorted_cons. 
        -- lia. (* proved by the lia tactic *)
        -- apply sorted_cons.
          --- exact H1. 
          --- exact S.
      * apply sorted_cons. (* x <= y < a *)
        -- exact H. 
        (* Since H1 states that a > y, y will always be the head of the list. This holds even when a is inserted into a list
           that already has y as head, or if a is first inserted, and then y is added as head*)
        -- rewrite <- insert_preserves_order.
          --- exact IHS. 
          --- exact H1. 
Qed.

(* This is the same proof as above, but I've used auto as much as possible, 
   and used the ; token to shorten the proof as much as possible. *)
Lemma insert_sorted_short:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S; simpl.
  - apply sorted_1.
  - bdestruct (a <=? x).
    + apply sorted_cons. exact H. apply sorted_1.
    + apply sorted_cons. lia. apply sorted_1.
  - bdestruct (a <=? x).
    + apply sorted_cons; auto. apply sorted_cons; auto.
    + bdestruct (a <=? y).
      * apply sorted_cons. lia. apply sorted_cons; auto.
      * apply sorted_cons. exact H. rewrite <- insert_preserves_order; auto. 
Qed.      

(* This proves that lists returned by insertion sort are sorted *)
Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros l. induction l as [| h tl IHl'].
 (*  base case. Apply the contructor for sorted empty list.
    Note: simpl is not needed here, because Coq evaluated sort[] to [], 
    without me needing to explicitly tell it to do so *)
  - apply sorted_nil.
  (* simpl is not needed here as well, but added for clarity. *)
  - simpl. apply insert_sorted. (* or insert_sorted_short *) exact IHl'.
Qed.

(* This proves that the list returned by insert is a permutation of the input list *)
Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros x l. induction l as [| a l' IHl']. 
  (* From Coq.Sorting.Permutations, Permutation_refl proves that the a list is a permutation of itself *)
  - simpl. apply Permutation_refl.
  - simpl. bdestruct (x <=? a).
    + apply Permutation_refl. (* case x <= a *)
    + apply perm_trans with (a :: x :: l'). (* since x > a, a will always be the head of the list *)
      * apply perm_swap. (* swapping the order of elements keeps the Permutation property *)
      * rewrite IHl'. apply Permutation_refl. (* induction hypothesis proves the Permutation property *)
Qed.

(* This proves that sort produces a permutation of the input list *)
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l as [| a l' IHl'].
  (* Note: simpl is not needed here, because Coq evaluated sort[] to [], 
    without me needing to explicitly tell it to do so *)
  - apply Permutation_refl.
  (* Note: simpl is not needed here as well, because Coq will evaluate (sort (a :: l'))
     to (insert a (sort l')) on its own, but adding simpl makes the last case, "apply insert_perm"
     easier to understand, as the evaluation step is shown. *)
  - simpl. apply perm_trans with (a :: sort l').
    + apply perm_skip. (* adding the same element to the beginning of the list allows us to skip it *) exact IHl'.
    + apply insert_perm. (* lemma proven above *)
Qed.

(* This proves that insertion sort is a sorting algorithm *)    
Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros al. split. (* split the goal into two subgoals *)
  - apply sort_perm. (* apply the Theorem I have already proved. *)
  - apply sort_sorted. (* apply the Theorem I have already proved. *)
Qed.
