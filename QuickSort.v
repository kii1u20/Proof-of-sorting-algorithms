Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Import ListNotations.
From Coq Require Export Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
From Coq Require Import Lia.


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

(* ------------  Definition or sorted, is_a_sorting_algorithm, partition ------------ *)
Inductive sorted : list nat -> Prop :=
    | sorted_nil:
        sorted []
    | sorted_1 : forall x,
        sorted [x]
    | sorted_cons : forall x y l,
        x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(* A direct, word for word copy of the F* implementation of partition *)
(* Splits a list in two, based on a predicate function *)
Fixpoint partition {A : Type} (f : A -> bool) (l : list A) : list A * list A :=
    match l with
    | [] => ([], [])
    | hd :: tl =>
        let (l1, l2) := partition f tl in
        if f hd then (hd :: l1, l2) else (l1, hd :: l2)
    end.

Compute (partition (fun x => x <=? 3) [1; 2; 3; 4; 5; 6]).

(* n represents the length of the original list l. As partitioning is 
   guaranteed to return two lists that have length <= n, 
   the recursion will reach the base case before n reaches 0 or exactly on 0, 
   at which point it will break. *)
(* The rest of the implementation is an exact copy of the F* implementation *)
Fixpoint quicksort (l: list nat) (n: nat){struct n} : list nat :=
  match l, n with
  | _, 0 => []
  | [], S _ => []
  | pivot :: tl, S n' =>
      let '(lo, hi) := partition (fun x => x <=? pivot) tl in
        quicksort lo n' ++ [pivot] ++ quicksort hi n'
      (* quicksort lo (length lo) ++ [pivot] ++ quicksort hi (length hi) *)
  end.

(* After some experimentation, I was able to get closer to a proof using the below
definition, which instead of first partitioning the lists and then recursively calling
quicksort, does the partitioning in the recursive call, taking the appropriate list
from the tuple returned by partition *)

(* Fixpoint quicksort (l: list nat) (n: nat){struct n} : list nat :=
  match l, n with
  | _, 0 => []
  | [], S _ => []
  | pivot :: tl, S n' =>
        quicksort (fst(partition (fun x => x <=? pivot) tl)) n' ++ pivot :: 
        quicksort (snd(partition (fun x => x <=? pivot) tl)) n'
      (* quicksort lo (length lo) ++ [pivot] ++ quicksort hi (length hi) *)
  end. *)

(* Since quicksort requires the length of the list to be passed as a parameter,
this function is called only using a list, and passes its length as well to quicksort *)
Definition sort (l: list nat) : list nat :=
  quicksort l (length l).

Compute (quicksort [200;3;4;1;8] 5).

(* A copy of the mem function from the F* implementation. 
Checks if an element is inside of a list. *)
Fixpoint mem (i : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | hd :: tl => if hd <=? i then true else mem i tl
  end.

(* Proves that if an element x exists in l1 ++ l2, it exists in either l1 or l2 *)
Lemma append_mem : forall (l1 l2 : list nat) (x : nat),
  mem x (l1 ++ l2) = orb (mem x l1) (mem x l2).
Proof.
  intros l1 l2 x. induction l1 as [| hd tl IH].
  - reflexivity.
  - simpl. bdestruct (hd <=? x).
    + simpl. reflexivity.
    + exact IH.
Qed.

(* an incredibly hard to prove lemma. Proves that if l1 and l2 are sorted,
and l1 is a list such that all elements inside are smaller or equal to the pivot,
and l2 is a list such that all elements inside are larger or equal to the pivot,
l1 ++ pivot :: l2 is also sorted *)
(* The proof is complex, relying havily on inversion to break down hypothesis further, 
and on the definition of sorted.
Adding a lot of comments to the code below would only complicate matters futher, so it is best
that this be run interactively in an IDE, and then it will make sense. *)
Lemma sorted_concat : forall (l1 l2 : list nat) (pivot : nat),
  sorted l1 -> sorted l2 ->
  (forall x, In x l1 -> x <= pivot) ->
  (forall x, In x l2 -> x >= pivot) ->
  sorted (l1 ++ pivot :: l2).
Proof.
  intros l1 l2 pivot H1 H2 H3 H4. induction l1 as [| hd tl IH].
  + simpl. induction l2 as [| hd2 tl2 IH2].
    - apply sorted_1.
    - apply sorted_cons. apply H4. simpl. left. reflexivity. apply H2.
  + simpl. induction l2 as [| hd2 tl2]. (* induction of l2 is needed as well *)
    - bdestruct (hd <=? pivot). destruct tl. (* need to prove that the head is smaller than pivot, so that sorted holds *)
      * apply sorted_cons. apply H. apply sorted_1.
      * simpl. apply sorted_cons. inversion H1. apply H6. 
        apply IH. inversion H1. exact H8. intros x H_in_tl. apply H3. simpl. right. apply H_in_tl.
      * induction tl as [| hd3 tl3 IH3].
        -- apply sorted_cons. apply H3. simpl. left. reflexivity. apply IH. exact H2. (*or apply sorted_nil*) 
           intros x H0. inversion H0.
        -- simpl. apply sorted_cons. inversion H1. exact H6. apply IH. inversion H1. 
           exact H8. intros x H_in_tl3. apply H3. simpl. right. simpl in H_in_tl3. (* simpl here to make it clear how exact does the proof. Not needed. *) 
           exact H_in_tl3.
    - destruct tl as [| hd3 tl3]. (* destruct and induction to the same thing here. Either works *)
      * simpl. apply sorted_cons. apply H3. simpl. left. reflexivity. apply IH. 
        apply sorted_nil. intros x H_in_l2. apply H3. simpl. right. simpl in H_in_l2. (* simpl here to make it clear how exact does the proof. Not needed. *) 
        exact H_in_l2.
      * simpl. apply sorted_cons. inversion H1. exact H5. apply IH. inversion H1. 
        exact H7. intros x H_in_tl3. apply H3. simpl. right. simpl in H_in_tl3. (* simpl here to make it more clear how exact does the proof. Not needed. *) 
        exact H_in_tl3.       
Qed. 

(* This one I was unable to prove. It is supposed to show the behaviour of the partition function,
that when f is applied to each element in l and returns true, those elements are in l1, and when false is returned
those elements are in l2. Finally, it proves that each element of l is in either l1 or l2. I tried tactics from the proof of
sorted_concat, but with no success. *)
Lemma partition_mem : forall (f: nat -> bool) (l l1 l2 : list nat),
  partition f l = (l1, l2) ->
  (forall x, In x l1 -> f x = true) /\
  (forall x, In x l2 -> f x = false) /\
  (forall x, In x l <-> In x l1 \/ In x l2).
Proof.
  intros f l. induction l as [| hd tl IH].
  - intros l1 l2 H. simpl in H. inversion H. subst. split.
    + intros x H_in. inversion H_in.
    + split.
      * intros x H_in. inversion H_in.
      * intros x. split.
        -- intros H_in. inversion H_in.
        -- intros H_in. inversion H_in. exact H0. exact H0. (* shorten by using ; after inversion *)
  - intros l1 l2 H. split.
    + intros x H_in.
  Admitted.

(* This is an additional lemma I added. It proves that if l1 and l2 are empty lists, (l1, l2) = ([], [])
This lemma was in an attempt to prove the permutation l (sort l), but ended up not used. *)
Lemma empty_lists_equal : forall (l1 l2 : list nat),
  l1 = [] -> l2 = [] -> (l1, l2) = ([], []).
Proof.
  intros l1 l2 H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

(* Another lemma I added. This one proves that the partition function produces two lists that when
appended together are a permutation of the input list. 
Again, in an attempt to prove permutation l (sort l). *)
Lemma partition_permutation : forall (f : nat -> bool) (l l1 l2 : list nat),
  partition f l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  intros f l. induction l as [| hd tl IH].
  - intros l1 l2 H. simpl in H. inversion H. apply Permutation_refl.
  - intros l1 l2 H. simpl in H.
    destruct (partition f tl) as [l1' l2'] eqn:E.
    destruct (f hd). inversion H. subst. apply perm_skip. auto.
    + inversion H. apply Permutation_cons_app. apply IH. rewrite H1. reflexivity.
Qed.

(* Another lemma I added. This proves that the result of the partition function is equal to
taking the fst and snd element of the tuple produced. 
Again, in an attempt to prove permutation l (sort l). *)
Lemma partition_pair : forall (f : nat -> bool) (l : list nat),
  partition f l =
(fst (partition f l), snd (partition f l)).
Proof.
  intros f l. induction l as [| hd tl IH].
  - simpl. reflexivity.
  - simpl. destruct (partition f tl) as [l1 l2]. destruct (f hd) eqn:E.
    + reflexivity.
    + reflexivity.
Qed.

(* Another lemma I added. This proves that the input list is a permutation of the 
fst and snd element of the tuple produced by the partition function. Essentially the same as partition_permutation,
but was needed in an attempt to prove permutation l (sort l), as I was not able to fit the partition_permutation
lemma into the proof. *)
Lemma partition_permutation2 : forall (f : nat -> bool) (l l1 l2 : list nat),
  Permutation l 
  (fst(partition f l) ++ snd(partition f l)).
Proof.
  intros. apply partition_permutation with f. apply partition_pair.
Qed. 

(* Another theorem I added. This one proves that, given a concrete function for f,
partition produces a permutation of the pivot concatinated to the input list, and the pivot
concatinated to the output of the partition function appended together. 
This one was used in the most successful attempt to prove permutation l (sort l) *)
Theorem partition_permutation3 : forall (pivot : nat) (l lo hi : list nat),
  partition (fun x => x <=? pivot) l = (lo, hi) -> Permutation (pivot :: l) (pivot :: (lo ++ hi)).
Proof.
  intros pivot l lo hi H.
  apply perm_skip.
  apply partition_permutation with (fun x => x <=? pivot).
  exact H.
Qed.

(* Another lemma I added. This one proves that when l' is an empty list, sort a :: [] results in [a] *)
Lemma sort_single_element_perm: forall a l',
  l' = [] -> 
  Permutation [a] (sort (a :: l')).
Proof.
  intros a l' H.
  rewrite H.
  apply Permutation_refl.
Qed.

(* Another lemma I added. This one shows that when l is not empty, partition creates two lists, l1 and l2.
Used in an attempt to prove permutation l (sort l), ultimately not used. *)
Lemma partition_produces_two_lists_nonempty : forall (A : Type) (f : A -> bool) (l : list A),
  l <> [] -> exists l1 l2, partition f l = (l1, l2).
Proof.
  intros A f l Hnonempty.
  destruct l as [|hd tl].
  - contradiction Hnonempty; reflexivity.
  - simpl. destruct (partition f tl) as [l1 l2]. destruct (f hd) eqn:E.
    + exists (hd :: l1). exists l2. reflexivity.
    + exists l1. exists (hd :: l2). reflexivity. 
Qed.

(* Another lemma I added. This one shows that when l is empty, partition creates two empty lists. 
Needed in an attempt to prove permutation l (sort l), ultimately not used. *)
Lemma partition_empty_list : forall (A : Type) (f : A -> bool),
  partition f [] = ([], []).
Proof.
  intros A f.
  simpl.
  reflexivity.
Qed.    

(* --- Most promising proof of permutatil l (sort l) --- *)

(* quicksort_unfolded in proven WHEN the second definition of quicksort from the top of the file
is used. Uncomment that, and comment the currently uncommented one for this to show as complete. *)

(* Lemma quicksort_unfolded : forall (l: list nat) (le: nat),
  quicksort l le = match l, le with
                   | [], _ => []
                   | _, 0 => []
                   | hd::tl, S le' => quicksort (fst(partition (fun x => x <=? hd) tl)) le' ++ [hd] ++ 
                               quicksort (snd(partition (fun x => x <=? hd) tl)) le'
                   end.
Proof.
  intros. destruct l as [| hd tl]. induction le as [| le' IH].
  - intuition.
  - simpl. reflexivity.
  - induction le as [| le' IH]. induction tl as [| hd' tl' IHtl].
    + intuition.
    + simpl. intuition.
    + simpl. intuition.
Qed.

Theorem sort_perm2: forall l (n : nat), Permutation l (sort l).
Proof.
  intros. induction l as [| hd tl IH]. induction n as [| n' IHn].
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_refl.
  - induction n as [| n' IHn].
    + unfold sort. rewrite quicksort_unfolded. apply Permutation_cons_app.
      apply Permutation_trans with
      (l' := (fst(partition (fun x : nat => x <=? hd) tl)) ++ 
      (snd(partition (fun x : nat => x <=? hd) tl))). apply partition_permutation2. auto. auto.
      apply Permutation_app.
      Admitted. *)
(* ----------------------------------------------------- *)  

(* An attempt to prove Permutation l (sort l) *)
Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros l. induction l as [| a l' IHl']. 
  - apply Permutation_refl.
  - apply perm_trans with (a :: sort l').
    + destruct sort. apply perm_skip. apply IHl'. apply perm_skip. apply IHl'.
    + destruct sort. apply sort_single_element_perm. apply Permutation_nil. 
      apply Permutation_sym. exact IHl'.
      rewrite <- IHl'. unfold sort. simpl. remember (partition (fun x => x <=? a) l') as part eqn:Heqpart.
      destruct part as [lo hi]. symmetry in Heqpart. apply partition_permutation3
      in Heqpart. apply Permutation_cons_app.
      Admitted.

(* Finally, where the correctness of quicksort should be proved *)
Lemma sort_correct (l: list nat) : is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros al. split.
  - induction al as [| hd tl IH].
   + reflexivity.
   + 
  Admitted.
          
