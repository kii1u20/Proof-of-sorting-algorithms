module InsertionSort

// The below definition is from the tutorial on QuickSort
// https://fstar-lang.org/tutorial/book/part1/part1_quicksort.html?highlight=permutation
// --- Permutation ---    
let rec count (#a:eqtype) (x:a) (l:list a)
  : nat
  = match l with
    | hd::tl -> (if hd = x then 1 else 0) + count x tl
    | [] -> 0

let is_permutation (#a:eqtype) (l m:list a) =
  forall x. count x l = count x m

// I did try defining my own implementation of permutation, and it worked, but the proof became a lot harder, and I was unable to 
// prove correctness of quicksort usinng the definitions below. This was because the SMT solver could not complete the check 
// if both lists contain the same elements on generic lists l1 l2. It works if a concrete list is passed, like 
// [1;2;3] [3;2;1]. But not on generic lists.

// let rec member (x: nat) (l: list nat) : Tot bool =
//   match l with
//   | [] -> false
//   | h::t -> if x = h then true else member x t

// let rec same_elements (l1: list nat) (l2: list nat) : Tot bool (decreases (List.length l1)) =
//   match l1 with
//   | [] -> true
//   | h::t -> member h l2 && same_elements t l2

// // Check if all elements of l1 exist in l2, and then if all elements of l2 exist
// // in l1. Then checks if the lenght of the lists are the same.

// let permutation (l1: list nat) (l2: list nat) : bool =
//   same_elements l1 l2 && same_elements l2 l1 && List.length l1 = List.length l2

// let rec lemma_member_insert (x: nat) (l: list nat) : Lemma (member x (insert x l)) =
//   match l with
//   | [] -> ()
//   | h::t -> 
//     lemma_member_insert x t; 
//     assert (member x (insert x (h :: t)))
// --- Permutation ---

(* ------------  Definition or sorted, is_a_sorting_algorithm, sorted_list, insert and sort ------------ *)
//As compared to the coq definition, this returns true or false, indicating if the list is sorted or not.
let rec sorted (l: list nat) : bool =
  match l with
  | [] -> true
  | [x] -> true
  | x::y::ys -> if x <= y then sorted (y::ys) else false

// A refinement type on list nat, to indicate that the list is sorted.
type sorted_list = l:list nat {sorted l}

// An exact copy of the Coq definition, using <= instead of <=? since this is special Coq syntax for boolean comparison.
let rec insert (i: nat) (l: list nat): Tot (r: list nat {is_permutation r (i :: l)}) =
  match l with
  | [] -> [i]
  | h::t -> if i <= h then i::h::t else h::(insert i t)

// Exact copy of the Coq definition
let rec sort (l: list nat): list nat =
  match l with
  | [] -> []
  | h::t -> insert h (sort t)

// Exact copy of the Coq definition. The return type of the function f (the sorting function) is annotated as Tot,
// indicating that it is a total function, which will always produce a result of type list nat.
type is_a_sorting_algorithm (f: list nat -> Tot (list nat)) : Type =
  forall (l: list nat). 
    (is_permutation l (f l)) /\ (sorted (f l))

(* ------------ Proving theorems ------------ *)
// when a is bigger than y, y will always be the head of the list.
// The refinement type on a ensures that a is greater than y. The input list l is also of type sorted_list.
// This helps prove that inserting an element into a sorted list preserves the order.
let insert_preserves_order (y: nat) (a: nat {a > y}) (l: sorted_list): Lemma
  // (requires a > y) this is not necessary as I have the refinement type on a.
  (ensures (insert a (y::l) = y::(insert a l)))
= assert (a > y ==> insert a (y::l) = y::(insert a l))

// Proves that given a sorted list l, inserting an element a into l results in a sorted list.
// The refinement type sorted_list is again used here to enforce the requirement of l being sorted.
// This lemma uses pattern matching on l, and a recursive call to itself to prove that insert produces a sorted list.
let rec insert_sorted (a: nat) (l: sorted_list): Lemma 
  // (requires sorted l) this is not needed as I am using the sorted_list refinement type.
  (ensures sorted (insert a l))
= match l with
  | [] -> ()
  | h::t -> if a <= h then ()
            else insert_sorted a t

// Follows the Coq strategy precisely. The inductive case proves that inserting
// the head of the list into the sorted tail produces a sorted list, proving that
// sort produces a sorted list.
let rec sort_sorted (l: list nat): Lemma (sorted (sort l)) =
  match l with
  | [] -> ()
  | h::t -> 
    sort_sorted t; // Prove that sorting the tail results in a sorted list
    insert_sorted h (sort t) // Prove that inserting the head into this sorted tail results in a sorted list

// Proves that the list returned by insert is a permutation of the input list with the element to be inserted concatenated.
// The refinement type sorted_list is not used here, as proving a permutation does not require a sorted list.
let rec insert_perm (x:nat) (l:list nat) : Lemma
  (ensures (is_permutation (insert x l) (x::l))) =
  match l with
  | [] -> ()
  | hd::tl -> 
    if x <= hd then () //essentially does this: assert (is_permutation (insert x (hd::tl)) (x::hd::tl))
    else insert_perm x tl

// This proves that sort produces a permutation of the input list.
// Again, sorted_list is not used as the type of l, since proving permutations does not require the list to be sorted.
let rec sort_perm (l: list nat) : Lemma
  (ensures (is_permutation l (sort l))) =
  match l with
  | [] -> ()
  | hd::tl -> 
    sort_perm tl; // Inductive hypothesis: the tail of the list is a permutation of its sort
    // Lemma: inserting an element into a list results in a permutation. The proof is accepted without this,
    // but it make it clearer as to why it's true.
    insert_perm hd (sort tl);
    // Now I need to show that the original list is a permutation of its sort
    assert (is_permutation (hd::tl) (sort (hd::tl)))
    
// This proves that inserting an element into a list returned by sort results in a permutation of the original list concatinated
// with the element to be inserted.
// The refinement type here requires that when the input list is returned by sort, it is a permutation of the original list.
// Currently, commenting out this lemma from insertion_sort_correct does not affect the proof, but
// a couple of days ago it did, so I do not know what changed by itself :). Z3 was unable to prove 
// assert (is_permutation (hd::tl) (sort (hd::tl))); without this lemma, even though sort_perm is similar.
let cons_insert_perm (x: nat) (l: list nat {is_permutation l (sort l)}) : Lemma
  // (requires (is_permutation l (sort l))) This is not needed as I have the refinement type on l.
  (ensures (is_permutation (x::l) (insert x (sort l)))) =
  insert_perm x (sort l)

// Proof of the correctness of insertion sort using the definition of is_a_sorting_algorithm.
// Doing ensures(is_a_sorting_algorithm sort) does not work, giving that Z3 is unable to prove the assertions.
// Even though the definition of is_a_sorting_algorithm is exactly the same as the ensures clause below.
let insertion_sort_correct (l: list nat) : Lemma
  (ensures ((is_permutation l (sort l)) /\ (sorted (sort l)))) =
    match l with
    | [] -> ()
    | hd::tl -> 
      sort_perm tl; // Prove that is_permutation tl (sort tl) holds
      sort_sorted tl; // Prove that sorted (sort tl) holds
      cons_insert_perm hd tl; // Prove that is_permutation (hd::tl) (insert hd (sort tl)) holds
      assert (is_permutation (hd::tl) (sort (hd::tl))); // Given the above proofs, Z3 proves the assertion, proving is_permutation l (sort l))
      insert_sorted hd (sort tl); // Prove that sorted (insert hd (sort tl)) holds
      // Having proven that sorted(sort tl) holds and that inserting hd into the sorted tail holds,
      // Z3 is able to assert that sorted (sort l) holds.
      assert (sorted (sort (hd::tl)))
    | _ -> () // A case to satisfy the pattern matching. Should/is never be reached.


