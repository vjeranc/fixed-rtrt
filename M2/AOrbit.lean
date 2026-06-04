import M2.Orbits

namespace Primitive
namespace Tree

def W (f : List Tree) : List Tree := rList (tList f)

def A : Nat → List Tree
  | 0 => []
  | n + 1 => W (A n) ++ [leaf]

def hForest (f : List Tree) : List Tree := tList (rList (tList f))

def NoReturn : Prop :=
  ∀ n, rList (A n) = A n → n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4

def StartsNonleaf (f : List Tree) : Prop :=
  ∃ c cs rest, f = .node (c :: cs) :: rest

def TopBoundaryMismatch (f : List Tree) : Prop :=
  StartsNonleaf f ∧ ∃ init, f = init ++ [leaf]

theorem rList_A_succ (n : Nat) :
    rList (A (n + 1)) = leaf :: tList (A n) := by
  simp [A, W, rList_append, rList_involutive, leaf]

theorem hForest_eq_tList_A_succ (n : Nat) :
    hForest [.node (A n)] = tList (A (n + 1)) := by
  unfold hForest
  simp +decide [A]
  congr

theorem hForest_fixed_iff_A_palindrome (n : Nat) :
    hForest [.node (A n)] = [.node (A n)] ↔ rList (A (n + 1)) = A (n + 1) := by
  unfold hForest
  have h1 : tList (rList (tList [node (A n)])) = tList (A (n + 1)) := by
    apply hForest_eq_tList_A_succ
  have h2 : tList (A (n + 1)) = [node (A n)] ↔ A (n + 1) = leaf :: tList (A n) := by
    constructor <;> intro h <;> simp_all +decide
    cases h' : A (n + 1) <;> simp_all +decide
    cases ‹Tree›
    simp_all +decide
    cases ‹List Tree› <;> simp_all +decide
    · rw [← h, tList_involutive]
    · cases ‹Tree›
      simp_all +decide [tList]
  rw [h1, h2, rList_A_succ]
  exact eq_comm

theorem forestSize_A (n : Nat) : forestSize (A n) = n := by
  induction n with
  | zero => simp [A]
  | succ n ih =>
    simp only [A, W, forestSize_append]
    rw [forestSize_rList, forestSize_tList, ih]
    simp

theorem A_ends_leaf_of_pos {n : Nat} (hn : n > 0) :
    ∃ init, A n = init ++ [leaf] := by
  cases n with
  | zero => omega
  | succ m => exact ⟨W (A m), rfl⟩

theorem A_succ_length_eq_leftSpine (n : Nat) :
    (A (n + 1)).length = leftSpine (A n) + 1 := by
  simp [A, W, rList_length, tList_length_eq_leftSpine, Nat.add_comm]

private theorem A_succ_starts_leaf_of_rfixed (n : Nat)
    (hfix : rList (A (n + 1)) = A (n + 1)) :
    ∃ rest, A (n + 1) = leaf :: rest := by
  have hstart : ∃ rest, rList (A (n + 1)) = leaf :: rest := by
    simp [A, W, rList_append, leaf]
  simpa [hfix] using hstart

private theorem A_rest_ne_nil_of_starts_leaf_ge_two {n : Nat} {rest : List Tree}
    (hn : n ≥ 2) (hA : A n = leaf :: rest) : rest ≠ [] := by
  intro hrest
  have hsize := congrArg forestSize hA
  rw [forestSize_A] at hsize
  simp [hrest, leaf] at hsize
  omega

theorem A_startsNonleaf_or_next_startsNonleaf (n : Nat) (hn : n ≥ 2) :
    StartsNonleaf (A n) ∨ StartsNonleaf (A (n + 1)) := by
  cases hA : A n with
  | nil =>
      have hsize := congrArg forestSize hA
      rw [forestSize_A] at hsize
      simp at hsize
      omega
  | cons t rest =>
      cases t with
      | node cs =>
          cases cs with
          | cons c cs =>
              exact Or.inl ⟨c, cs, rest, rfl⟩
          | nil =>
              have hrest : rest ≠ [] := A_rest_ne_nil_of_starts_leaf_ge_two hn hA
              have htail_ne : rList (tList rest) ≠ [] :=
                rList_ne_nil (tList_ne_nil_of_ne_nil hrest)
              rcases List.exists_cons_of_ne_nil htail_ne with ⟨c, cs, hcs⟩
              refine Or.inr ⟨c, cs, [leaf], ?_⟩
              change W (A n) ++ [leaf] = .node (c :: cs) :: [leaf]
              rw [hA]
              simp [W, rList, leaf, hcs]

theorem A_startsNonleaf_not_rfixed {n : Nat}
    (h : StartsNonleaf (A (n + 1))) :
    rList (A (n + 1)) ≠ A (n + 1) := by
  intro hfix
  rcases h with ⟨c, cs, rest, hA⟩
  rcases A_succ_starts_leaf_of_rfixed n hfix with ⟨rest', hleaf⟩
  rw [hA] at hleaf
  injection hleaf with hhead _
  simp [leaf] at hhead

theorem A_depth_one_bounded_gap (n : Nat) (hn : n ≥ 2) :
    TopBoundaryMismatch (A n) ∨ TopBoundaryMismatch (A (n + 1)) := by
  rcases A_startsNonleaf_or_next_startsNonleaf n hn with h | h
  · exact Or.inl ⟨h, A_ends_leaf_of_pos (by omega)⟩
  · exact Or.inr ⟨h, A_ends_leaf_of_pos (by omega)⟩

theorem A_no_consecutive_rfixed_ge_two (n : Nat) (hn : n ≥ 2) :
    ¬ (rList (A n) = A n ∧ rList (A (n + 1)) = A (n + 1)) := by
  rintro ⟨hfix, hfix_next⟩
  cases n with
  | zero => omega
  | succ m =>
      have hstart := A_succ_starts_leaf_of_rfixed m hfix
      rcases hstart with ⟨rest, hA⟩
      have hrest : rest ≠ [] := A_rest_ne_nil_of_starts_leaf_ge_two hn hA
      have htail_ne : rList (tList rest) ≠ [] :=
        rList_ne_nil (tList_ne_nil_of_ne_nil hrest)
      have hshape : A (m + 1 + 1) = .node (rList (tList rest)) :: [leaf] := by
        change W (A (m + 1)) ++ [leaf] = .node (rList (tList rest)) :: [leaf]
        rw [hA]
        simp [W, rList, leaf]
      have hstart_next := A_succ_starts_leaf_of_rfixed (m + 1) hfix_next
      rcases hstart_next with ⟨rest_next, hnext⟩
      rw [hshape] at hnext
      injection hnext with hhead _
      have hnil : rList (tList rest) = [] := by
        simpa [leaf] using hhead
      exact htail_ne hnil

theorem A_rfixed_bounded_gap_depth_one (n : Nat) (hn : n ≥ 2) :
    rList (A n) ≠ A n ∨ rList (A (n + 1)) ≠ A (n + 1) := by
  by_contra h
  push_neg at h
  exact A_no_consecutive_rfixed_ge_two n hn ⟨h.1, h.2⟩

end Tree
end Primitive
