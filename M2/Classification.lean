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

theorem rList_A_succ (n : Nat) :
    rList (A (n + 1)) = leaf :: tList (A n) := by
  simp [A, W, rList_append, rList_involutive, leaf]

theorem hForest_eq_tList_A_succ (n : Nat) :
    hForest [.node (A n)] = tList (A (n + 1)) := by
  unfold hForest;
  simp +decide [ A ];
  congr

theorem hForest_fixed_iff_A_palindrome (n : Nat) :
    hForest [.node (A n)] = [.node (A n)] ↔ rList (A (n + 1)) = A (n + 1) := by
  unfold hForest;
  have h1 : tList (rList (tList [node (A n)])) = tList (A (n + 1)) := by
    apply hForest_eq_tList_A_succ;
  have h2 : tList (A (n + 1)) = [node (A n)] ↔ A (n + 1) = leaf :: tList (A n) := by
    constructor <;> intro h <;> simp_all +decide;
    cases h' : A ( n + 1 ) <;> simp_all +decide;
    cases ‹Tree› ; simp_all +decide;
    cases ‹List Tree› <;> simp_all +decide;
    · rw [ ← h, tList_involutive ];
    · cases ‹Tree› ; simp_all +decide [ tList ];
  rw [ h1, h2, rList_A_succ ];
  exact eq_comm

theorem bookend_core_r_fixed {core : Tree}
    (hfix : PrimFixedM2 (.node [leaf, core, leaf])) :
    r core = core := by
  cases hfix;
  rename_i h₁ h₂;
  have := r_fixed_of_m2 _ h₂;
  cases this' : core ; simp_all +decide [ Tree.r ]

theorem bookend_core_padded {core : Tree}
    (hfix : PrimFixedM2 (.node [leaf, core, leaf])) :
    hForest [core, leaf] = [core, leaf] := by
  cases hfix;
  unfold hForest;
  rename_i h1 h2;
  have := m2_orbit_pair ( Tree.node [ leaf, core, leaf ] ) h2;
  simp_all +decide [ Tree.t, Tree.r ]

theorem bookend_core_full_padded {core : Tree}
    (hfix : PrimFixedM2 (.node [leaf, core, leaf])) :
    Prim core ∧ r core = core ∧ hForest [core, leaf] = [core, leaf] := by
  refine ⟨?_, bookend_core_r_fixed hfix, bookend_core_padded hfix⟩
  · rcases hfix with ⟨hp, _⟩
    rcases core with ⟨cs⟩
    cases cs with
    | nil => simp [Prim, prim, squeezeOuter]
    | cons c cs =>
      exact Prim_core_of_Prim_bookend hp (by simp [leaf])

theorem forestSize_A (n : Nat) : forestSize (A n) = n := by
  induction n with
  | zero => simp [A]
  | succ n ih =>
    simp only [A, W, forestSize_append]
    rw [forestSize_rList, forestSize_tList, ih]
    simp

def FullPaddedCore (n : Nat) (core : Tree) : Prop :=
  r core = core ∧
  hForest [core, .node (A n)] = [core, .node (A n)] ∧
  Prim (.node [core, .node (A n)])

instance : DecidablePred (FullPaddedCore n) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def baseCore (n : Nat) : Tree :=
  .node (tList [.node (A (n + 1))])

def liftCore (n : Nat) (sub : Tree) : Tree :=
  .node (tList [sub, .node (A (n + 1))])

theorem Prim_core_leaf_of_Prim_bookend {core : Tree}
    (hp : Prim (.node [leaf, core, leaf])) :
    Prim (.node [core, leaf]) := by
  simp only [Prim] at hp ⊢
  simp only [prim, primList, squeezeOuter, primChildrenRaw, squeezeMid] at hp ⊢
  simp only [primInner_leaf] at hp ⊢
  rcases h : core.primInner with ( _ | ⟨ x ⟩ ) <;> simp_all +decide

theorem bookend_core_is_fullPadded {core : Tree}
    (hfix : PrimFixedM2 (.node [leaf, core, leaf])) :
    FullPaddedCore 0 core := by
  have ⟨_, hr, hh⟩ := bookend_core_full_padded hfix
  refine ⟨hr, ?_, ?_⟩
  · show hForest [core, .node (A 0)] = [core, .node (A 0)]
    simp only [A]; exact hh
  · show Prim (.node [core, .node (A 0)])
    simp only [A]
    exact Prim_core_leaf_of_Prim_bookend hfix.1

def knownPrimFixedM2Trees : List Tree :=
  [leaf, .node [leaf], orbit2a, orbit2b, orbit5a, orbit5b, orbit14a, orbit14b]

theorem hForest_leaf_padding_iff (n : Nat) :
    hForest [leaf, .node (A n)] = [leaf, .node (A n)] ↔ rList (A (n + 1)) = A (n + 1) := by
  convert hForest_fixed_iff_A_palindrome n using 1;
  unfold hForest; simp +decide [ tList_cons_leaf ] ;

theorem FullPaddedCore_leaf_palindrome (n : Nat) (h : FullPaddedCore n leaf) :
    rList (A (n + 1)) = A (n + 1) := by
  exact (hForest_leaf_padding_iff n).mp h.2.1

theorem no_FullPaddedCore_node_leaf (n : Nat) (_hn : n ≥ 1) :
    ¬FullPaddedCore n (.node [leaf]) := by
  unfold FullPaddedCore;
  simp +decide [ hForest, tList, rList ]

theorem fc0_nonleaf_implies_PrimFixedM2_bookend (core : Tree)
    (h : FullPaddedCore 0 core) (hne : core ≠ leaf) :
    PrimFixedM2 (.node [leaf, core, leaf]) := by
      have h_prim : Prim (.node [leaf, core, leaf]) := by
        cases h;
        cases core ; simp_all +decide [ Tree.prim ];
        cases ‹List Tree› <;> simp_all +decide [ squeezeMid, squeezeOuter ];
      obtain ⟨h_r, h_hForest, h_prim⟩ := h;
      constructor;
      · assumption;
      · simp +decide [ FixedM2, h_r ];
        convert h_hForest using 1

theorem r_node_tList_A (n : Nat) :
    r (.node (tList [.node (A n)])) = .node (A (n + 1)) := by
  simp +decide [ Tree.r, Tree.rList, A, W ]

theorem hForest_eq_tList_W (cs : List Tree) (n : Nat) :
    hForest [.node cs, .node (A n)] = tList (W cs ++ [.node (A (n + 1))]) := by
  unfold hForest W;
  simp +decide [ ← r_node_tList_A ];
  simp +decide [ tList, rList ]

theorem W_cs_eq_of_hForest {cs : List Tree} {n : Nat}
    (hhf : hForest [.node cs, .node (A n)] = [.node cs, .node (A n)]) :
    W cs ++ [.node (A (n + 1))] = .node (leaf :: tList (A n)) :: tList cs := by
  have h_tList_eq : tList (W cs ++ [.node (A (n + 1))]) = tList (.node (tList [.node (A n)]) :: tList cs) := by
    rw [ ← hForest_eq_tList_W ];
    unfold tList; aesop;
  convert congr_arg tList h_tList_eq using 1;
  · exact?;
  · simp +decide [ tList ]

theorem rList_fixed_head_eq_r_last {cs : List Tree} (hne : cs ≠ [])
    (hr : rList cs = cs) :
    cs.head hne = r (cs.getLast hne) := by
  have h := rList_head_eq_r_last cs hne
  simp only [hr] at h; exact h

theorem nodeCount_head_eq_last_of_palindrome {cs : List Tree} (hne : cs ≠ [])
    (hr : rList cs = cs) :
    nodeCount (cs.head hne) = nodeCount (cs.getLast hne) := by
  have h_head_last : cs.head hne = r (cs.getLast hne) := by
    exact?;
  rw [ h_head_last, nodeCount_r ]

theorem tList_head_eq {a : Tree} {as : List Tree} :
    (tList (a :: as)).head (tList_ne_nil_of_ne_nil (List.cons_ne_nil a as))
    = .node (tList as) := by
  cases a;
  cases ‹List Tree› <;> simp +decide [ tList ]

theorem tList_tail_eq {a : Tree} {as : List Tree} :
    (tList (a :: as)).tail = tList a.children := by
  cases a; simp +decide [ tList ]

theorem primInner_node_singleton_ne {x : Tree} (hx : x ≠ leaf) :
    primInner (.node [x]) ≠ .node [x] := by
  by_contra h_contra
  have h_contra' : primInner x = .node [x] := by
    cases x ; simp_all +decide;
    cases h : primChildrenRaw ‹_› <;> simp_all +decide [ squeezeOuter ];
    · cases h_contra;
      contradiction;
    · unfold contractRoot at * ; aesop;
  exact absurd h_contra' ( by exact no_primInner_wrap x |> fun h => by aesop )

theorem descent_base (n : Nat) (cs : List Tree)
    (hr_cs : rList cs = cs) (_hcs_ne : cs ≠ [])
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_len : (tList cs).dropLast = []) :
    nodeCount (.node cs) = n + 3 /\ rList (A (n + 2)) = A (n + 2) := by
  have htcs_singleton : tList cs = [.node (A (n + 1))] := by
    rcases k : tList cs with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
  have hcs_eq : cs = tList [Tree.node (A (n + 1))] := by
    rw [ ← htcs_singleton, tList_involutive ];
  simp_all +decide;
  constructor;
  · unfold Tree.nodeCount; simp +arith +decide;
    have h_foldr : ∀ (ts : List Tree), List.foldr (fun t acc => acc + t.nodeCount) 0 (tList ts) = forestSize ts := by
      intro ts; exact (by
      convert forestSize_tList ts using 1;
      induction ( tList ts ) <;> simp +arith +decide [ * ]);
    rw [ h_foldr, forestSize_A ];
  · convert rList_A_succ ( n + 1 ) using 1

theorem descent_base_shape (n : Nat) (cs : List Tree)
    (hr_cs : rList cs = cs) (_hcs_ne : cs ≠ [])
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_len : (tList cs).dropLast = []) :
    .node cs = baseCore n ∧ rList (A (n + 2)) = A (n + 2) := by
  have htcs_singleton : tList cs = [.node (A (n + 1))] := by
    rcases k : tList cs with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
  have hcs_eq : cs = tList [Tree.node (A (n + 1))] := by
    rw [ ← htcs_singleton, tList_involutive ];
  constructor
  · rw [hcs_eq]
    rfl
  · simp_all +decide
    convert rList_A_succ (n + 1) using 1

theorem descent_leaf_sub_false (n : Nat) (cs : List Tree)
    (hprim : Prim (.node [.node cs, .node (A n)]))
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_len : (tList cs).dropLast = [leaf]) :
    False := by
  have htcs : tList cs = [leaf, .node (A (n + 1))] := by
    rw [ ← List.dropLast_append_getLast htcs_ne ] ; aesop;
  have hcs : cs = tList [leaf, .node (A (n + 1))] := by
    rw [ ← htcs ];
    exact?;
  have h_primInner : primInner (.node cs) ≠ .node cs := by
    rw [ hcs, tList_cons_leaf ];
    apply primInner_node_singleton_ne;
    exact ne_of_apply_ne ( fun x => x.children ) ( by simp +decide );
  have := hprim;
  unfold Tree.prim at this; simp_all +decide [ squeezeOuter ] ;

theorem descent_recursive_r_helper {n : Nat} {cs : List Tree} {sub : Tree}
    (hcs_eq : cs = tList [sub, .node (A (n + 1))])
    (hhf : tList (rList (tList [.node cs, .node (A n)])) = [.node cs, .node (A n)])
    (_hsub_ne : sub ≠ leaf) : r sub = sub := by
  have := @W_cs_eq_of_hForest; simp_all +decide [ hForest ] ;
  specialize this hhf; simp_all +decide [ tList, W ] ;

private theorem primList_two_eq {a b : Tree} :
    primList [a, b] = [primInner a, primInner b] := by
  simp [squeezeOuter, squeezeMid]

private theorem primInner_eq_of_Prim_two {a b : Tree}
    (h : Prim (.node [a, b])) : primInner a = a ∧ primInner b = b := by
  have h1 : Tree.node (primList [a, b]) = Tree.node [a, b] := h
  have h2 : primList [a, b] = [a, b] := Tree.node.inj h1
  rw [primList_two_eq] at h2
  exact ⟨(List.cons.inj h2).1, (List.cons.inj (List.cons.inj h2).2).1⟩

private theorem cs_length_ge_two {sub : Tree} {n : Nat}
    (hsub_ne : sub ≠ leaf) : (tList [sub, .node (A (n + 1))]).length ≥ 2 := by
  rcases sub with ( _ | ⟨ _ | sub ⟩ ) <;> norm_num [ tList ] at *

private theorem primList_length_ge_two {ts : List Tree} (h : ts.length ≥ 2) :
    (primList ts).length ≥ 2 := by
  rcases ts with ( _ | ⟨ a, _ | ⟨ b, ts ⟩ ⟩ ) <;> simp_all +decide;
  unfold squeezeOuter; simp +arith +decide;
  exact List.length_pos_iff.mpr ( squeezeMid_ne_nil_of_cons _ _ )

private theorem contractRoot_of_length_ge_two {ts : List Tree} (h : ts.length ≥ 2) :
    contractRoot ts = ts := by
  cases h' : ts <;> simp_all +decide;
  induction ‹List Tree› <;> simp_all +decide [ contractRoot ]

private theorem primList_eq_of_contractRoot_eq_length_ge_two
    {cs : List Tree} (h_cr : contractRoot (primList cs) = cs) (h_len : cs.length ≥ 2) :
    primList cs = cs := by
  convert h_cr using 1;
  exact Eq.symm ( contractRoot_of_length_ge_two ( by simpa using primList_length_ge_two h_len ) )

theorem descent_recursive_prim_helper {n : Nat} {cs : List Tree} {sub : Tree}
    (hcs_eq : cs = tList [sub, .node (A (n + 1))])
    (hprim : Prim (.node [.node cs, .node (A n)]))
    (hsub_ne : sub ≠ leaf) : Prim (.node [sub, .node (A (n + 1))]) := by
  have ⟨h_pi_cs, _⟩ := primInner_eq_of_Prim_two hprim
  rw [primInner_node] at h_pi_cs
  have h_cr : contractRoot (primList cs) = cs := Tree.node.inj h_pi_cs
  have h_cs_len : cs.length ≥ 2 := by rw [hcs_eq]; exact cs_length_ge_two hsub_ne
  have h_pl_eq : primList cs = cs := primList_eq_of_contractRoot_eq_length_ge_two h_cr h_cs_len
  show prim (.node [sub, .node (A (n + 1))]) = .node [sub, .node (A (n + 1))]
  simp only [prim]
  congr 1
  have h_tList_inj : Function.Injective tList := by
    intro a b hab; have := congrArg tList hab; simp at this; exact this
  apply h_tList_inj
  rw [← primList_tList, ← hcs_eq, h_pl_eq, hcs_eq]

theorem descent_recursive (n : Nat) (cs : List Tree) (sub : Tree)
    (hr_cs : rList cs = cs)
    (hhf : hForest [.node cs, .node (A n)] = [.node cs, .node (A n)])
    (hprim : Prim (.node [.node cs, .node (A n)]))
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_len : (tList cs).dropLast = [sub])
    (hsub_ne : sub ≠ leaf) :
    FullPaddedCore (n + 1) sub /\ nodeCount (.node cs) = nodeCount sub + n + 3 := by
  have hcs_eq : cs = tList [sub, .node (A (n + 1))] := by
    have hcs_eq : tList cs = [sub, .node (A (n + 1))] := by
      rw [← List.dropLast_append_getLast htcs_ne]; aesop
    rw [← hcs_eq, tList_involutive cs]
  have hsub_r : r sub = sub := descent_recursive_r_helper hcs_eq (by unfold hForest at hhf; exact hhf) hsub_ne
  have hsub_prim : Prim (.node [sub, .node (A (n + 1))]) := descent_recursive_prim_helper hcs_eq hprim hsub_ne
  constructor
  · exact ⟨hsub_r, by unfold hForest; aesop, hsub_prim⟩
  · rw [hcs_eq, nodeCount_unfold]
    rw [forestSize_tList, forestSize_cons, forestSize_cons]; simp +arith +decide
    rw [nodeCount_unfold, forestSize_A]; simp +arith +decide

theorem descent_recursive_shape (n : Nat) (cs : List Tree) (sub : Tree)
    (hr_cs : rList cs = cs)
    (hhf : hForest [.node cs, .node (A n)] = [.node cs, .node (A n)])
    (hprim : Prim (.node [.node cs, .node (A n)]))
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_len : (tList cs).dropLast = [sub])
    (hsub_ne : sub ≠ leaf) :
    sub ≠ leaf ∧ FullPaddedCore (n + 1) sub ∧ .node cs = liftCore n sub := by
  have hcs_eq : cs = tList [sub, .node (A (n + 1))] := by
    have hcs_eq : tList cs = [sub, .node (A (n + 1))] := by
      rw [← List.dropLast_append_getLast htcs_ne]; aesop
    rw [← hcs_eq, tList_involutive cs]
  have hrec := descent_recursive n cs sub hr_cs hhf hprim htcs_ne hlast hds_len hsub_ne
  exact ⟨hsub_ne, hrec.1, by rw [hcs_eq]; rfl⟩

theorem descent_no_ge2 (n : Nat) (cs : List Tree) (d1 d2 : Tree) (ds_rest' : List Tree)
    (hr_cs : rList cs = cs)
    (hprim : Prim (.node [.node cs, .node (A n)]))
    (htcs_ne : tList cs ≠ [])
    (hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)))
    (hds_init_pal : rList (tList cs).dropLast = (tList cs).dropLast)
    (hds_len : (tList cs).dropLast = d1 :: d2 :: ds_rest') :
    False := by
  obtain ⟨d1_cs, hd1_cs⟩ : ∃ d1_cs : List Tree, d1 = .node d1_cs ∧ d1_cs ≠ [] := by
    by_cases hd1_leaf : d1 = leaf;
    · have htList_cs_start_leaf : tList cs = leaf :: (tList cs).tail := by
        rcases k : tList cs with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide;
      have h_contra : primInner (.node cs) ≠ .node cs := by
        have h_contradiction : cs = tList (leaf :: (tList cs).tail) := by
          rw [ ← htList_cs_start_leaf, tList_involutive ];
        rw [ h_contradiction, tList_cons_leaf ];
        apply primInner_node_singleton_ne;
        grind +suggestions
      unfold Tree.Prim at hprim; simp +decide at hprim;
      unfold squeezeOuter at hprim; simp +decide at hprim;
      unfold primInner at h_contra; simp +decide at h_contra;
      exact False.elim <| h_contra <| hprim.1;
    · rcases d1 with ( _ | ⟨ d1_cs ⟩ ) <;> simp_all +decide;
  have h_nodeCount_first_cs : nodeCount (cs.head (by
  rintro rfl; simp_all +decide ;)) = forestSize (d2 :: ds_rest') + n + 3 := by
    have h_nodeCount_first_cs : tList cs = d1 :: d2 :: ds_rest' ++ [.node (A (n + 1))] := by
      rw [ ← hlast, ← hds_len, List.dropLast_append_getLast htcs_ne ];
    have h_nodeCount_first_cs : cs = tList (tList cs) := by
      exact?;
    rw [ ‹tList cs = d1 :: d2 :: ds_rest' ++ [ node ( A ( n + 1 ) ) ] › ] at h_nodeCount_first_cs;
    simp +decide [ h_nodeCount_first_cs ];
    simp +decide [ tList, hd1_cs ];
    rw [ nodeCount_unfold ];
    rw [ forestSize_tList ];
    simp +arith +decide [ forestSize_append ];
    rw [ nodeCount_unfold ] ; simp +arith +decide [ forestSize_A ]
  generalize_proofs at *;
  have h_nodeCount_last_cs : nodeCount (cs.getLast ‹_›) ≤ nodeCount d1 - 1 := by
    have h_nodeCount_last_cs : nodeCount (cs.getLast ‹_›) ≤ forestSize (tList d1_cs) := by
      have h_nodeCount_last_cs : cs = .node (tList (d2 :: ds_rest' ++ [.node (A (n + 1))])) :: tList d1_cs := by
        have h_nodeCount_last_cs : tList cs = d1 :: d2 :: ds_rest' ++ [.node (A (n + 1))] := by
          rw [ ← hlast, ← hds_len, List.dropLast_append_getLast ];
        convert congr_arg tList h_nodeCount_last_cs using 1;
        · exact?;
        · simp +decide [ hd1_cs, tList ];
      rcases x : tList d1_cs <;> simp_all +decide [ List.getLast ];
      rename_i k hk;
      induction' k using List.reverseRecOn with k ih <;> simp_all +decide [ List.getLast ];
      exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( by simp +decide [ forestSize_append ] );
    convert h_nodeCount_last_cs using 1;
    rw [ hd1_cs.1, nodeCount_unfold, forestSize_tList ];
    rw [ Nat.add_sub_cancel_left ];
  have h_nodeCount_d1 : nodeCount d1 ≤ forestSize (d2 :: ds_rest') := by
    have h_nodeCount_d1 : nodeCount d1 = nodeCount (List.getLast (d1 :: d2 :: ds_rest') (by simp)) := by
      have h_nodeCount_d1 : nodeCount (List.head (d1 :: d2 :: ds_rest') (by simp)) = nodeCount (List.getLast (d1 :: d2 :: ds_rest') (by simp)) := by
        apply nodeCount_head_eq_last_of_palindrome;
        aesop;
      exact h_nodeCount_d1;
    have h_nodeCount_last_d2_ds_rest' : nodeCount (List.getLast (d2 :: ds_rest') (by
    simp +decide)) ≤ forestSize (d2 :: ds_rest') := by
      all_goals generalize_proofs at *;
      exact?
    generalize_proofs at *;
    grind;
  have h_nodeCount_first_cs_eq_last_cs : nodeCount (cs.head ‹_›) = nodeCount (cs.getLast ‹_›) := by
    exact?;
  omega

theorem descent_step (n : Nat) (core : Tree)
    (hFC : FullPaddedCore n core) (hne : core ≠ leaf) :
    (nodeCount core = n + 3 ∧ rList (A (n + 2)) = A (n + 2)) ∨
    (∃ sub, FullPaddedCore (n + 1) sub ∧ nodeCount core = nodeCount sub + n + 3) := by
  obtain ⟨hr_core, hhf, hprim⟩ := hFC
  obtain ⟨cs, rfl⟩ : ∃ cs, core = .node cs := ⟨core.children, by cases core; rfl⟩
  have hcs_ne : cs ≠ [] := by intro h; subst h; exact hne rfl
  have hr_cs : rList cs = cs := by
    have := congrArg Tree.children hr_core; simp [Tree.r] at this; exact this
  have hWeq := W_cs_eq_of_hForest hhf
  have htcs_ne : tList cs ≠ [] := tList_ne_nil_of_ne_nil hcs_ne
  have hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)) := by
    replace hWeq := congr_arg List.reverse hWeq ; simp_all +decide [ List.reverse_append ];
    cases h : ( tList cs ).reverse <;> cases h' : ( W cs ).reverse <;> simp_all +decide [ List.getLast ]
  have hds_init_pal : rList (tList cs).dropLast = (tList cs).dropLast := by
    unfold W at hWeq;
    rw [ ← List.dropLast_append_getLast htcs_ne ] at hWeq ; simp_all +decide [ rList ]
  rcases hds_len : (tList cs).dropLast with _ | ⟨d₁, ds_rest⟩
  · exact Or.inl (descent_base n cs hr_cs hcs_ne htcs_ne hlast hds_len)
  · rcases ds_rest with _ | ⟨d₂, ds_rest'⟩
    · by_cases hd₁_leaf : d₁ = leaf
      · exact absurd (descent_leaf_sub_false n cs hprim htcs_ne hlast (by rw [hds_len, hd₁_leaf])) False.elim
      · exact Or.inr ⟨d₁, descent_recursive n cs d₁ hr_cs hhf hprim htcs_ne hlast hds_len hd₁_leaf⟩
    · exact absurd (descent_no_ge2 n cs d₁ d₂ ds_rest' hr_cs hprim htcs_ne hlast hds_init_pal hds_len) False.elim

theorem descent_step_shape (n : Nat) (core : Tree)
    (hFC : FullPaddedCore n core) (hne : core ≠ leaf) :
    (core = baseCore n ∧ rList (A (n + 2)) = A (n + 2)) ∨
    (∃ sub, sub ≠ leaf ∧ FullPaddedCore (n + 1) sub ∧ core = liftCore n sub) := by
  obtain ⟨hr_core, hhf, hprim⟩ := hFC
  obtain ⟨cs, rfl⟩ : ∃ cs, core = .node cs := ⟨core.children, by cases core; rfl⟩
  have hcs_ne : cs ≠ [] := by intro h; subst h; exact hne rfl
  have hr_cs : rList cs = cs := by
    have := congrArg Tree.children hr_core; simp [Tree.r] at this; exact this
  have hWeq := W_cs_eq_of_hForest hhf
  have htcs_ne : tList cs ≠ [] := tList_ne_nil_of_ne_nil hcs_ne
  have hlast : (tList cs).getLast htcs_ne = .node (A (n + 1)) := by
    replace hWeq := congr_arg List.reverse hWeq ; simp_all +decide [ List.reverse_append ];
    cases h : ( tList cs ).reverse <;> cases h' : ( W cs ).reverse <;> simp_all +decide [ List.getLast ]
  have hds_init_pal : rList (tList cs).dropLast = (tList cs).dropLast := by
    unfold W at hWeq;
    rw [ ← List.dropLast_append_getLast htcs_ne ] at hWeq ; simp_all +decide [ rList ]
  rcases hds_len : (tList cs).dropLast with _ | ⟨d₁, ds_rest⟩
  · exact Or.inl (descent_base_shape n cs hr_cs hcs_ne htcs_ne hlast hds_len)
  · rcases ds_rest with _ | ⟨d₂, ds_rest'⟩
    · by_cases hd₁_leaf : d₁ = leaf
      · exact absurd (descent_leaf_sub_false n cs hprim htcs_ne hlast (by rw [hds_len, hd₁_leaf])) False.elim
      · exact Or.inr ⟨d₁, descent_recursive_shape n cs d₁ hr_cs hhf hprim htcs_ne hlast hds_len hd₁_leaf⟩
    · exact absurd (descent_no_ge2 n cs d₁ d₂ ds_rest' hr_cs hprim htcs_ne hlast hds_init_pal hds_len) False.elim

theorem no_FC_ge4 (hNR : NoReturn) (n : Nat) (hn : n ≥ 4) (core : Tree) :
    ¬FullPaddedCore n core := by
  suffices ∀ k, ∀ m ≥ 4, ∀ c : Tree, nodeCount c = k → ¬FullPaddedCore m c by
    exact this (nodeCount core) n hn core rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro m hm c hk hFC'
    by_cases hleaf : c = leaf
    · subst hleaf
      have := FullPaddedCore_leaf_palindrome m hFC'
      rcases hNR (m + 1) this with h | h | h | h <;> omega
    · rcases descent_step m c hFC' hleaf with ⟨_, hpal⟩ | ⟨sub, hFCsub, hsize⟩
      · rcases hNR (m + 2) hpal with h | h | h | h <;> omega
      · exact ih (nodeCount sub) (by omega) (m + 1) (by omega) sub rfl hFCsub

theorem FC_3_only_leaf (hNR : NoReturn) (core : Tree)
    (hFC : FullPaddedCore 3 core) : core = leaf := by
  by_contra hne
  rcases descent_step 3 core hFC hne with ⟨_, hpal⟩ | ⟨sub, hFCsub, _⟩
  · rcases hNR 5 hpal with h | h | h | h <;> omega
  · exact no_FC_ge4 hNR 4 (by omega) sub hFCsub

theorem FC_2_nonleaf_shape (hNR : NoReturn) (core : Tree)
    (hFC : FullPaddedCore 2 core) (hne : core ≠ leaf) :
    core = baseCore 2 := by
  rcases descent_step_shape 2 core hFC hne with ⟨hcore, _⟩ | ⟨sub, hsub_ne, hFCsub, _⟩
  · exact hcore
  · exact absurd (FC_3_only_leaf hNR sub hFCsub) hsub_ne

theorem FC_1_nonleaf_shape (hNR : NoReturn) (core : Tree)
    (hFC : FullPaddedCore 1 core) (hne : core ≠ leaf) :
    core = liftCore 1 (baseCore 2) := by
  rcases descent_step_shape 1 core hFC hne with ⟨_, hpal⟩ | ⟨sub, hsub_ne, hFCsub, hcore⟩
  · rcases hNR 3 hpal with h | h | h | h <;> omega
  · rw [hcore, FC_2_nonleaf_shape hNR sub hFCsub hsub_ne]

theorem FC_0_nonleaf_shape (hNR : NoReturn) (core : Tree)
    (hFC : FullPaddedCore 0 core) (hne : core ≠ leaf) :
    core = baseCore 0 ∨ core = liftCore 0 (liftCore 1 (baseCore 2)) := by
  rcases descent_step_shape 0 core hFC hne with ⟨hcore, _⟩ | ⟨sub, hsub_ne, hFCsub, hcore⟩
  · exact Or.inl hcore
  · exact Or.inr (by rw [hcore, FC_1_nonleaf_shape hNR sub hFCsub hsub_ne])

theorem bookend_baseCore0_eq_orbit5a :
    .node [leaf, baseCore 0, leaf] = orbit5a := by
  simp +decide [baseCore, orbit5a, A, W]

theorem bookend_liftCore0_liftCore1_baseCore2_eq_orbit14a :
    .node [leaf, liftCore 0 (liftCore 1 (baseCore 2)), leaf] = orbit14a := by
  simp +decide [baseCore, liftCore, orbit14a, A, W, rList, tList]

theorem bookend_classification (hNR : NoReturn) (x core : Tree)
    (hfix : PrimFixedM2 x) (hcore_ne : core ≠ leaf)
    (hchildren : x.children = [leaf, core, leaf]) :
    x = orbit5a ∨ x = orbit14a := by
  have hx : x = .node [leaf, core, leaf] := by
    cases x
    simp_all [Tree.children]
  have hbook : PrimFixedM2 (.node [leaf, core, leaf]) := by
    simpa [hx] using hfix
  have hFC : FullPaddedCore 0 core := bookend_core_is_fullPadded hbook
  rcases FC_0_nonleaf_shape hNR core hFC hcore_ne with hcore | hcore
  · left
    rw [hx, hcore]
    exact bookend_baseCore0_eq_orbit5a
  · right
    rw [hx, hcore]
    exact bookend_liftCore0_liftCore1_baseCore2_eq_orbit14a

theorem conditional_classification' (hNR : NoReturn) (x : Tree) (h : PrimFixedM2 x) :
    x = leaf ∨ x = .node [leaf] ∨
    x = orbit2a ∨ x = orbit2b ∨
    x = orbit5a ∨ x = orbit5b ∨
    x = orbit14a ∨ x = orbit14b := by
  by_cases hleaf : x = leaf
  · tauto
  by_cases hsingle_leaf : x = .node [leaf]
  · tauto
  obtain h_cases | h_cases | h_cases :=
    prim_fixedM2_refined_trichotomy x h hleaf hsingle_leaf
  · have hx : x = orbit2a := by
      cases x
      simp_all [Tree.children, orbit2a]
    tauto
  · obtain ⟨core, hcore_ne_leaf, _hcore_prim, hchildren⟩ := h_cases
    rcases bookend_classification hNR x core h hcore_ne_leaf hchildren with hx | hx <;> tauto
  · obtain ⟨cs, hcs_ne, hchildren⟩ := h_cases
    have hx_single : x = .node [.node cs] := by
      cases x
      simp_all [Tree.children]
    have hmx_ne_leaf : m x ≠ leaf := by
      rw [hx_single]
      simp [m, rList, leaf]
    have hmx_ne_single_leaf : m x ≠ .node [leaf] := by
      rw [hx_single]
      have ht_ne : tList (rList cs) ≠ [] := tList_ne_nil_of_ne_nil (rList_ne_nil hcs_ne)
      intro hcontra
      simp [m, rList, leaf] at hcontra
      exact ht_ne hcontra
    have hmxfix : PrimFixedM2 (m x) := PrimFixedM2_m h
    obtain h_cases_m | h_cases_m | h_cases_m :=
      prim_fixedM2_refined_trichotomy (m x) hmxfix hmx_ne_leaf hmx_ne_single_leaf
    · have hmx : m x = orbit2a := by
        cases hmx_tree : m x
        simp_all [Tree.children, orbit2a]
      have hx : x = orbit2b := by
        calc
          x = m (m x) := h.2.symm
          _ = m orbit2a := by rw [hmx]
          _ = orbit2b := m_orbit2a
      tauto
    · obtain ⟨core, hcore_ne_leaf, _hcore_prim, hchildren_m⟩ := h_cases_m
      rcases bookend_classification hNR (m x) core hmxfix hcore_ne_leaf hchildren_m with hmx | hmx
      · have hx : x = orbit5b := by
          calc
            x = m (m x) := h.2.symm
            _ = m orbit5a := by rw [hmx]
            _ = orbit5b := m_orbit5a
        tauto
      · have hx : x = orbit14b := by
          calc
            x = m (m x) := h.2.symm
            _ = m orbit14a := by rw [hmx]
            _ = orbit14b := m_orbit14a
        tauto
    · cases x
      simp_all +decide [Tree.r]

theorem conditional_classification (hNR : NoReturn) (x : Tree) (h : PrimFixedM2 x) :
    x ∈ knownPrimFixedM2Trees := by
  have hm := conditional_classification' hNR x h
  simp [knownPrimFixedM2Trees] at hm ⊢
  tauto

theorem classification_or_noreturn (x : Tree) (h : PrimFixedM2 x) :
    x ∈ knownPrimFixedM2Trees ∨ ∃ n, n ≥ 5 ∧ rList (A n) = A n := by
  by_cases hNR : NoReturn
  · left; exact conditional_classification hNR x h
  · right
    unfold NoReturn at hNR
    push_neg at hNR
    obtain ⟨n, hn, hne⟩ := hNR
    have h3 : rList (A 3) ≠ A 3 := by
      simp +decide [A, W, rList]
    have : n ≠ 3 := fun heq => h3 (heq ▸ hn)
    exact ⟨n, by omega, hn⟩

end Tree
end Primitive
