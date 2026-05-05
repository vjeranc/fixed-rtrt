import M2.Prim

namespace Primitive
namespace Tree

def FixedM2 (x : Tree) : Prop := m (m x) = x

def PrimFixedM2 (x : Tree) : Prop := Prim x ∧ FixedM2 x

theorem FixedM2_prim_of_FixedM2 (x : Tree) (h : FixedM2 x) : FixedM2 (prim x) := by
  unfold FixedM2 at *
  calc m (m (prim x)) = prim (m (m x)) := by rw [← prim_m, ← prim_m]
    _ = prim x := by rw [h]

theorem FixedM2_leaf : FixedM2 leaf := by simp [FixedM2, m]

theorem PrimFixedM2_leaf : PrimFixedM2 leaf :=
  ⟨by simp [Prim, prim, squeezeOuter], FixedM2_leaf⟩

def orbit2a : Tree := .node [leaf, leaf]
def orbit2b : Tree := .node [.node [leaf]]

theorem m_orbit2a : m orbit2a = orbit2b := by
  unfold orbit2a orbit2b;
  simp +decide [ Primitive.Tree.rList, Primitive.Tree.tList ]

theorem m_orbit2b : m orbit2b = orbit2a := by
  apply Eq.symm; exact (by
  fapply congr_arg;
  simp [rList, tList])

theorem FixedM2_orbit2a : FixedM2 orbit2a := by
  unfold orbit2a
  generalize_proofs at *;
  unfold FixedM2;
  simp +decide [ Tree.rList, Tree.tList ]

theorem Prim_orbit2a : Prim orbit2a := by
  unfold Prim
  simp [orbit2a];
  rfl

theorem Prim_orbit2b : Prim orbit2b := by
  unfold Prim
  simp [orbit2b];
  rfl

def orbit5a : Tree := .node [leaf, .node [leaf, leaf], leaf]
def orbit5b : Tree := .node [.node [.node [leaf], .node [leaf]]]

@[simp] theorem m_orbit5a : m orbit5a = orbit5b := by native_decide
@[simp] theorem m_orbit5b : m orbit5b = orbit5a := by native_decide
theorem PrimFixedM2_orbit5a : PrimFixedM2 orbit5a := ⟨by unfold Prim; native_decide, by unfold FixedM2; native_decide⟩
theorem PrimFixedM2_orbit5b : PrimFixedM2 orbit5b := ⟨by unfold Prim; native_decide, by unfold FixedM2; native_decide⟩

def orbit14a : Tree :=
  .node [leaf,
    .node [.node [leaf, leaf],
           .node [leaf, .node [leaf], leaf],
           .node [leaf, leaf]],
    leaf]

def orbit14b : Tree :=
  .node [.node [.node [leaf],
                .node [.node [leaf, .node [leaf]],
                       .node [.node [leaf], leaf]],
                .node [leaf]]]

@[simp] theorem m_orbit14a : m orbit14a = orbit14b := by native_decide
@[simp] theorem m_orbit14b : m orbit14b = orbit14a := by native_decide
theorem PrimFixedM2_orbit14a : PrimFixedM2 orbit14a := ⟨by unfold Prim; native_decide, by unfold FixedM2; native_decide⟩
theorem PrimFixedM2_orbit14b : PrimFixedM2 orbit14b := ⟨by unfold Prim; native_decide, by unfold FixedM2; native_decide⟩

theorem rList_init_last (init : List Tree) (last : Tree) :
    rList (init ++ [last]) = r last :: rList init := by
  simp [rList]

theorem nodeCount_first_formula (init : List Tree) :
    nodeCount (.node (tList (rList init))) = 1 + forestSize init := by
  rw [nodeCount_unfold, forestSize_tList, forestSize_rList]

theorem tList_rList_ge2_of_last_nonleaf {init : List Tree}
    {d : Tree} {ds : List Tree} :
    ∃ q1 q2 qrest, tList (rList (init ++ [.node (d :: ds)])) = q1 :: q2 :: qrest := by
  simp_all +decide ;
  rw [ show tList ( node ( rList ( d :: ds ) ) :: rList init ) = node ( tList ( rList init ) ) :: tList ( rList ( d :: ds ) ) from ?_ ];
  · have h_tList_nonempty : tList (rList (d :: ds)) ≠ [] := by
      have h_tList_nonempty : ∀ {ts : List Tree}, ts ≠ [] → tList ts ≠ [] := by
        intros ts hts_nonempty
        induction' ts with t ts ih;
        · contradiction;
        · cases t ; simp_all +decide [ tList ];
      induction ds <;> simp_all +decide [ rList ];
    cases h : tList ( rList ( d :: ds ) ) <;> aesop;
  · rw [Tree.tList]

theorem first_of_tList_rList {init : List Tree} {tn : Tree} {cs_tn : List Tree}
    (htn : tn = .node cs_tn) :
    (tList (rList (init ++ [tn]))).head
      (by rw [rList_init_last, htn]; cases cs_tn <;> simp [tList]) =
    .node (tList (rList init)) := by
  all_goals norm_num;
  all_goals subst htn;
  all_goals simp +decide;
  all_goals cases cs_tn <;> simp +decide [ tList ]

theorem nodeCount_last_le_forestSize_sub_first
    {a b : Tree} {rest : List Tree} :
    nodeCount ((a :: b :: rest).getLast (by simp)) ≤
      forestSize (a :: b :: rest) - nodeCount a := by
  induction' rest with d rest ih <;> simp_all +decide [ List.getLast ];
  grind +qlia

theorem not_fixedM2_nonleaf_first {c : Tree} {cs : List Tree}
    {b : Tree} {rest : List Tree} :
    ¬FixedM2 (.node (.node (c :: cs) :: b :: rest)) := by
  set ts : List Tree := .node (c :: cs) :: b :: rest;
  set Q : List Tree := tList (rList ts);
  intro h_fixedM2
  have hQ : tList (rList Q) = ts := by
    injection h_fixedM2;
  by_cases h_last_leaf : ts.getLast (by
  grind) = leaf
  generalize_proofs at *
  all_goals generalize_proofs at *;
  · obtain ⟨T, hT⟩ : ∃ T, Q = [T] := by
      have h_rList_leaf : rList ts = leaf :: rList (ts.dropLast) := by
        convert rList_init_last ( ts.dropLast ) leaf using 1;
        rw [ ← h_last_leaf, List.dropLast_append_getLast ];
      simp +zetaDelta at *;
      rw [ h_rList_leaf, tList ] ; aesop;
    simp +zetaDelta at *;
    cases T ; simp_all +decide [ Tree.tList ];
  · obtain ⟨q1, q2, qrest, hQ_ge2⟩ : ∃ q1 q2 qrest, Q = q1 :: q2 :: qrest := by
      have hQ_ge2 : ∃ q1 q2 qrest, Q = q1 :: q2 :: qrest := by
        have h_last_nonleaf : ∃ d ds, ts.getLast (by
        assumption) = .node (d :: ds) := by
          rcases h : ts.getLast ‹_› with ( _ | ⟨ d, ds ⟩ ) <;> aesop
        obtain ⟨ d, ds, h ⟩ := h_last_nonleaf;
        have hQ_ge2 : ∃ q1 q2 qrest, tList (rList (ts.dropLast ++ [node (d :: ds)])) = q1 :: q2 :: qrest := by
          exact?
        generalize_proofs at *;
        convert hQ_ge2 using 1;
        rw [ ← h, List.dropLast_append_getLast ]
      generalize_proofs at *;
      exact hQ_ge2;
    have h_nodeCount_q1 : nodeCount q1 = 1 + forestSize (ts.dropLast) := by
      have h_nodeCount_q1 : q1 = .node (tList (rList (ts.dropLast))) := by
        convert first_of_tList_rList _;
        rotate_left;
        exact ts.getLast ‹_›
        all_goals generalize_proofs at *;
        exact ts.getLast ‹_› |> fun x => x.children
        all_goals generalize_proofs at *;
        · cases h : ts.getLast ‹_› ; aesop;
        · grind +suggestions
      generalize_proofs at *;
      rw [ h_nodeCount_q1, nodeCount_unfold ];
      rw [ forestSize_m_children ]
    have h_nodeCount_first_ts : nodeCount (.node (c :: cs)) = 1 + forestSize (Q.dropLast) := by
      have h_nodeCount_first_ts : nodeCount (.node (c :: cs)) = nodeCount (.node (tList (rList (Q.dropLast)))) := by
        have h_nodeCount_first_ts : tList (rList Q) = .node (c :: cs) :: b :: rest := by
          exact hQ
        generalize_proofs at *;
        have h_nodeCount_first_ts : (tList (rList Q)).head (by
        exact h_nodeCount_first_ts.symm ▸ by simp +decide ;) = .node (tList (rList (Q.dropLast))) := by
          convert first_of_tList_rList _;
          rotate_left;
          exact Q.getLast ( by simp +decide [ hQ_ge2 ] );
          exact ( Q.getLast ( by simp +decide [ hQ_ge2 ] ) ).children;
          · cases h : Q.getLast ( by simp +decide [ hQ_ge2 ] ) ; aesop;
          · rw [ List.dropLast_append_getLast ]
        generalize_proofs at *;
        grind +qlia
      generalize_proofs at *;
      rw [h_nodeCount_first_ts];
      exact?
    have h_nodeCount_last_Q : nodeCount (Q.getLast (by
    grind)) ≤ forestSize Q - nodeCount q1 := by
      have h_nodeCount_last_Q : nodeCount (Q.getLast (by
      grind)) ≤ forestSize Q - nodeCount q1 := by
        have := nodeCount_last_le_forestSize_sub_first (a := q1) (b := q2) (rest := qrest)
        grind
      generalize_proofs at *;
      exact h_nodeCount_last_Q
    generalize_proofs at *;
    simp_all +decide;
    simp +zetaDelta at *;
    omega

@[simp] theorem tList_cons_leaf (ts : List Tree) :
    tList (leaf :: ts) = [.node (tList ts)] := by
  simp [tList, leaf]

@[simp] theorem tList_singleton_node (cs : List Tree) :
    tList [.node cs] = leaf :: tList cs := by
  simp [tList]

theorem tList_ne_nil_of_ne_nil {ts : List Tree} (h : ts ≠ []) : tList ts ≠ [] := by
  induction' ts with t ts ih
  · contradiction
  · cases t; simp_all +decide [tList]

theorem tList_cons_length (cs : List Tree) (ts : List Tree) :
    (tList (.node cs :: ts)).length = 1 + (tList cs).length := by
  simp [tList]; omega

theorem tList_singleton_iff (ts : List Tree) (hne : ts ≠ []) :
    (∃ x, tList ts = [x]) ↔ ∃ rest, ts = leaf :: rest := by
  constructor
  · intro ⟨x, hx⟩
    match ts, hne with
    | .node cs :: rest, _ =>
      cases cs with
      | nil => exact ⟨rest, rfl⟩
      | cons c cs' =>
        have h1 := tList_cons_length (c :: cs') rest
        rw [hx] at h1; simp at h1
        exact absurd h1 (tList_ne_nil_of_ne_nil (List.cons_ne_nil c cs'))
  · rintro ⟨rest, rfl⟩
    exact ⟨.node (tList rest), tList_cons_leaf rest⟩

theorem tList_head_leaf_iff (ts : List Tree) (hne : ts ≠ []) :
    (∃ rest, tList ts = leaf :: rest) ↔ ∃ cs, ts = [.node cs] := by
  constructor
  · rcases ts with (_ | ⟨x, _ | ⟨y, ts⟩⟩) <;> simp_all +decide
    · cases x; tauto
    · cases x; cases y; simp_all +decide [tList]
  · aesop

theorem rList_bookend (middle : List Tree) :
    rList (leaf :: middle ++ [leaf]) = leaf :: rList middle ++ [leaf] := by
  simp [rList, rList_append]

theorem rList_ne_nil {ts : List Tree} (hne : ts ≠ []) : rList ts ≠ [] := by
  rcases ts with (_ | ⟨t, _ | ⟨m, ts⟩⟩) <;> simp_all +decide [rList]

theorem rList_starts_leaf_iff {ts : List Tree} (hne : ts ≠ []) :
    (∃ rest, rList ts = leaf :: rest) ↔ ∃ middle, ts = middle ++ [leaf] := by
  constructor
  · induction' ts using List.reverseRecOn with ts t ih
    · contradiction
    · cases eq_or_ne ts [] <;> simp_all +decide [rList_append]
  · rintro ⟨middle, rfl⟩; exact ⟨rList middle, by simp +decide [rList_append]⟩

def leftSpine : List Tree → Nat
  | [] => 0
  | .node cs :: _ => 1 + leftSpine cs

theorem tList_length_eq_leftSpine : ∀ (ts : List Tree),
    (tList ts).length = leftSpine ts := by
  intro cs;
  induction' cs using Primitive.Tree.tList.induct with cs ih;
  · native_decide +revert;
  · rw [ tList_cons_length, leftSpine ];
    grind

@[simp] theorem leftSpine_leaf_cons (ts : List Tree) : leftSpine (leaf :: ts) = 1 := by
  simp [leftSpine, leaf]

theorem rList_starts_leaf_of_ends_leaf {ts : List Tree} (hne : ts ≠ [])
    (hlast : ts.getLast hne = leaf) :
    ∃ rest, rList ts = leaf :: rest := by
  convert rList_starts_leaf_iff hne |>.2 _;
  use ts.dropLast;
  rw [ ← hlast, List.dropLast_append_getLast ]

theorem tList_rList_singleton_of_last_leaf {ts : List Tree} (hne : ts ≠ [])
    (hlast : ts.getLast hne = leaf) :
    ∃ x, tList (rList ts) = [x] := by
  obtain ⟨ rest, hrest ⟩ := rList_starts_leaf_of_ends_leaf hne hlast;
  exact ⟨ _, by rw [ hrest, tList_cons_leaf ] ⟩

theorem tList_rList_singleton_starts_leaf (T : Tree) :
    ∃ rest, tList (rList [T]) = leaf :: rest := by
  cases T;
  cases ‹List Tree› <;> simp_all +decide [ rList ]

theorem m_chain_singleton_gives_leaf {ts : List Tree}
    (hT : ∃ T, tList (rList ts) = [T]) :
    ∃ rest, tList (rList (tList (rList ts))) = leaf :: rest := by
  obtain ⟨T, hT⟩ := hT;
  rw [hT];
  apply tList_rList_singleton_starts_leaf

theorem not_fixedM2_nonleaf_first_leaf_last {c : Tree} {cs : List Tree}
    {rest : List Tree} (_hrest : rest ≠ [])
    (hlast : ((.node (c :: cs) :: rest)).getLast (by simp) = leaf) :
    ¬FixedM2 (.node (.node (c :: cs) :: rest)) := by
  unfold FixedM2;
  have h_m2_start_leaf : ∃ rest', tList (rList (tList (rList (node (c :: cs) :: rest)))) = leaf :: rest' := by
    apply m_chain_singleton_gives_leaf;
    apply tList_rList_singleton_of_last_leaf;
    exact hlast;
  cases h_m2_start_leaf ; simp_all +decide [ Primitive.Tree.m ]

theorem fixedM2_nontrivial_dichotomy (x : Tree)
    (hfix : FixedM2 x) (hprim : Prim x)
    (hne_leaf : x ≠ leaf) (hne_single : x ≠ .node [leaf]) :
    (∃ rest, rest ≠ [] ∧ x.children = leaf :: rest) ∨
    (∃ cs, cs ≠ [] ∧ x.children = [.node cs]) := by
  obtain ⟨ts, rfl⟩ : ∃ ts, x = .node ts := ⟨x.children, by cases x; rfl⟩
  simp at *
  match ts, hne_leaf with
  | [], h => exact absurd rfl h
  | [child], _ =>
    right
    cases child with
    | node cs =>
      cases cs with
      | nil => exact absurd rfl hne_single
      | cons c cs => exact ⟨c :: cs, List.cons_ne_nil c cs, rfl⟩
  | first :: second :: rest, _ =>
    cases first with
    | node cs =>
      cases cs with
      | nil => left; exact ⟨second :: rest, List.cons_ne_nil second rest, rfl⟩
      | cons c cs => exact absurd hfix (not_fixedM2_nonleaf_first)

theorem FixedM2_m {x : Tree} (h : FixedM2 x) : FixedM2 (m x) := by
  simp only [FixedM2] at *; congr 1

theorem PrimFixedM2_m {x : Tree} (h : PrimFixedM2 x) : PrimFixedM2 (m x) :=
  ⟨Prim_m x h.1, FixedM2_m h.2⟩

theorem rList_nonleaf_last_gives_nonleaf_first {ts : List Tree}
    (hne : ts ≠ [])
    (hlast : ∃ c cs, ts.getLast hne = .node (c :: cs)) :
    ∃ c cs rest, rList ts = .node (c :: cs) :: rest := by
  induction' ts using List.reverseRecOn with ts ih;
  · contradiction;
  · obtain ⟨c, cs, hlast⟩ : ∃ c cs, ih = .node (c :: cs) := by grind;
    simp_all +decide [ rList_append ];
    exact List.exists_cons_of_ne_nil ( rList_ne_nil ( by aesop ) )

theorem tList_nonleaf_first_structure {c : Tree} {cs : List Tree}
    {rest : List Tree} (hrest : rest ≠ []) :
    ∃ d ds tail, tList (.node (c :: cs) :: rest) = .node (d :: ds) :: tail ∧ tail ≠ [] := by
  have htList_rest_nonempty : tList rest ≠ [] := by exact?;
  obtain ⟨d, ds, hd⟩ : ∃ d ds, tList rest = d :: ds := by
    exact List.exists_cons_of_ne_nil htList_rest_nonempty;
  cases c ; cases cs <;> simp_all +decide [ tList ]

theorem m_leaf_start_nonleaf_end {rest : List Tree}
    (hne : rest ≠ [])
    (hlast : ∃ c cs, rest.getLast hne = .node (c :: cs)) :
    ∃ c cs b tail, m (.node (leaf :: rest)) = .node (.node (c :: cs) :: b :: tail) := by
  have htList : ∃ d ds tail, tList (rList rest ++ [leaf]) = .node (d :: ds) :: tail ∧ tail ≠ [] := by
    have hrList_nonleaf_first : ∃ c cs rest', rList rest = .node (c :: cs) :: rest' := by exact?;
    obtain ⟨ c, cs, rest', hrList_nonleaf_first ⟩ := hrList_nonleaf_first; simp_all +decide ;
    exact tList_nonleaf_first_structure ( by aesop );
  rcases htList with ⟨ d, ds, tail, h₁, h₂ ⟩ ; rcases tail with ( _ | ⟨ b, tail ⟩ ) <;> aesop;

theorem fixedM2_bookend_last_leaf {rest : List Tree}
    (hne : rest ≠ [])
    (hfix : FixedM2 (.node (leaf :: rest))) :
    rest.getLast hne = leaf := by
  by_contra h_last_nonleaf
  obtain ⟨c', cs', b, tail, hm⟩ := m_leaf_start_nonleaf_end hne
    (by rcases h : rest.getLast hne with ⟨_ | ⟨_, _⟩⟩ <;> aesop)
  exact not_fixedM2_nonleaf_first (hm ▸ FixedM2_m hfix)

theorem fixedM2_bookend_form {rest : List Tree}
    (hne : rest ≠ [])
    (hfix : FixedM2 (.node (leaf :: rest))) :
    ∃ middle, rest = middle ++ [leaf] :=
  ⟨rest.dropLast, by rw [← fixedM2_bookend_last_leaf hne hfix, List.dropLast_append_getLast]⟩

theorem prim_bookend_middle_nonleaf {middle : List Tree}
    (hp : Prim (.node (leaf :: middle ++ [leaf])))
    (m : Tree) (hm : m ∈ middle) :
    m ≠ leaf := by
  intro h;
  have h_squeeze : squeezeMid (middle ++ [leaf]) ≠ middle ++ [leaf] := by
    rw [ squeezeMid_append_singleton ];
    simp_all +decide [ Tree.isNonLeaf ];
    exact ⟨ _, hm, rfl ⟩;
  simp_all +decide [ Prim ];
  unfold squeezeOuter at hp;
  norm_num +zetaDelta at *;
  contrapose! h_squeeze;
  rw [ ← hp.2, primChildrenRaw_append ];
  rw [ squeezeMid_idem ]

theorem fixedM2_bookend_commutation {middle : List Tree}
    (hfix : FixedM2 (.node (leaf :: middle ++ [leaf]))) :
    tList (rList middle ++ [leaf]) = rList (tList (middle ++ [leaf])) := by
  have hQ : tList (rList (tList (rList middle ++ [leaf]))) = middle ++ [leaf] := by
    unfold Tree.FixedM2 at hfix;
    simp_all +decide [ Tree.r, Tree.rList ];
  have h_inv : rList (tList (rList middle ++ [leaf])) = tList (middle ++ [leaf]) := by
    rw [ ← hQ, tList_involutive ];
  rw [ ← h_inv, rList_involutive ]

theorem nodeCount_head_tList {a : Tree} {rest : List Tree} :
    nodeCount ((tList (a :: rest)).head (tList_ne_nil_of_ne_nil (List.cons_ne_nil a rest))) =
    1 + forestSize rest := by
  cases a ; simp_all +decide [ tList ];
  rw [nodeCount_unfold];
  rw [ forestSize_tList ]

theorem nodeCount_head_rList {ts : List Tree} (hne : ts ≠ []) :
    nodeCount ((rList ts).head (rList_ne_nil hne)) = nodeCount (ts.getLast hne) := by
  induction' ts using List.reverseRecOn with ts ih
  all_goals generalize_proofs at *;
  · contradiction;
  · cases ts <;> simp_all +decide [ rList ];
    · exact?;
    · exact?

theorem nodeCount_head_le_forestSize {a : Tree} {rest : List Tree} :
    nodeCount a ≤ forestSize (a :: rest) := by
  unfold forestSize; omega

theorem nodeCount_head_tList_rList_ge {m₁ m₂ : Tree} {ms : List Tree} :
    nodeCount ((tList (rList (m₁ :: m₂ :: ms) ++ [leaf])).head
      (tList_ne_nil_of_ne_nil (by simp [rList]))) ≥ 2 + nodeCount m₁ := by
  have h_tList : tList (rList (m₁ :: m₂ :: ms) ++ [leaf]) = tList (rList (m₂ :: ms) ++ [r m₁] ++ [leaf]) := by
    exact?;
  cases h : rList ( m₂ :: ms ) <;> simp_all +decide;
  · cases ms <;> simp_all +decide [ rList ];
  · rw [ nodeCount_head_tList ] ; simp +arith +decide [ * ];
    rw [ forestSize_append ] ; simp +arith +decide [ * ];
    rw [ nodeCount_r ] ; simp +arith +decide [ * ]

theorem nodeCount_head_rList_tList_le {m₁ m₂ : Tree} {ms : List Tree}
    (hm₁ : m₁ ≠ leaf) :
    nodeCount ((rList (tList ((m₁ :: m₂ :: ms) ++ [leaf]))).head
      (rList_ne_nil (tList_ne_nil_of_ne_nil (by simp)))) ≤ nodeCount m₁ - 1 := by
  obtain ⟨c, cs, hc⟩ : ∃ c cs, m₁ = .node (c :: cs) := by
    rcases m₁ with ( _ | ⟨ _ | cs ⟩ ) <;> tauto;
  rw [ hc ];
  convert nodeCount_getLast_le_forestSize _ using 1;
  rotate_left;
  rotate_left;
  exact tList ( c :: cs );
  exact tList_ne_nil_of_ne_nil ( by simp +decide );
  · rw [ nodeCount_head_rList ];
    all_goals norm_num [ tList ];
    grind +splitIndPred;
    grind;
  · rw [ nodeCount_unfold, forestSize_tList ];
    grind

theorem fixedM2_bookend_no_ge2_middle {m₁ m₂ : Tree} {ms : List Tree}
    (hfix : FixedM2 (.node (leaf :: (m₁ :: m₂ :: ms) ++ [leaf])))
    (hm₁ : m₁ ≠ leaf) :
    False := by
  convert fixedM2_bookend_commutation hfix using 1;
  simp +decide [ List.cons_append ];
  intro h; have := congr_arg List.length h; simp +decide [ rList_length, tList_length_eq_leftSpine ] at this;
  convert nodeCount_head_tList_rList_ge using 1;
  rotate_left;
  exact m₁;
  exact m₂;
  exact ms;
  simp +decide [ h ];
  exact lt_of_le_of_lt ( nodeCount_head_rList_tList_le hm₁ ) ( by omega )

theorem nodeCount_primInner_le : ∀ t : Tree, nodeCount (primInner t) ≤ nodeCount t := by
  intro t;
  by_contra h_contra;
  obtain ⟨t, ht⟩ : ∃ t : Tree, t.primInner.nodeCount > t.nodeCount ∧ ∀ t' : Tree, t'.nodeCount < t.nodeCount → t'.primInner.nodeCount ≤ t'.nodeCount := by
    have h_well_founded : WellFounded (fun t t' : ℕ => t < t') := by
      exact wellFounded_lt;
    have := h_well_founded.has_min { n | ∃ t : Tree, t.nodeCount = n ∧ t.primInner.nodeCount > t.nodeCount } ⟨ _, ⟨ t, rfl, lt_of_not_ge h_contra ⟩ ⟩;
    obtain ⟨ a, ⟨ t, rfl, ht ⟩, ha ⟩ := this; exact ⟨ t, ht, fun t' ht' => not_lt.1 fun contra => ha _ ⟨ t', rfl, contra ⟩ ht' ⟩ ;
  rcases t with ⟨ ts ⟩;
  have h_forestSize_primChildrenRaw : forestSize (primChildrenRaw ts) ≤ forestSize ts := by
    have h_forestSize_primChildrenRaw : ∀ ts : List Tree, (∀ t' ∈ ts, t'.primInner.nodeCount ≤ t'.nodeCount) → forestSize (primChildrenRaw ts) ≤ forestSize ts := by
      intros ts hts; induction' ts with t ts ih <;> simp_all +decide;
      exact add_le_add hts.1 ih;
    apply h_forestSize_primChildrenRaw;
    intro t' ht'
    have h_nodeCount_lt : t'.nodeCount < (node ts).nodeCount := by
      have h_nodeCount_lt : ∀ {ts : List Tree}, t' ∈ ts → t'.nodeCount ≤ forestSize ts := by
        intros ts ht'; induction' ts with t ts ih <;> simp_all +decide [ forestSize ] ;
        grind;
      exact lt_of_le_of_lt ( h_nodeCount_lt ht' ) ( by linarith! [ nodeCount_unfold ts ] );
    exact ht.2 t' h_nodeCount_lt;
  have h_forestSize_squeezeOuter : forestSize (squeezeOuter (primChildrenRaw ts)) ≤ forestSize (primChildrenRaw ts) := by
    have h_forestSize_squeezeMid : ∀ (ts : List Tree), forestSize (squeezeMid ts) ≤ forestSize ts := by
      intro ts;
      induction' n : forestSize ts using Nat.strong_induction_on with n ih generalizing ts;
      rcases ts with ( _ | ⟨ t, _ | ⟨ m, ts ⟩ ⟩ ) <;> simp_all +decide;
      · aesop;
      · by_cases ht : t = .node [] <;> simp_all +decide [ squeezeMid ];
        have h_ind : forestSize (squeezeMid (m :: ts)) ≤ forestSize (m :: ts) := by
          apply ih (forestSize (m :: ts)) (by
          simp +arith +decide [ ← n ]) (m :: ts) rfl;
        exact h_ind.trans ( by simp +arith +decide [ ← n ] )
        · linarith [ ih ( m.nodeCount + forestSize ts ) ( by linarith [ nodeCount_pos t ] ) ( m :: ts ) rfl ];
    cases h : primChildrenRaw ts <;> simp_all +decide [ squeezeOuter ];
  have h_forestSize_contractRoot : forestSize (contractRoot (squeezeOuter (primChildrenRaw ts))) ≤ forestSize (squeezeOuter (primChildrenRaw ts)) := by
    rcases h : squeezeOuter ( primChildrenRaw ts ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ contractRoot ];
    rcases a with ( _ | ⟨ c, cs ⟩ ) <;> simp_all +decide [ forestSize ];
    simp +decide [ nodeCount_unfold ];
  unfold Tree.primInner at ht; simp_all +decide [ nodeCount_unfold ] ;
  linarith

theorem no_primInner_wrap (t : Tree) : primInner t ≠ .node [t] := by
  intro h
  have h1 := nodeCount_primInner_le t
  rw [h] at h1
  have h2 := nodeCount_pos t
  rw [nodeCount_unfold] at h1
  simp only [forestSize] at h1
  omega

theorem Prim_of_primInner_fixed {t : Tree} (h : primInner t = t) (hne : t ≠ leaf) : Prim t := by
  obtain ⟨ts, rfl⟩ : ∃ ts : List Tree, t = .node ts := by
    cases t ; tauto;
  rcases x : squeezeOuter ( primChildrenRaw ts ) with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ contractRoot ];
  rcases a with ( _ | ⟨ c, cs ⟩ ) <;> simp_all +decide [ squeezeOuter ];
  rcases ts with ( _ | ⟨ t, _ | ⟨ m, ts ⟩ ⟩ ) <;> simp_all +decide;
  · exact absurd x ( by exact? );
  · exact absurd x.2 ( by exact? )

theorem Prim_core_of_Prim_bookend {core : Tree}
    (hp : Prim (.node [leaf, core, leaf]))
    (hne : core ≠ leaf) :
    Prim core := by
  obtain ⟨c, cs, hc⟩ : ∃ c cs, core = .node (c :: cs) := by
    rcases core with ( _ | ⟨ cs ⟩ ) <;> tauto;
  obtain ⟨b, bs, hb⟩ : ∃ b bs, primInner core = .node (b :: bs) := by
    have := primInner_node_cons_exists_cons c cs; aesop;
  have h_eq : prim (.node [leaf, core, leaf]) = .node [leaf, primInner core, leaf] := by
    unfold prim;
    unfold primList; simp +decide [ hb ] ;
    rfl;
  apply Prim_of_primInner_fixed;
  · aesop;
  · assumption

theorem prim_fixedM2_bookend_singleton_middle {middle : List Tree}
    (hp : PrimFixedM2 (.node (leaf :: middle ++ [leaf])))
    (hne : middle ≠ []) :
    ∃ core, middle = [core] ∧ core ≠ leaf ∧ Prim core := by
  rcases middle with ( _ | ⟨ m, _ | ⟨ m₂, ms ⟩ ⟩ ) <;> simp_all +decide;
  · constructor;
    · exact fun h => by have := hp.1; simp_all +decide [ Tree.PrimFixedM2 ] ;
    · exact Prim_core_of_Prim_bookend hp.1 ( by
        intro h; have := hp.1; simp_all +decide [ Tree.Prim ] ; );
  · exact absurd ( fixedM2_bookend_no_ge2_middle hp.2 ( by
      apply prim_bookend_middle_nonleaf;
      convert hp.1 using 1;
      rotate_right;
      exacts [ m :: m₂ :: ms, by simp +decide, by simp +decide ] ) ) ( by tauto )

theorem prim_fixedM2_refined_trichotomy (x : Tree)
    (hpm : PrimFixedM2 x)
    (hne_leaf : x ≠ leaf) (hne_single : x ≠ .node [leaf]) :
    (x.children = [leaf, leaf]) ∨
    (∃ core, core ≠ leaf ∧ Prim core ∧ x.children = [leaf, core, leaf]) ∨
    (∃ cs, cs ≠ [] ∧ x.children = [.node cs]) := by
  obtain ⟨rest, hrest⟩ | ⟨cs, hcs⟩ := fixedM2_nontrivial_dichotomy x hpm.2 hpm.1 hne_leaf hne_single;
  · obtain ⟨middle, hmiddle⟩ : ∃ middle, rest = middle ++ [leaf] := by
      apply fixedM2_bookend_form hrest.left;
      convert hpm.2 using 1;
      cases x ; aesop;
    by_cases hmiddle_empty : middle = [];
    · aesop;
    · have := prim_fixedM2_bookend_singleton_middle ( show PrimFixedM2 ( .node ( leaf :: middle ++ [ leaf ] ) ) from ?_ ) hmiddle_empty; aesop;
      cases x ; aesop;
  · exact Or.inr <| Or.inr <| ⟨ cs, hcs ⟩

theorem H_leaf_cons (X : List Tree) :
    tList (rList (tList (leaf :: X))) = leaf :: tList (rList (tList X)) := by
  simp only [tList_cons_leaf, rList_singleton, r_node, tList_singleton_node]

@[simp] theorem tList_cons_leaf' (X : List Tree) :
    tList (leaf :: X) = [.node (tList X)] := by
  simp [leaf]

@[simp] theorem rList_cons (t : Tree) (ts : List Tree) :
    rList (t :: ts) = rList ts ++ [r t] := by
  simp [rList]

theorem rList_head_eq_r_last (ts : List Tree) (hne : ts ≠ []) :
    (rList ts).head (rList_ne_nil hne) = r (ts.getLast hne) := by
  rcases ts with ( _ | ⟨ _ | ts ⟩ ) <;> simp_all +decide [ rList ];
  · contradiction;
  · induction ‹List Tree› using List.reverseRecOn <;> simp_all +decide [ rList ];
  · rename_i k hk;
    induction k using List.reverseRecOn <;> simp_all +decide [ rList ]

theorem getLast_eq_leaf_of_rList_head_eq_leaf {B : List Tree} (hBne : B ≠ [])
    (hhead : (rList B).head (rList_ne_nil hBne) = leaf) :
    B.getLast hBne = leaf := by
  have h_last : r (B.getLast hBne) = leaf := by
    rw [ ← hhead, rList_head_eq_r_last ]
  generalize_proofs at *;
  apply r_injective; exact h_last

theorem rList_append_leaf (C : List Tree) :
    rList (C ++ [leaf]) = leaf :: rList C := by
  simp [rList_append, rList]

theorem forestSize_dropLast_lt {B : List Tree} (hBne : B ≠ []) :
    forestSize B.dropLast < forestSize B := by
  induction B using List.reverseRecOn <;> simp_all +decide;
  have h_forestSize_append : ∀ (l : List Tree) (a : Tree), forestSize (l ++ [a]) = forestSize l + nodeCount a := by
    intros l a; induction l <;> simp_all +decide [ forestSize ] ;
    ring;
  exact h_forestSize_append _ _ ▸ Nat.lt_add_of_pos_right ( nodeCount_pos _ )

theorem rList_leaf_sandwich {C : List Tree} (hC : rList C = C) :
    rList (leaf :: C ++ [leaf]) = leaf :: C ++ [leaf] := by
  rw [ show rList ( leaf :: C ++ [ leaf ] ) = rList ( C ++ [ leaf ] ) ++ rList [ leaf ] from ?_ ];
  · rw [ rList_append, hC, rList_cons ] ; aesop;
  · norm_num +zetaDelta at *

theorem padding_lemma_leaf_case (B P : List Tree) (n : ℕ)
    (ih_n : ∀ F' P' : List Tree, forestSize F' ≤ n →
      tList (rList (tList (F' ++ P'))) = rList F' ++ P' → rList F' = F')
    (hle : forestSize (leaf :: B) ≤ n + 1)
    (h : tList (rList (tList (leaf :: B ++ P))) = rList (leaf :: B) ++ P) :
    rList (leaf :: B) = leaf :: B := by
  by_cases hB : B = [] <;> simp_all +decide;
  have h_first : (rList B).head (rList_ne_nil hB) = leaf := by
    have h_eq : leaf :: tList (rList (tList (B ++ P))) = rList B ++ node [] :: P := h
    have h_first : (rList B).head (rList_ne_nil hB) = leaf := by
      have h_eq : leaf :: tList (rList (tList (B ++ P))) = rList B ++ node [] :: P := h_eq
      have h_first : (rList B).head (rList_ne_nil hB) = (leaf :: tList (rList (tList (B ++ P)))).head (by simp) := by
        grind
      exact h_first.trans ( by rfl );
    exact h_first;
  have h_last : B.getLast hB = leaf := by exact?;
  obtain ⟨C, hC⟩ : ∃ C, B = C ++ [leaf] := by
    exact ⟨ B.dropLast, by rw [ ← h_last, List.dropLast_append_getLast hB ] ⟩;
  simp_all +decide;
  apply ih_n C (leaf :: P);
  · simp_all +decide [ add_comm, forestSize_append ]; linarith;
  · convert h using 1

theorem aux_cancel (Q : Tree) (G : List Tree) (n : ℕ)
    (ih_n : ∀ F' P' : List Tree, forestSize F' ≤ n →
      tList (rList (tList (F' ++ P'))) = rList F' ++ P' → rList F' = F')
    (hGsize : forestSize G ≤ n)
    (h : rList G ++ [r Q] = Q :: tList (rList (tList G))) :
    tList (rList (tList G)) = G := by
  by_cases hG : G = [] <;> simp_all +decide [ List.append_eq_cons_iff ];
  obtain ⟨E, hE⟩ : ∃ E, G = E ++ [r Q] := by
    have h_last : G.getLast hG = r Q := by
      cases' h with h_empty h_nonempty;
      · exact absurd h_empty.1 ( rList_ne_nil hG );
      · have := rList_head_eq_r_last G hG; aesop;
    exact ⟨ G.dropLast, by rw [ ← h_last, List.dropLast_append_getLast hG ] ⟩;
  contrapose! ih_n;
  cases h <;> simp_all +decide [ rList_append ];
  refine' ⟨ E, _, _, ih_n ⟩;
  · exact le_trans ( by simp +decide [ forestSize_append ] ) hGsize;
  · use [Q.r]

theorem padding_lemma_single_root_case (c : Tree) (cs P : List Tree) (n : ℕ)
    (ih_n : ∀ F' P' : List Tree, forestSize F' ≤ n →
      tList (rList (tList (F' ++ P'))) = rList F' ++ P' → rList F' = F')
    (hle : forestSize [.node (c :: cs)] ≤ n + 1)
    (h : tList (rList (tList ([.node (c :: cs)] ++ P))) = rList [.node (c :: cs)] ++ P) :
    rList [.node (c :: cs)] = [.node (c :: cs)] := by
  revert h;
  intros h
  set A : List Tree := c :: cs
  set G : List Tree := tList A
  set Q : Tree := .node (tList P)
  set hGsize : forestSize G ≤ n := by
    have h_nodeCount : nodeCount (node A) = 1 + forestSize A := by
      rw [Tree.nodeCount_unfold];
    rw [ show forestSize [ node A ] = nodeCount ( node A ) from ?_ ] at hle ; linarith! [ nodeCount_pos ( node A ), forestSize_tList A ];
    rfl
  set h_eq : rList G ++ [r Q] = Q :: tList (rList (tList G)) := by
    apply_fun tList at h; simp_all +decide [ tList_involutive ] ;
    convert h using 1 <;> simp +decide [ tList ];
    · exact ⟨ rfl, rfl ⟩;
    · aesop;
  have h_aux_cancel : tList (rList (tList G)) = G := by
    apply aux_cancel Q G n ih_n hGsize h_eq;
  have := t_injective ( show t ( Tree.node ( rList A ) ) = t ( Tree.node A ) from ?_ ) ; aesop;
  cases h_eq : tList ( rList ( tList G ) ) <;> aesop

theorem nodeCount_head_rList_le {a : Tree} {B : List Tree} (hB : B ≠ []) :
    nodeCount ((rList (a :: B)).head (rList_ne_nil (List.cons_ne_nil a B))) ≤
    forestSize B := by
  convert nodeCount_getLast_le_forestSize hB using 1
  rw [rList_head_eq_r_last]
  convert nodeCount_r _ using 1
  grind
  aesop

theorem nodeCount_head_tList_rList_node_cons {X : List Tree} {Y : List Tree} (hY : Y ≠ []) :
    nodeCount ((tList (rList (.node X :: Y))).head
      (tList_ne_nil_of_ne_nil (rList_ne_nil (List.cons_ne_nil (.node X) Y)))) ≥
    2 + forestSize X := by
  have h_last : nodeCount ((rList (.node X :: Y)).head (rList_ne_nil (by simp))) ≤ forestSize Y := by
    convert nodeCount_head_rList_le hY using 1
  have h_head_tList : ((tList (rList (.node X :: Y))).head (tList_ne_nil_of_ne_nil (by simp))).nodeCount = 1 + forestSize (rList (.node X :: Y)).tail := by
    convert nodeCount_head_tList using 1
    swap
    exact ( rList ( node X :: Y ) ).head ( rList_ne_nil ( by simp ) )
    grind +splitImp
  have h_forestSize_tail : forestSize (rList (.node X :: Y)).tail = forestSize (rList Y) - nodeCount ((rList (.node X :: Y)).head (rList_ne_nil (by simp))) + nodeCount (.node (rList X)) := by
    have h_tail : forestSize (rList (.node X :: Y)).tail = forestSize ((rList Y) ++ [r (.node X)]).tail := by congr
    cases h : rList Y <;> simp_all +decide [ forestSize_append ]
    · exact absurd h ( rList_ne_nil hY )
  have h_nodeCount_node : nodeCount (.node (rList X)) = 1 + forestSize (rList X) := by exact?
  have h_forestSize_rList : forestSize (rList Y) = forestSize Y ∧ forestSize (rList X) = forestSize X := by
    exact ⟨ forestSize_rList Y, forestSize_rList X ⟩
  omega

theorem padding_size_contradiction
    {c : Tree} {cs B P : List Tree} (hB : B ≠ [])
    (h : tList (rList (tList (.node (c :: cs) :: B ++ P))) =
         rList (.node (c :: cs) :: B) ++ P) :
    False := by
  have h1 : (tList (rList (tList (node (c :: cs) :: B ++ P)))).head (tList_ne_nil_of_ne_nil (by
  exact rList_ne_nil ( tList_ne_nil_of_ne_nil ( by aesop ) ))) = (rList (node (c :: cs) :: B) ++ P).head (by
  grind +suggestions) := by grobner
  generalize_proofs at *
  have h2 : nodeCount ((tList (rList (tList (node (c :: cs) :: B ++ P)))).head ‹_›) ≥ 2 + forestSize (tList (B ++ P)) := by
    convert nodeCount_head_tList_rList_node_cons _ using 1
    rotate_left; exact tList ( c :: cs )
    · exact tList_ne_nil_of_ne_nil ( by aesop )
    · simp +decide [ tList, rList ]
  have h3 : nodeCount ((rList (node (c :: cs) :: B) ++ P).head ‹_›) ≤ forestSize B := by
    have h3 : nodeCount ((rList (node (c :: cs) :: B) ++ P).head ‹_›) = nodeCount ((rList (node (c :: cs) :: B)).head (rList_ne_nil (List.cons_ne_nil (node (c :: cs)) B))) := by grind
    exact h3.symm ▸ nodeCount_head_rList_le hB
  simp_all +decide [ forestSize_tList ]
  linarith [ show forestSize ( B ++ P ) ≥ forestSize B from by rw [ forestSize_append ] ; exact Nat.le_add_right _ _ ]

theorem padding_lemma (F P : List Tree)
    (h : tList (rList (tList (F ++ P))) = rList F ++ P) :
    rList F = F := by
  suffices ∀ n, ∀ F P : List Tree, forestSize F ≤ n →
      tList (rList (tList (F ++ P))) = rList F ++ P → rList F = F from
    this (forestSize F) F P le_rfl h
  intro n; induction n with
  | zero =>
    intro F P hle h
    match F with
    | [] => simp [rList]
    | t :: ts => exfalso; simp [forestSize] at hle; linarith [nodeCount_pos t]
  | succ n ih_n =>
    intro F P hle h
    match F with
    | [] => simp [rList]
    | .node [] :: B =>
      exact padding_lemma_leaf_case B P n ih_n hle h
    | .node (c :: cs) :: [] =>
      exact padding_lemma_single_root_case c cs P n ih_n hle h
    | .node (c :: cs) :: b :: bs =>
      exact absurd (padding_size_contradiction (List.cons_ne_nil b bs) h) id

theorem rList_fixed_of_trtrt (ts : List Tree)
    (h : tList (rList (tList (rList ts))) = ts) :
    rList ts = ts := by
  have h1 : tList (rList (tList (rList ts ++ []))) = rList (rList ts) ++ [] := by
    simp [rList_involutive, h]
  have h2 := padding_lemma (rList ts) [] h1
  rw [rList_involutive] at h2; exact h2.symm

theorem r_fixed_of_m2 (x : Tree) (h : FixedM2 x) : r x = x := by
  cases x with | node ts =>
  simp only [FixedM2, m] at h
  have h' : tList (rList (tList (rList ts))) = ts := by
    have := congrArg Tree.children h; simpa using this
  exact congrArg Tree.node (rList_fixed_of_trtrt ts h')

theorem m_eq_t_of_m2 (x : Tree) (h : FixedM2 x) : m x = t x := by
  simp [m, r_fixed_of_m2 x h]

theorem r_fixed_t_of_m2 (x : Tree) (h : FixedM2 x) : r (t x) = t x := by
  have hm : FixedM2 (m x) := by simp only [FixedM2] at h ⊢; congr 1
  rw [← m_eq_t_of_m2 x h]; exact r_fixed_of_m2 (m x) hm

theorem m2_orbit_pair (x : Tree) (h : FixedM2 x) :
    m x = t x ∧ m (t x) = x := by
  exact ⟨m_eq_t_of_m2 x h, by
    rw [m, r_fixed_t_of_m2 x h, t_involutive]⟩

theorem PrimFixedM2_iff (x : Tree) :
    PrimFixedM2 x ↔ Prim x ∧ r x = x ∧ r (t x) = t x := by
  constructor
  · intro ⟨hp, hf⟩
    exact ⟨hp, r_fixed_of_m2 x hf, r_fixed_t_of_m2 x hf⟩
  · intro ⟨hp, hr, hrt⟩
    exact ⟨hp, by show t (r (t (r x))) = x; rw [hr, hrt, t_involutive]⟩

instance : DecidablePred PrimFixedM2 := fun x =>
  if h1 : prim x = x then
    if h2 : r x = x then
      if h3 : r (t x) = t x then
        .isTrue ((PrimFixedM2_iff x).mpr ⟨h1, h2, h3⟩)
      else .isFalse (fun h => h3 ((PrimFixedM2_iff x).mp h).2.2)
    else .isFalse (fun h => h2 ((PrimFixedM2_iff x).mp h).2.1)
  else .isFalse (fun h => h1 ((PrimFixedM2_iff x).mp h).1)

instance : DecidablePred Prim := fun x => inferInstanceAs (Decidable (prim x = x))
instance : DecidablePred FixedM2 := fun x => inferInstanceAs (Decidable (m (m x) = x))

end Tree
end Primitive
