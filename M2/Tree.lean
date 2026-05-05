import Mathlib

namespace Primitive

inductive Tree where
  | node : List Tree → Tree
deriving Repr

mutual
def Tree.decEq_aux : (a b : Tree) → Decidable (a = b)
  | .node as, .node bs =>
    match Tree.listDecEq_aux as bs with
    | .isTrue h => .isTrue (congrArg Tree.node h)
    | .isFalse h => .isFalse (fun heq => h (Tree.node.inj heq))

def Tree.listDecEq_aux : (as bs : List Tree) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun h => nomatch h)
  | _ :: _, [] => .isFalse (fun h => nomatch h)
  | a :: as, b :: bs =>
    match Tree.decEq_aux a b with
    | .isFalse h => .isFalse (fun heq => h (List.cons.inj heq).1)
    | .isTrue ha =>
      match Tree.listDecEq_aux as bs with
      | .isTrue hbs => .isTrue (by rw [ha, hbs])
      | .isFalse hbs => .isFalse (fun heq => hbs (List.cons.inj heq).2)
end

instance : DecidableEq Tree := Tree.decEq_aux

instance : BEq Tree := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Tree where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

namespace Tree

def children : Tree → List Tree
  | .node ts => ts

abbrev leaf : Tree := .node []

mutual
  def rList : List Tree → List Tree
    | [] => []
    | t :: ts => rList ts ++ [r t]

  def r : Tree → Tree
    | .node ts => .node (rList ts)
end

@[simp] private theorem rList_nil : rList [] = [] := by simp [rList]

mutual
  def tList : List Tree → List Tree
    | [] => []
    | .node cs :: ts => .node (tList ts) :: tList cs

  def t : Tree → Tree
    | .node ts => .node (tList ts)
end

@[simp] private theorem tList_nil : tList [] = [] := by simp [tList]

def m (x : Tree) : Tree := t (r x)

@[simp] theorem children_node (ts : List Tree) : children (.node ts) = ts := rfl
@[simp] theorem children_leaf : children leaf = [] := rfl
@[simp] theorem r_node (ts : List Tree) : r (.node ts) = .node (rList ts) := rfl
@[simp] theorem t_node (ts : List Tree) : t (.node ts) = .node (tList ts) := rfl
@[simp] theorem r_leaf : r leaf = leaf := rfl
@[simp] theorem t_leaf : t leaf = leaf := by simp [leaf, t]
@[simp] theorem m_leaf : m leaf = leaf := by simp [m, leaf]
@[simp] theorem m_eq_t_r (x : Tree) : m x = t (r x) := rfl

@[simp] theorem rList_append (xs ys : List Tree) :
    rList (xs ++ ys) = rList ys ++ rList xs := by
  induction xs with
  | nil => simp [rList]
  | cons x xs ih => simp [rList, ih, List.append_assoc]

mutual
  @[simp] theorem r_involutive : ∀ x : Tree, r (r x) = x
    | .node ts => by simp [r, rList_involutive ts]

  @[simp] theorem rList_involutive : ∀ ts : List Tree, rList (rList ts) = ts
    | [] => rfl
    | x :: xs => by simp [rList, rList_append, r_involutive, rList_involutive]
end

mutual
  @[simp] theorem t_involutive : ∀ x : Tree, t (t x) = x
    | .node ts => by simp [t, tList_involutive ts]

  @[simp] theorem tList_involutive : ∀ ts : List Tree, tList (tList ts) = ts
    | [] => by simp
    | .node cs :: ts => by
        simp [tList, tList_involutive cs, tList_involutive ts]
end

theorem r_injective : Function.Injective r := by
  intro x y h; simpa using congrArg r h

theorem t_injective : Function.Injective t := by
  intro x y h; simpa using congrArg t h

def nodeCount : Tree → Nat
  | .node cs => 1 + cs.foldr (fun t acc => nodeCount t + acc) 0

def forestSize : List Tree → Nat
  | [] => 0
  | t :: ts => nodeCount t + forestSize ts

@[simp] theorem forestSize_nil : forestSize ([] : List Tree) = 0 := rfl
@[simp] theorem forestSize_cons (t : Tree) (ts : List Tree) :
    forestSize (t :: ts) = nodeCount t + forestSize ts := rfl

theorem nodeCount_unfold (cs : List Tree) :
    nodeCount (.node cs) = 1 + forestSize cs := by
  induction cs with
  | nil => simp [nodeCount, forestSize]
  | cons t ts ih =>
    simp [nodeCount, forestSize]
    simp [nodeCount] at ih
    omega

@[simp] theorem nodeCount_leaf_val : nodeCount leaf = 1 := by
  simp [nodeCount, leaf]

theorem nodeCount_pos (t : Tree) : 0 < nodeCount t := by
  cases t with | node cs => rw [nodeCount_unfold]; omega

theorem forestSize_nonneg (ts : List Tree) : 0 ≤ forestSize ts := Nat.zero_le _

theorem forestSize_pos_of_ne_nil {ts : List Tree} (h : ts ≠ []) : 0 < forestSize ts := by
  cases ts with
  | nil => contradiction
  | cons t ts => simp [forestSize]; have := nodeCount_pos t; omega

theorem forestSize_append (xs ys : List Tree) :
    forestSize (xs ++ ys) = forestSize xs + forestSize ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [forestSize, ih]; omega

mutual
  theorem nodeCount_r (t : Tree) : nodeCount (r t) = nodeCount t := by
    induction' t using Tree.recOn with t ih;
    exact?;
    · bound;
    · simp_all +decide [ rList, nodeCount_unfold ];
      rw [ forestSize_append, add_comm ] ; aesop

  theorem forestSize_rList (ts : List Tree) :
      forestSize (rList ts) = forestSize ts := by
    induction' ts with t ts ih;
    · rfl;
    · convert congr_arg₂ ( · + · ) ih ( show forestSize [ r t ] = forestSize [ t ] from ?_ ) using 1;
      · convert forestSize_append ( rList ts ) [ t.r ] using 1;
      · simp +arith +decide [ forestSize ];
      · have h_nodeCount_def : ∀ cs : List Tree, nodeCount (.node cs) = 1 + forestSize cs := by
          exact?;
        induction t using Tree.recOn ; simp +decide [ * ];
        exact?;
        · rfl;
        · simp_all +decide [ rList ];
          grind +suggestions
end

mutual
  theorem nodeCount_t (t : Tree) : nodeCount (Tree.t t) = nodeCount t := by
    induction t using Tree.recOn;
    exact?;
    · aesop;
    · simp_all +decide [ Tree.t ];
      rw [ nodeCount_unfold, nodeCount_unfold ];
      rename_i k hk₁ hk₂;
      rename_i t;
      cases t ; simp_all +decide [ Tree.tList ];
      rw [ ← hk₁, nodeCount_unfold ] ; ring_nf;
      rw [ nodeCount_unfold ] ; ring

  theorem forestSize_tList (ts : List Tree) :
      forestSize (tList ts) = forestSize ts := by
    induction' ts with t ts ih;
    · native_decide +revert;
    · cases t ; simp_all +decide [ tList ];
      rename_i ts';
      induction' ts' using tList.induct with t ts' ih' <;> simp_all +decide [ nodeCount_unfold ];
      simp_all +decide [ tList, add_comm, add_left_comm, add_assoc ];
      linarith [ nodeCount_unfold ( tList ts' ) ]
end

theorem forestSize_m_children (ts : List Tree) :
    forestSize (tList (rList ts)) = forestSize ts := by
  rw [forestSize_tList, forestSize_rList]

theorem nodeCount_getLast_le_forestSize {ts : List Tree} (hne : ts ≠ []) :
    nodeCount (ts.getLast hne) ≤ forestSize ts := by
  induction' ts with t ts ih;
  · contradiction;
  · cases ts <;> simp_all +decide [ List.getLast ];
    exact le_trans ih ( Nat.le_add_left _ _ )

end Tree

end Primitive
