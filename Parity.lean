import M3.Basic
import Mathlib

namespace LeanM3

open Forest

mutual
  def Tree.nc : Tree → Nat
    | .node f => 1 + f.nc

  def Forest.nc : Forest → Nat
    | .nil => 0
    | .cons t f => t.nc + f.nc
end

mutual
  def Tree.leafCount : Tree → Nat
    | .node .nil => 1
    | .node (.cons t f) => Forest.leafCount (.cons t f)

  def Forest.leafCount : Forest → Nat
    | .nil => 0
    | .cons t f => t.leafCount + f.leafCount
end

def Miterate (k : Nat) (f : Forest) : Forest := Nat.iterate M k f

@[simp] theorem Tree.nc_node (f : Forest) : (Tree.node f).nc = 1 + f.nc := rfl
@[simp] theorem Forest.nc_nil : Forest.nil.nc = 0 := rfl
@[simp] theorem Forest.nc_cons (t : Tree) (f : Forest) :
    (Forest.cons t f).nc = t.nc + f.nc := rfl

@[simp] theorem Tree.leafCount_nil : (Tree.node .nil).leafCount = 1 := rfl
@[simp] theorem Tree.leafCount_cons (t : Tree) (f : Forest) :
    (Tree.node (.cons t f)).leafCount = (Forest.cons t f).leafCount := rfl
@[simp] theorem Forest.leafCount_nil : Forest.nil.leafCount = 0 := rfl
@[simp] theorem Forest.leafCount_cons (t : Tree) (f : Forest) :
    (Forest.cons t f).leafCount = t.leafCount + f.leafCount := rfl

@[simp] theorem S_nc (f : Forest) : (S f).nc = 1 + f.nc := by
  simp [S]

@[simp] theorem S_leafCount_nil : (S .nil).leafCount = 1 := by
  simp [S]

@[simp] theorem S_leafCount_cons (t : Tree) (f : Forest) :
    (S (.cons t f)).leafCount = (Forest.cons t f).leafCount := by
  simp [S]

theorem S_leafCount_of_ne_nil {f : Forest} (h : f ≠ .nil) :
    (S f).leafCount = f.leafCount := by
  cases f with
  | nil => cases h rfl
  | cons t f => simp [S]

@[simp] theorem Forest.nc_append : ∀ f g : Forest, (f ++ g).nc = f.nc + g.nc
  | .nil, g => by simp
  | .cons t f, g => by simp [Forest.nc_append f g, Nat.add_assoc]

@[simp] theorem Forest.leafCount_append : ∀ f g : Forest,
    (f ++ g).leafCount = f.leafCount + g.leafCount
  | .nil, g => by simp
  | .cons t f, g => by simp [Forest.leafCount_append f g, Nat.add_assoc]

@[simp] theorem Tree.leafCount_append_singleton (f : Forest) (t : Tree) :
    (Tree.node (f ++ Forest.singleton t)).leafCount = f.leafCount + t.leafCount := by
  cases f <;>
    simp [Forest.singleton, Forest.leafCount_append, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm]

mutual
  @[simp] theorem RTree_nc : ∀ t : Tree, (RTree t).nc = t.nc
    | .node f => by simp [RTree, RForest_nc f]

  @[simp] theorem RForest_nc : ∀ f : Forest, (RForest f).nc = f.nc
    | .nil => by simp [RForest]
    | .cons t f => by
        simp [RForest, Forest.singleton, RForest_nc f, RTree_nc t,
          Nat.add_comm]
end

@[simp] theorem T_nc : ∀ f : Forest, (T f).nc = f.nc
  | .nil => by simp [T]
  | .cons (.node a) b => by
      simp [T, T_nc a, T_nc b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem M_nc (f : Forest) : (M f).nc = f.nc := by
  simp [M]

mutual
  @[simp] theorem RTree_leafCount : ∀ t : Tree, (RTree t).leafCount = t.leafCount
    | .node .nil => by rfl
    | .node (.cons t .nil) => by
        simp [RTree, RForest, Forest.singleton, RTree_leafCount t]
    | .node (.cons t (.cons m f)) => by
        rw [RTree, RForest, Tree.leafCount_append_singleton]
        rw [RForest_leafCount]
        simp [RTree_leafCount t, Nat.add_left_comm, Nat.add_comm]

  @[simp] theorem RForest_leafCount : ∀ f : Forest,
      (RForest f).leafCount = f.leafCount
    | .nil => by simp [RForest]
    | .cons t f => by
        simp [RForest, Forest.singleton, RForest_leafCount f,
          RTree_leafCount t, Nat.add_comm]
end

@[simp] theorem T_nil_iff (f : Forest) : T f = .nil ↔ f = .nil := by
  constructor
  · intro h
    exact T_injective (by rw [h]; rfl)
  · intro h
    rw [h]; rfl

@[simp] theorem M_nil_iff (f : Forest) : M f = .nil ↔ f = .nil := by
  constructor
  · intro h
    have hR : RForest f = .nil := by
      exact (T_nil_iff (RForest f)).1 h
    have hRR : RForest (RForest f) = RForest .nil := congrArg RForest hR
    calc
      f = RForest (RForest f) := (RForest_RForest f).symm
      _ = RForest .nil := hRR
      _ = .nil := rfl
  · intro h
    cases h
    rfl

theorem T_leaf_parity_nonempty : ∀ f : Forest, f ≠ .nil →
    ((T f).leafCount + f.leafCount + f.nc) % 2 = 1
  | .nil, h => by cases h rfl
  | .cons (.node a) b, _ => by
      cases hb : b with
      | nil =>
          cases ha : a with
          | nil =>
              simp [T]
          | cons a1 a2 =>
              have ih := T_leaf_parity_nonempty (.cons a1 a2) (by simp)
              let e :=
                a2.leafCount + ((T (Forest.cons a1 a2)).leafCount +
                  (a2.nc + (a1.leafCount + a1.nc)))
              have htwo : (1 + (1 + e)) % 2 = e % 2 := by
                omega
              have ihe : e % 2 = 1 := by
                simpa [e, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
              simpa [e, T, ha, hb, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using htwo.trans ihe
      | cons b1 b2 =>
          cases ha : a with
          | nil =>
              have ih := T_leaf_parity_nonempty (.cons b1 b2) (by simp)
              have hTb : T (Forest.cons b1 b2) ≠ .nil := by
                intro hT
                have : Forest.cons b1 b2 = .nil :=
                  (T_nil_iff (Forest.cons b1 b2)).1 hT
                simp at this
              let e :=
                b2.leafCount + (b2.nc +
                  (b1.leafCount + ((T (Forest.cons b1 b2)).leafCount + b1.nc)))
              have htwo : (1 + (1 + e)) % 2 = e % 2 := by
                omega
              have ihe : e % 2 = 1 := by
                simpa [e, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih
              simpa [e, T, ha, hb, S_leafCount_of_ne_nil hTb, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm] using htwo.trans ihe
          | cons a1 a2 =>
              have iha := T_leaf_parity_nonempty (.cons a1 a2) (by simp)
              have ihb := T_leaf_parity_nonempty (.cons b1 b2) (by simp)
              have hTb : T (Forest.cons b1 b2) ≠ .nil := by
                intro hT
                have : Forest.cons b1 b2 = .nil :=
                  (T_nil_iff (Forest.cons b1 b2)).1 hT
                simp at this
              have hsum :
                  (((T (Forest.cons a1 a2)).leafCount +
                    (Forest.cons a1 a2).leafCount + (Forest.cons a1 a2).nc) +
                    ((T (Forest.cons b1 b2)).leafCount +
                      (Forest.cons b1 b2).leafCount + (Forest.cons b1 b2).nc) +
                    1) % 2 = 1 := by
                omega
              simpa [T, ha, hb, S_leafCount_of_ne_nil hTb, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm] using hsum

theorem T_leaf_parity (f : Forest) :
    ((T f).leafCount + f.leafCount + f.nc) % 2 = if f = .nil then 0 else 1 := by
  by_cases h : f = .nil
  · simp [h]
  · simp [h, T_leaf_parity_nonempty f h]

theorem M_leaf_parity (f : Forest) (hne : f ≠ .nil) :
    ((M f).leafCount + f.leafCount + f.nc) % 2 = 1 := by
  have hRne : RForest f ≠ .nil := by
    intro h
    have hRR : RForest (RForest f) = RForest .nil := congrArg RForest h
    apply hne
    calc
      f = RForest (RForest f) := (RForest_RForest f).symm
      _ = RForest .nil := hRR
      _ = .nil := rfl
  simpa [M, RForest_leafCount, RForest_nc, hRne] using
    T_leaf_parity_nonempty (RForest f) hRne

theorem M_leaf_parity_flip_even (f : Forest) (hne : f ≠ .nil)
    (heven : Even f.nc) :
    (M f).leafCount % 2 = (f.leafCount + 1) % 2 := by
  have h := M_leaf_parity f hne
  rcases heven with ⟨k, hk⟩
  omega

theorem Miterate_ne_nil_of_ne_nil (k : Nat) {f : Forest} (hne : f ≠ .nil) :
    Miterate k f ≠ .nil := by
  induction k generalizing f with
  | zero =>
      simpa [Miterate] using hne
  | succ k ih =>
      have hMne : M f ≠ .nil := by
        intro hM
        exact hne ((M_nil_iff f).1 hM)
      simpa [Miterate, Function.iterate_succ_apply] using ih hMne

@[simp] theorem Miterate_nc (k : Nat) (f : Forest) : (Miterate k f).nc = f.nc := by
  induction k generalizing f with
  | zero => simp [Miterate]
  | succ k ih =>
      simpa [Miterate, Function.iterate_succ_apply] using ih (M f)

theorem Miterate_leaf_parity_even (k : Nat) (f : Forest) (hne : f ≠ .nil)
    (heven : Even f.nc) :
    (Miterate k f).leafCount % 2 = (f.leafCount + k) % 2 := by
  induction k generalizing f with
  | zero =>
      simp [Miterate]
  | succ k ih =>
      have hMne : M f ≠ .nil := by
        intro hM
        exact hne ((M_nil_iff f).1 hM)
      have hEvenM : Even (M f).nc := by
        simpa [M_nc] using heven
      have ih' := ih (M f) hMne hEvenM
      have hflip := M_leaf_parity_flip_even f hne heven
      have hstep :
          ((M f).leafCount + k) % 2 = (f.leafCount + (k + 1)) % 2 := by
        omega
      simpa [Miterate, Function.iterate_succ_apply, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih'.trans hstep

theorem not_Miterate_fixed_of_even_nc_of_odd {f : Forest} {k : Nat}
    (hne : f ≠ .nil) (heven : Even f.nc) (hk : Odd k) :
    Miterate k f ≠ f := by
  intro hfix
  have hpar := Miterate_leaf_parity_even k f hne heven
  rw [hfix] at hpar
  rcases hk with ⟨m, hm⟩
  omega

end LeanM3
