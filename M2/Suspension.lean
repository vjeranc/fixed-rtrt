import M2.Tree

namespace Primitive
namespace Tree

mutual
  def suspendTree : Tree → Tree
    | .node ts => .node (suspendBody ts ++ [leaf])

  def suspendBody : List Tree → List Tree
    | [] => []
    | t :: ts => suspendTree t :: suspendBody ts
end

def suspendList (ts : List Tree) : List Tree :=
  suspendBody ts ++ [leaf]

mutual
  def leftSuspendTree : Tree → Tree
    | .node ts => .node (leaf :: leftSuspendBody ts)

  def leftSuspendBody : List Tree → List Tree
    | [] => []
    | t :: ts => leftSuspendTree t :: leftSuspendBody ts
end

def leftSuspendList (ts : List Tree) : List Tree :=
  leaf :: leftSuspendBody ts

def suspendIter : Nat → List Tree → List Tree
  | 0, ts => ts
  | n + 1, ts => suspendList (suspendIter n ts)

def wList (ts : List Tree) : List Tree :=
  rList (tList ts)

def wListIter (n : Nat) : List Tree → List Tree :=
  Nat.iterate wList n

@[simp] theorem suspendTree_node (ts : List Tree) :
    suspendTree (.node ts) = .node (suspendList ts) := rfl

@[simp] theorem suspendBody_nil :
    suspendBody [] = [] := rfl

@[simp] theorem suspendBody_cons (t : Tree) (ts : List Tree) :
    suspendBody (t :: ts) = suspendTree t :: suspendBody ts := rfl

@[simp] theorem suspendList_eq (ts : List Tree) :
    suspendList ts = suspendBody ts ++ [leaf] := rfl

@[simp] theorem leftSuspendTree_node (ts : List Tree) :
    leftSuspendTree (.node ts) = .node (leftSuspendList ts) := rfl

@[simp] theorem leftSuspendBody_nil :
    leftSuspendBody [] = [] := rfl

@[simp] theorem leftSuspendBody_cons (t : Tree) (ts : List Tree) :
    leftSuspendBody (t :: ts) = leftSuspendTree t :: leftSuspendBody ts := rfl

@[simp] theorem leftSuspendList_eq (ts : List Tree) :
    leftSuspendList ts = leaf :: leftSuspendBody ts := rfl

@[simp] theorem suspendIter_zero (ts : List Tree) :
    suspendIter 0 ts = ts := rfl

@[simp] theorem suspendIter_succ (n : Nat) (ts : List Tree) :
    suspendIter (n + 1) ts = suspendList (suspendIter n ts) := rfl

@[simp] theorem wList_nil :
    wList [] = [] := by
  simp [wList]

@[simp] theorem wList_cons_node (cs ts : List Tree) :
    wList (.node cs :: ts) = wList cs ++ [.node (wList ts)] := by
  simp [wList, rList, tList]

@[simp] theorem wList_cons_leaf (ts : List Tree) :
    wList (leaf :: ts) = [.node (wList ts)] := by
  simp [leaf]

@[simp] theorem suspendBody_append (xs ys : List Tree) :
    suspendBody (xs ++ ys) = suspendBody xs ++ suspendBody ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem leftSuspendBody_append (xs ys : List Tree) :
    leftSuspendBody (xs ++ ys) = leftSuspendBody xs ++ leftSuspendBody ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem suspendBody_inj : ∀ {xs ys : List Tree},
    suspendBody xs = suspendBody ys → xs = ys
  | [], [], _ => rfl
  | [], .node cs :: ys, h => by
      simp [suspendBody] at h
  | .node cs :: xs, [], h => by
      simp [suspendBody] at h
  | .node cs :: xs, .node ds :: ys, h => by
      have hhead : suspendTree (.node cs) = suspendTree (.node ds) := (List.cons.inj h).1
      have htail : suspendBody xs = suspendBody ys := (List.cons.inj h).2
      have hbody :
          suspendBody cs ++ [leaf] = suspendBody ds ++ [leaf] := Tree.node.inj hhead
      have hcs : cs = ds := suspendBody_inj (List.append_cancel_right hbody)
      have hxs : xs = ys := suspendBody_inj htail
      simp [hcs, hxs]
termination_by xs ys _ => forestSize xs + forestSize ys
decreasing_by
  all_goals simp [forestSize, nodeCount_unfold]
  all_goals omega

theorem suspendTree_injective : Function.Injective suspendTree := by
  intro x y h
  cases x with
  | node xs =>
      cases y with
      | node ys =>
          have hbody :
              suspendBody xs ++ [leaf] = suspendBody ys ++ [leaf] := Tree.node.inj h
          have hxs : xs = ys := suspendBody_inj (List.append_cancel_right hbody)
          simp [hxs]

theorem suspendBody_injective : Function.Injective suspendBody := by
  intro xs ys h
  exact suspendBody_inj h

theorem suspendList_injective : Function.Injective suspendList := by
  intro xs ys h
  exact suspendBody_inj (List.append_cancel_right h)

theorem suspendIter_injective (r : Nat) : Function.Injective (suspendIter r) := by
  induction r with
  | zero =>
      intro xs ys h
      exact h
  | succ r ih =>
      intro xs ys h
      apply ih
      exact suspendList_injective h

theorem suspendIter_eq_iff (r : Nat) {xs ys : List Tree} :
    suspendIter r xs = suspendIter r ys ↔ xs = ys := by
  constructor
  · exact fun h => suspendIter_injective r h
  · exact fun h => by rw [h]

mutual
  theorem t_suspendTree (t : Tree) :
      Tree.t (suspendTree t) = suspendTree (Tree.t t) := by
    cases t with
    | node ts =>
        simpa [Tree.t] using tList_suspendList ts

  theorem tList_suspendList (ts : List Tree) :
      tList (suspendList ts) = suspendList (tList ts) := by
    cases ts with
    | nil =>
        simp [suspendList, suspendBody, leaf, tList]
    | cons t ts =>
        cases t with
        | node cs =>
            have hcs := tList_suspendList cs
            have hts := tList_suspendList ts
            simpa [suspendList, suspendBody, tList] using And.intro hts hcs
end

theorem rList_suspendBody_left : ∀ x : List Tree,
    rList (suspendBody x) = leftSuspendBody (rList x)
  | [] => by
      simp [suspendBody, rList]
  | .node cs :: ts => by
      have hcs := rList_suspendBody_left cs
      have htail := rList_suspendBody_left ts
      simp [suspendBody, suspendTree, leftSuspendTree, Tree.r,
        rList, hcs, htail, leftSuspendBody_append, leaf]
termination_by x => forestSize x
decreasing_by
  all_goals simp [forestSize, nodeCount_unfold]
  all_goals omega

theorem r_suspendTree_left (x : Tree) :
    Tree.r (suspendTree x) = leftSuspendTree (Tree.r x) := by
  cases x with
  | node cs =>
      have hcs := rList_suspendBody_left cs
      simp [suspendTree, leftSuspendList, Tree.r, rList, hcs, leaf]

theorem rList_suspendList_left (ts : List Tree) :
    rList (suspendList ts) = leftSuspendList (rList ts) := by
  simp [suspendList, leftSuspendList, rList, rList_suspendBody_left, leaf]

theorem rList_leftSuspendBody_right : ∀ x : List Tree,
    rList (leftSuspendBody x) = suspendBody (rList x)
  | [] => by
      simp [leftSuspendBody, rList]
  | .node cs :: ts => by
      have hcs := rList_leftSuspendBody_right cs
      have htail := rList_leftSuspendBody_right ts
      simp [leftSuspendBody, suspendTree, leftSuspendTree, Tree.r,
        rList, hcs, htail, suspendBody_append, leaf]
termination_by x => forestSize x
decreasing_by
  all_goals simp [forestSize, nodeCount_unfold]
  all_goals omega

theorem r_leftSuspendTree_right (x : Tree) :
    Tree.r (leftSuspendTree x) = suspendTree (Tree.r x) := by
  cases x with
  | node cs =>
      have hcs := rList_leftSuspendBody_right cs
      simp [leftSuspendTree, suspendList, Tree.r, rList, hcs, leaf]

theorem rList_leftSuspendList_right (ts : List Tree) :
    rList (leftSuspendList ts) = suspendList (rList ts) := by
  simp [leftSuspendList, suspendList, rList, rList_leftSuspendBody_right, leaf]

theorem w_suspendList_left (ts : List Tree) :
    wList (suspendList ts) = leftSuspendList (wList ts) := by
  rw [wList, tList_suspendList, rList_suspendList_left]
  rfl

mutual
  theorem w_leftSuspendBody_tList (ts : List Tree) :
      wList (leftSuspendBody ts) = tList (leftSuspendBody (tList ts)) := by
    cases ts with
    | nil =>
        simp [leftSuspendBody, wList]
    | cons t ts =>
        cases t with
        | node cs =>
            have hcs := w_leftSuspendBody_tList cs
            have hts := w_leftSuspendBody_tList ts
            simpa [leftSuspendBody, leftSuspendList, wList, tList, rList, leaf]
              using And.intro hcs hts

  theorem w_leftSuspendList_tList (ts : List Tree) :
      wList (leftSuspendList ts) = tList (leftSuspendList (tList ts)) := by
    simp [leftSuspendList, w_leftSuspendBody_tList, tList, leaf]
end

theorem w2_leftSuspendList (ts : List Tree) :
    wList (wList (leftSuspendList ts)) = suspendList (wList ts) := by
  rw [w_leftSuspendList_tList]
  change rList (tList (tList (leftSuspendList (tList ts)))) = suspendList (wList ts)
  rw [tList_involutive]
  rw [rList_leftSuspendList_right]
  rfl

theorem w3_suspendList (ts : List Tree) :
    wList (wList (wList (suspendList ts))) =
      suspendList (wList (wList ts)) := by
  rw [w_suspendList_left]
  exact w2_leftSuspendList (wList ts)

theorem wListIter_three_suspendList (ts : List Tree) :
    wListIter 3 (suspendList ts) = suspendList (wListIter 2 ts) := by
  exact w3_suspendList ts

private theorem iterate_semiconj_apply {α : Type} {A B E : α → α}
    (h : ∀ x, A (E x) = E (B x)) :
    ∀ n x, Nat.iterate A n (E x) = E (Nat.iterate B n x)
  | 0, _ => rfl
  | n + 1, x => by
      change Nat.iterate A n (A (E x)) = E (Nat.iterate B n (B x))
      rw [h, iterate_semiconj_apply h n (B x)]

theorem wListIter_mul (a b : Nat) (ts : List Tree) :
    wListIter (a * b) ts = Nat.iterate (wListIter a) b ts := by
  unfold wListIter
  rw [Function.iterate_mul]

theorem wListIter_pow_three_suspendIter (r : Nat) (ts : List Tree) :
    wListIter (3 ^ r) (suspendIter r ts) =
      suspendIter r (wListIter (2 ^ r) ts) := by
  induction r generalizing ts with
  | zero =>
      simp [wListIter]
  | succ r ih =>
      have hbase :
          ∀ x, wListIter 3 (suspendList x) = suspendList (wListIter 2 x) := by
        intro x
        exact wListIter_three_suspendList x
      have hbaseIter :=
        iterate_semiconj_apply
          (A := wListIter 3) (B := wListIter 2) (E := suspendList)
          hbase (3 ^ r) (suspendIter r ts)
      have hbaseIter' :
          wListIter (3 ^ (Nat.succ r)) (suspendList (suspendIter r ts)) =
            suspendList (wListIter (2 * 3 ^ r) (suspendIter r ts)) := by
        simpa [wListIter_mul, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
          Nat.mul_assoc] using hbaseIter
      have htwice :=
        iterate_semiconj_apply
          (A := wListIter (3 ^ r)) (B := wListIter (2 ^ r))
          (E := suspendIter r) ih 2 ts
      have htwice' :
          wListIter (3 ^ r * 2) (suspendIter r ts) =
            suspendIter r (wListIter (2 ^ (Nat.succ r)) ts) := by
        simpa [wListIter_mul, Nat.pow_succ] using htwice
      calc
        wListIter (3 ^ Nat.succ r) (suspendIter (Nat.succ r) ts)
            = suspendList (wListIter (2 * 3 ^ r) (suspendIter r ts)) := by
                simpa using hbaseIter'
        _ = suspendList (suspendIter r (wListIter (2 ^ Nat.succ r) ts)) := by
                rw [show 2 * 3 ^ r = 3 ^ r * 2 by omega, htwice']
        _ = suspendIter (Nat.succ r) (wListIter (2 ^ Nat.succ r) ts) := rfl

end Tree
end Primitive
