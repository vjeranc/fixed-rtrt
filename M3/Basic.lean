import Mathlib

namespace LeanM3

mutual
  inductive Tree where
    | node : Forest → Tree
  deriving DecidableEq, Repr

  inductive Forest where
    | nil : Forest
    | cons : Tree → Forest → Forest
  deriving DecidableEq, Repr
end

namespace Forest

def append : Forest → Forest → Forest
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

instance : Append Forest where
  append := append

def singleton (t : Tree) : Forest := .cons t .nil

@[simp] theorem singleton_append (t : Tree) (xs : Forest) :
    singleton t ++ xs = .cons t xs := rfl
@[simp] theorem nil_append (xs : Forest) : .nil ++ xs = xs := rfl
@[simp] theorem cons_append (x : Tree) (xs ys : Forest) :
    (.cons x xs) ++ ys = .cons x (xs ++ ys) := rfl

@[simp] theorem append_nil : ∀ xs : Forest, xs ++ .nil = xs
  | .nil => rfl
  | .cons x xs => by simp [append_nil xs]

theorem append_assoc : ∀ xs ys zs : Forest, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | .nil, _, _ => rfl
  | .cons x xs, ys, zs => by simp [append_assoc xs ys zs]

end Forest

open Forest

def S (f : Forest) : Tree := .node f
abbrev leaf : Tree := S Forest.nil
abbrev wrap (f : Forest) : Forest := Forest.singleton (S f)

mutual
  def RTree : Tree → Tree
    | .node f => .node (RForest f)

  def RForest : Forest → Forest
    | .nil => .nil
    | .cons t ts => RForest ts ++ Forest.singleton (RTree t)
end

def T : Forest → Forest
  | .nil => .nil
  | .cons (.node a) b => .cons (S (T b)) (T a)

def M (f : Forest) : Forest := T (RForest f)

def bar (f g : Forest) : Forest := T (T g ++ T f)

def L : Nat → Forest
  | 0 => Forest.nil
  | n + 1 => .cons leaf (L n)

def P : Nat → Forest
  | 0 => Forest.nil
  | n + 1 => wrap (P n)

@[simp] theorem wrap_eq_singleton (f : Forest) : wrap f = Forest.singleton (S f) := rfl
@[simp] theorem T_nil : T Forest.nil = Forest.nil := rfl
@[simp] theorem T_cons_node (a b) : T (.cons (S a) b) = .cons (S (T b)) (T a) := rfl
@[simp] theorem T_wrap (f : Forest) : T (wrap f) = .cons leaf (T f) := rfl
@[simp] theorem T_cons_leaf (f : Forest) : T (Forest.cons leaf f) = wrap (T f) := rfl
@[simp] theorem T_wrap_append (f g : Forest) : T (wrap f ++ g) = wrap (T g) ++ T f := rfl

@[simp] theorem T_involutive : ∀ f : Forest, T (T f) = f
  | .nil => rfl
  | .cons (.node a) b => by simp [T, S, T_involutive a, T_involutive b]

theorem T_injective : Function.Injective T := by
  intro a b h; simpa using congrArg T h

@[simp] theorem R_singleton (t : Tree) :
    RForest (Forest.singleton t) = Forest.singleton (RTree t) := by
  simp [Forest.singleton, RForest]

@[simp] theorem R_wrap (f : Forest) : RForest (wrap f) = wrap (RForest f) := by
  simp [wrap, Forest.singleton, RForest, RTree, S]

@[simp] theorem R_append : ∀ xs ys : Forest, RForest (xs ++ ys) = RForest ys ++ RForest xs
  | .nil, ys => by cases ys <;> simp [RForest]
  | .cons x xs, ys => by simp [RForest, R_append xs ys, Forest.append_assoc]

@[simp] theorem T_bar (f g : Forest) : T (bar f g) = T g ++ T f := by simp [bar]

theorem bar_assoc (f g h : Forest) : bar (bar f g) h = bar f (bar g h) := by
  apply T_injective; simp [T_bar, Forest.append_assoc]

@[simp] theorem L_zero : L 0 = Forest.nil := rfl
@[simp] theorem L_succ (n : Nat) : L (n + 1) = .cons leaf (L n) := rfl
@[simp] theorem P_zero : P 0 = Forest.nil := rfl
@[simp] theorem P_succ (n : Nat) : P (n + 1) = wrap (P n) := rfl

theorem pnat_cast_eq (n : PNat) : n - 1 + 1 = (n : Nat) :=
  Nat.succ_pred_eq_of_pos n.2

theorem L_pos (n : PNat) : L n = Forest.cons leaf (L (n - 1)) := by
  rw [← pnat_cast_eq n, L_succ]; simp

theorem P_pos (n : PNat) : P n = wrap (P (n - 1)) := by
  rw [← pnat_cast_eq n, P_succ]; simp

@[simp] theorem L_append_leaf : ∀ n : Nat, L n ++ Forest.singleton leaf = L (n + 1)
  | 0 => rfl
  | n + 1 => by simp [L, L_append_leaf n]

@[simp] theorem T_L : ∀ n : Nat, T (L n) = P n
  | 0 => rfl
  | n + 1 => by simp [L, P, wrap, Forest.singleton, T_L n]

@[simp] theorem T_P : ∀ n : Nat, T (P n) = L n
  | 0 => rfl
  | n + 1 => by simp [P, T_P n, leaf]

@[simp] theorem R_L : ∀ n : Nat, RForest (L n) = L n
  | 0 => rfl
  | n + 1 => by rw [L, RForest, R_L n, show RTree leaf = leaf from rfl, L_append_leaf]; rfl

@[simp] theorem R_P : ∀ n : Nat, RForest (P n) = P n
  | 0 => rfl
  | n + 1 => by simp [P, Forest.singleton, RForest, RTree, S, R_P n]

inductive PComp where
  | single : PNat → PComp
  | cons : PNat → PComp → PComp

namespace PComp

def snoc : PComp → PNat → PComp
  | .single a, n => .cons a (.single n)
  | .cons a q, n => .cons a (snoc q n)

def ones (n : PNat) : PComp :=
  PNat.recOn n (.single 1) (fun _ ih => .cons 1 ih)

def incLast : PComp → PComp
  | .single n => .single (n + 1)
  | .cons n q => .cons n (incLast q)

def appendOnes : PComp → Nat → PComp
  | q, 0 => q
  | q, n + 1 => appendOnes (q.snoc 1) n

def rev : PComp → PComp
  | .single n => .single n
  | .cons n q => (rev q).snoc n

def succHead : PComp → PComp
  | .single n => .single (n + 1)
  | .cons n q => .cons (n + 1) q

end PComp

def A : PComp → Forest
  | .single n => L n
  | .cons n q => bar (L n) (A q)

def B : PComp → Forest
  | .single n => L n
  | .cons n q => L (n - 1) ++ wrap (B q)

def C : PComp → Forest
  | .single n => P n
  | .cons n q => P n ++ C q

def conj : PComp → PComp
  | .single n => PComp.ones n
  | .cons n q => PComp.appendOnes (PComp.incLast (conj q)) n.natPred

def cuts : PComp → List Bool
  | .single n => List.replicate n.natPred false
  | .cons n q => List.replicate n.natPred false ++ true :: cuts q

def revCompl (bs : List Bool) : List Bool := bs.reverse.map not

def fromCuts : List Bool → PComp
  | [] => .single 1
  | false :: bs => PComp.succHead (fromCuts bs)
  | true :: bs => PComp.cons 1 (fromCuts bs)

@[simp] theorem natPred_one : (1 : PNat).natPred = 0 := rfl

theorem natPred_succ (n : PNat) : (n + 1).natPred = n.natPred + 1 := by
  simp [PNat.natPred, PNat.add_coe]
  exact (Nat.succ_pred_eq_of_pos n.2).symm

theorem replicate_natPred_succ (n : PNat) (a : α) :
    List.replicate (n + 1).natPred a = a :: List.replicate n.natPred a := by
  rw [natPred_succ]; rfl

theorem cuts_ones_step (n : PNat) : cuts (PComp.ones (n + 1)) = true :: cuts (PComp.ones n) := by
  simp [PComp.ones, cuts]

theorem cuts_ones (n : PNat) : cuts (PComp.ones n) = List.replicate n.natPred true := by
  refine PNat.recOn n rfl ?_
  intro n ih
  rw [cuts_ones_step, ih, natPred_succ]; rfl

theorem cuts_incLast (q : PComp) : cuts (PComp.incLast q) = cuts q ++ [false] := by
  induction q with
  | single n =>
    show List.replicate (n + 1).natPred false = List.replicate n.natPred false ++ [false]
    rw [natPred_succ, List.replicate_add]; rfl
  | cons n q ih => simp [PComp.incLast, cuts, ih, List.append_assoc]

theorem cuts_snoc_one (q : PComp) : cuts (q.snoc 1) = cuts q ++ [true] := by
  induction q with
  | single n => rfl
  | cons n q ih => simp [PComp.snoc, cuts, ih, List.append_assoc]

theorem cuts_appendOnes (q : PComp) (m : Nat) :
    cuts (PComp.appendOnes q m) = cuts q ++ List.replicate m true := by
  induction m generalizing q with
  | zero => simp [PComp.appendOnes]
  | succ m ih =>
    rw [PComp.appendOnes, ih, cuts_snoc_one]
    simp [List.append_assoc, List.replicate_succ]

theorem cuts_conj (q : PComp) : cuts (conj q) = revCompl (cuts q) := by
  induction q with
  | single n =>
    rw [conj, cuts_ones]; simp [revCompl, cuts]
  | cons n q ih =>
    rw [conj, cuts_appendOnes, cuts_incLast, ih]
    simp [cuts, revCompl, List.reverse_append, List.map_append, List.append_assoc]

theorem cuts_succHead (q : PComp) : cuts (PComp.succHead q) = false :: cuts q := by
  cases q with
  | single n => exact replicate_natPred_succ n false
  | cons n q =>
    show List.replicate (n + 1).natPred false ++ true :: cuts q =
         false :: (List.replicate n.natPred false ++ true :: cuts q)
    rw [replicate_natPred_succ]; rfl

theorem fromCuts_replicate_false (n : PNat) :
    fromCuts (List.replicate n.natPred false) = PComp.single n := by
  refine PNat.recOn n rfl ?_
  intro n ih
  rw [replicate_natPred_succ]; simp [fromCuts, ih, PComp.succHead]

theorem fromCuts_false_run_true (n : PNat) (bs : List Bool) :
    fromCuts (List.replicate n.natPred false ++ true :: bs) = PComp.cons n (fromCuts bs) := by
  refine PNat.recOn n (by simp [fromCuts]) ?_
  intro n ih
  rw [replicate_natPred_succ]; simp [fromCuts, ih, PComp.succHead]

theorem cuts_fromCuts (bs : List Bool) : cuts (fromCuts bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [fromCuts, cuts_succHead, cuts, ih]

theorem fromCuts_cuts (q : PComp) : fromCuts (cuts q) = q := by
  induction q with
  | single n => simpa [cuts] using fromCuts_replicate_false n
  | cons n q ih => simpa [cuts, ih] using fromCuts_false_run_true n (cuts q)

theorem conj_eq_fromCuts_revCompl_cuts (q : PComp) :
    conj q = fromCuts (revCompl (cuts q)) := by
  rw [← cuts_conj, fromCuts_cuts]

theorem bar_L (f : Forest) (n : PNat) :
    bar f (L n) = wrap f ++ L (n - 1) := by
  apply T_injective; simp [bar, T_L, P_pos n]

theorem A_snoc (q : PComp) (n : PNat) :
    A (q.snoc n) = bar (A q) (L n) := by
  induction q with
  | single a => rfl
  | cons a q ih => simp [PComp.snoc, A, ih, bar_assoc]

theorem C_snoc (q : PComp) (n : PNat) :
    C (q.snoc n) = C q ++ P n := by
  induction q with
  | single a => rfl
  | cons a q ih => simp [PComp.snoc, C, ih, Forest.append_assoc]

@[simp] theorem rev_cons (n : PNat) (q : PComp) :
    PComp.rev (PComp.cons n q) = (PComp.rev q).snoc n := rfl

@[simp] theorem rev_snoc (q : PComp) (n : PNat) :
    PComp.rev (q.snoc n) = PComp.cons n (PComp.rev q) := by
  induction q with
  | single a => rfl
  | cons a q ih => simp [PComp.snoc, PComp.rev, ih]

@[simp] theorem rev_rev (q : PComp) : PComp.rev (PComp.rev q) = q := by
  induction q with
  | single n => rfl
  | cons n q ih => simp [ih]

theorem B_succHead (q : PComp) :
    B (PComp.succHead q) = L 1 ++ B q := by
  cases q with
  | single n => rfl
  | cons n q => simp [PComp.succHead, B]; rw [L_pos n]; rfl

theorem B_cons_one (q : PComp) :
    B (PComp.cons 1 q) = wrap (B q) := by
  simp [B, wrap, Forest.singleton]

theorem B_cons_succ (n : PNat) (q : PComp) :
    B (PComp.cons (n + 1) q) = L n ++ wrap (B q) := by simp [B]

theorem T_L_pos_wrap (n : PNat) (f : Forest) :
    T (L n ++ wrap f) = wrap (T (L (n - 1) ++ wrap f)) := by
  rw [L_pos n]; simp [Forest.singleton]

theorem succHead_snoc_one (q : PComp) :
    PComp.snoc (PComp.succHead q) 1 = PComp.succHead (PComp.snoc q 1) := by
  cases q <;> rfl

theorem incLast_succHead (q : PComp) :
    PComp.incLast (PComp.succHead q) = PComp.succHead (PComp.incLast q) := by
  cases q <;> rfl

theorem appendOnes_succHead (q : PComp) (m : Nat) :
    PComp.appendOnes (PComp.succHead q) m = PComp.succHead (PComp.appendOnes q m) := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih => rw [PComp.appendOnes, PComp.appendOnes, succHead_snoc_one, ih]

theorem appendOnes_cons (a : PNat) (q : PComp) (m : Nat) :
    PComp.appendOnes (PComp.cons a q) m = PComp.cons a (PComp.appendOnes q m) := by
  induction m generalizing q with
  | zero => rfl
  | succ m ih => rw [PComp.appendOnes, PComp.appendOnes]; simp [PComp.snoc, ih]

theorem appendOnes_one (n : PNat) :
    PComp.appendOnes (PComp.ones 1) n.natPred = PComp.ones n := by
  refine PNat.recOn n rfl ?_
  intro n ih
  rw [natPred_succ]
  simp [PComp.appendOnes, PComp.ones, PComp.snoc, appendOnes_cons]
  simpa [PComp.ones] using ih

theorem incLast_ones_succ (n : PNat) :
    PComp.incLast (PComp.ones (n + 1)) = PComp.cons 1 (PComp.incLast (PComp.ones n)) := by
  simp [PComp.ones, PComp.incLast]

theorem conj_snoc_one (q : PComp) :
    conj (q.snoc 1) = PComp.succHead (conj q) := by
  induction q with
  | single n =>
    rw [PComp.snoc, conj]
    simpa [PComp.incLast] using
      (appendOnes_succHead (PComp.ones 1) n.natPred).trans
        (congrArg PComp.succHead (appendOnes_one n))
  | cons n q ih =>
    rw [PComp.snoc, conj, ih, incLast_succHead, appendOnes_succHead]; simp [conj]

theorem conj_snoc_succ (q : PComp) (n : PNat) :
    conj (q.snoc (n + 1)) = PComp.cons 1 (conj (q.snoc n)) := by
  induction q with
  | single a =>
    rw [PComp.snoc, conj, conj, incLast_ones_succ, appendOnes_cons, PComp.snoc, conj]
    simp [conj]
  | cons a q ih =>
    rw [PComp.snoc, conj, ih, PComp.incLast, appendOnes_cons, PComp.snoc, conj]

theorem R_A_rev_eq_B (q : PComp) :
    RForest (A (PComp.rev q)) = B q := by
  induction q with
  | single n => simp [PComp.rev, A, B]
  | cons n q ih =>
    rw [PComp.rev, A_snoc, bar_L, R_append, R_L, R_wrap, ih]; simp [B]

theorem B_ones (n : PNat) :
    B (PComp.ones n) = P n := by
  refine PNat.recOn n rfl ?_
  intro n ih
  simp [PComp.ones, B, P_succ, wrap]
  exact congrArg (fun f => Forest.singleton (S f)) ih

theorem T_B_eq_B_conj_rev (q : PComp) :
    T (B q) = B (conj (PComp.rev q)) := by
  induction q with
  | single n => simpa [B, conj] using (B_ones n).symm
  | cons n q ih =>
    refine PNat.recOn n ?_ ?_
    · simpa [B, conj_snoc_one, B_succHead] using ih
    · intro n ihn
      rw [B_cons_succ, PComp.rev, conj_snoc_succ, B_cons_one]
      have hstep : T (L n ++ wrap (B q)) = wrap (T (B (PComp.cons n q))) := by
        simpa [B] using T_L_pos_wrap n (B q)
      simpa [PComp.rev] using hstep.trans (congrArg wrap ihn)

theorem M_A_eq_B_conj (q : PComp) :
    M (A q) = B (conj q) := by
  have h : RForest (A q) = B (PComp.rev q) := by
    simpa [rev_rev] using R_A_rev_eq_B (PComp.rev q)
  rw [M, h, T_B_eq_B_conj_rev (PComp.rev q), rev_rev]

theorem M_L_wrap (n : Nat) (f : Forest) :
    M (L n ++ wrap f) = P (n + 1) ++ M f := by
  rw [M, R_append, R_L, R_wrap, T_wrap_append]; simp [M, T_L, P_succ]

theorem M_B_eq_C (q : PComp) : M (B q) = C q := by
  induction q with
  | single n => simp [M, B, C, T_L]
  | cons n q ih => simpa [B, C, ih, P_pos n] using M_L_wrap (n - 1) (B q)

theorem M_P_append (n : Nat) (f : Forest) :
    M (P n ++ f) = bar (L n) (M f) := by
  apply T_injective; simp [M, T_bar, T_L, R_append, R_P]

theorem M_C_eq_A (q : PComp) : M (C q) = A q := by
  induction q with
  | single n => simp [M, C, A, T_P, R_P]
  | cons n q ih => simpa [C, A, ih] using M_P_append n (C q)

theorem M3_A_eq_A_conj (q : PComp) :
    M (M (M (A q))) = A (conj q) := by
  rw [M_A_eq_B_conj, M_B_eq_C, M_C_eq_A]

theorem M3_B_eq_B_conj (q : PComp) :
    M (M (M (B q))) = B (conj q) := by
  rw [M_B_eq_C, M_C_eq_A, M_A_eq_B_conj]

theorem M3_C_eq_C_conj (q : PComp) :
    M (M (M (C q))) = C (conj q) := by
  rw [M_C_eq_A, M_A_eq_B_conj, M_B_eq_C]

def FCorrPrefix : Forest :=
  Forest.singleton leaf ++
    wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf))

def FCorrSuffix : Forest :=
  wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf))

def GCorrPrefix : Forest :=
  wrap (wrap (Forest.singleton leaf) ++ Forest.singleton leaf)

def GCorrSuffix : Forest :=
  GCorrPrefix ++ Forest.singleton leaf

def FCorr (q : PComp) : Forest :=
  Forest.singleton leaf ++
    wrap (FCorrPrefix ++ C (PComp.incLast q) ++ FCorrSuffix)

def GCorr (q : PComp) : Forest :=
  wrap (GCorrPrefix ++ RForest (C (PComp.incLast q)) ++ GCorrSuffix) ++
    Forest.singleton leaf

mutual
theorem RTree_RTree : ∀ t : Tree, RTree (RTree t) = t
  | .node f => by simp [RTree, RForest_RForest f]

theorem RForest_RForest : ∀ f : Forest, RForest (RForest f) = f
  | .nil => rfl
  | .cons t ts => by
    simp [RForest, R_append, RForest_RForest ts, R_singleton, RTree_RTree t]
end

@[simp] theorem RForest_FCorrSuffix :
    RForest FCorrSuffix = GCorrPrefix := by
  decide

@[simp] theorem RForest_FCorrPrefix :
    RForest FCorrPrefix = GCorrSuffix := by
  decide

@[simp] theorem RForest_GCorrPrefix :
    RForest GCorrPrefix = FCorrSuffix := by
  decide

@[simp] theorem RForest_GCorrSuffix :
    RForest GCorrSuffix = FCorrPrefix := by
  decide

theorem RForest_FCorr (q : PComp) :
    RForest (FCorr q) = GCorr q := by
  unfold FCorr GCorr;
  
  have h_split : RForest (Forest.singleton leaf ++ wrap (FCorrPrefix ++ C q.incLast ++ FCorrSuffix)) = RForest (wrap (FCorrPrefix ++ C q.incLast ++ FCorrSuffix)) ++ RForest (Forest.singleton leaf) := by
    exact?;
  rw [ h_split, R_wrap ];
  rw [ R_append, R_append ] ; aesop;

theorem RForest_GCorr (q : PComp) :
    RForest (GCorr q) = FCorr q := by
  have := @RForest_FCorr;
  rw [ ← this, RForest_RForest ]

def Forest.len : Forest → Nat
  | .nil => 0
  | .cons _ f => 1 + f.len

@[simp] theorem Forest.len_nil : Forest.nil.len = 0 := rfl
@[simp] theorem Forest.len_cons (t : Tree) (f : Forest) :
    (Forest.cons t f).len = 1 + f.len := rfl

@[simp] theorem Forest.len_append (f g : Forest) :
    (f ++ g).len = f.len + g.len := by
  
  have h_len_append : ∀ (f g : Forest), Forest.len (f ++ g) = Forest.len f + Forest.len g := by
    intro f g
    have h_ind : ∀ (f : Forest), ∀ (n : ℕ), Forest.len f = n → ∀ (g : Forest), Forest.len (f ++ g) = n + Forest.len g := by
      intros f n hf g
      induction' n with n ih generalizing f g;
      · cases f <;> aesop;
      · rcases f with ( _ | ⟨ t, f ⟩ ) <;> simp_all +arith +decide
    exact h_ind f (Forest.len f) rfl g;
  exact h_len_append f g

@[simp] theorem Forest.len_singleton (t : Tree) :
    (Forest.singleton t).len = 1 := rfl

theorem FCorr_len (q : PComp) : (FCorr q).len = 2 := by
  
  simp [FCorr]

theorem GCorr_len (q : PComp) : (GCorr q).len = 2 := by
  unfold GCorr; aesop;

theorem L_len (n : Nat) : (L n).len = n := by
  induction' n with n ih;
  · rfl;
  · rw [ show L ( n + 1 ) = .cons leaf ( L n ) by rfl, Forest.len_cons ] ; linarith

theorem P_len : ∀ n : Nat, (P n).len = if n = 0 then 0 else 1
  | 0 => rfl
  | n + 1 => by
    aesop

theorem C_len_pos (q : PComp) : 0 < (C q).len := by
  induction' q with n q ih;
  · 
    have hP_len : ∀ n : ℕ+, (P n).len = 1 := by
      intro n; exact P_len n.val ▸ by simp +decide [ n.ne_zero ] ;
    convert hP_len n |> fun h => h.symm ▸ Nat.one_pos;
  · rw [ show C ( PComp.cons q ih ) = P q ++ C ih from rfl ] ; simp +arith +decide [ *, Forest.len_append ] ;

theorem FCorr_head (q : PComp) :
    ∃ f, FCorr q = Forest.cons leaf (Forest.cons (.node f) .nil) ∧ f ≠ .nil := by
  
  have h_unfold : FCorr q = Forest.cons leaf (Forest.cons (Tree.node (FCorrPrefix ++ C (PComp.incLast q) ++ FCorrSuffix)) Forest.nil) := by
    rfl;
  refine' ⟨ _, h_unfold, _ ⟩ ; intro h ; simp_all +decide [ FCorrPrefix, FCorrSuffix ] ;

theorem GCorr_head (q : PComp) :
    ∃ f, GCorr q = Forest.cons (.node f) (Forest.cons leaf .nil) ∧ f ≠ .nil := by
  
  simp [GCorr];
  unfold GCorrPrefix GCorrSuffix; aesop;

theorem A_single_eq_L (n : PNat) : A (.single n) = L n := rfl

theorem A_cons_head_ne_leaf (n : PNat) (q : PComp) :
    ∀ t rest, A (.cons n q) = .cons t rest → t ≠ leaf := by
  intro t rest h_eq
  have h_T : A (PComp.cons n q) = T (T (A q) ++ P n) := by
    
    have h_A_cons : A (PComp.cons n q) = bar (L n) (A q) := by
      exact?;
    rw [h_A_cons];
    unfold bar; aesop;
  rcases f : T ( A q ) with ( _ | ⟨ _, _ ⟩ ) <;> simp_all +decide;
  · rcases n with ⟨ _ | n, hn ⟩ <;> norm_num [ L ] at *;
    · contradiction;
    · have h_contra : ∀ f : Forest, T f = .nil → f = .nil := by
        intros f hf; exact (by
        have := T_involutive f; aesop;);
      
      have h_Aq_nil : A q = .nil := by
        exact h_contra _ f;
      cases q <;> simp_all +decide;
      · exact absurd h_Aq_nil ( by erw [ A_single_eq_L ] ; exact ne_of_apply_ne Forest.len ( by simp +decide [ L_len ] ) );
      · have h_contra : ∀ q : PComp, A q ≠ .nil := by
          intro q; induction q <;> simp_all +decide [ A ] ;
          · rename_i k hk;
            induction hk using PNat.recOn <;> simp_all +decide;
          · intro h; have := h_contra _ h; simp_all +decide;
            cases h : T ( A ‹_› ) <;> cases h' : P ↑‹ℕ+› <;> simp_all +decide;
        exact h_contra _ h_Aq_nil;
  · rename_i a b;
    cases a ; cases b <;> simp_all +decide;
    · cases h_eq;
      cases n using PNat.recOn <;> simp_all +decide [ P ];
      exact ne_of_apply_ne ( fun x => x ) ( by simp +decide [ S ] );
    · cases h_eq;
      simp +decide [ S, leaf ];
      cases ‹Tree› ; simp +decide [ T ]

theorem B_single_eq_L (n : PNat) : B (.single n) = L n := rfl

theorem B_len (q : PComp) : (B q).len ≥ 1 := by
  induction' q with n q ih;
  · rw [ B_single_eq_L ];
    exact Nat.one_le_iff_ne_zero.mpr ( by rw [ L_len ] ; positivity );
  · unfold B; aesop;

theorem FCorrInner_len_ge (q : PComp) :
    (FCorrPrefix ++ C (PComp.incLast q) ++ FCorrSuffix).len ≥ 4 := by
  rw [ Forest.len_append, Forest.len_append ];
  exact le_trans ( by decide ) ( add_le_add_three le_rfl ( C_len_pos _ ) ( show FCorrSuffix.len ≥ 1 from by decide ) )

theorem GCorrInner_len_ge (q : PComp) :
    (GCorrPrefix ++ RForest (C (PComp.incLast q)) ++ GCorrSuffix).len ≥ 4 := by
  norm_num [ GCorrPrefix, GCorrSuffix ];
  linarith [ show ( RForest ( C q.incLast ) ).len ≥ 1 from by
              have h_len : (C (PComp.incLast q)).len ≥ 1 := by
                exact C_len_pos _;
              have h_len : ∀ f : Forest, (RForest f).len = f.len := by
                intro f; exact (by
                induction' n : f.len using Nat.strong_induction_on with n ih generalizing f; rcases f with ( _ | ⟨ t, f ⟩ ) <;> simp_all +arith +decide;
                · aesop;
                · rw [ ← n, RForest ] ; aesop;);
              grind ]

theorem P_inner_len_le_one (n : PNat) :
    ∀ f, P n = .cons (.node f) .nil → f.len ≤ 1 := by
  intro f hf; have := P_len n; rcases n with ( _ | _ | n ) <;> norm_cast at *;
  · cases hf ; aesop;
  · cases hf ; aesop

theorem R_C_eq_C_rev (q : PComp) : RForest (C q) = C (PComp.rev q) := by
  induction q <;> simp_all +decide [ C ];
  · exact?;
  · exact?

theorem T_C_eq_A_rev (q : PComp) : T (C q) = A (PComp.rev q) := by
  induction' q with n q ih;
  · convert T_P n;
  · 
    have hC_cons : C (PComp.cons q ih) = P q ++ C ih := by
      rfl;
    
    have hA_rev_cons : A (PComp.rev (PComp.cons q ih)) = bar (A (PComp.rev ih)) (L q) := by
      convert A_snoc _ _ using 1;
    simp_all +decide [ bar ];
    rw [ ← ‹T ( C ih ) = A ih.rev› ];
    rw [ T_involutive ]

theorem M_FCorr (q : PComp) :
    M (FCorr q) = P 2 ++ M (FCorrPrefix ++ C (PComp.incLast q) ++ FCorrSuffix) := by
  convert M_L_wrap 1 _

theorem T_A_eq_C_rev (q : PComp) : T (A q) = C (PComp.rev q) := by
  by_contra h_contra;
  
  have h_T_A_rev_inv : T (A q) = T (T (C (PComp.rev q))) := by
    have h_T_A_rev : T (C q) = A (PComp.rev q) := by
      exact?
    generalize_proofs at *; (
    have h_T_A_rev_inv : T (A q) = T (T (C (PComp.rev q))) := by
      have := T_C_eq_A_rev (PComp.rev q)
      rw [ this, rev_rev ]
    generalize_proofs at *; (
    exact h_T_A_rev_inv))
  generalize_proofs at *; (
  exact h_contra ( h_T_A_rev_inv.trans ( by rw [ T_involutive ] ) ))

theorem R_B_eq_A_rev (q : PComp) : RForest (B q) = A (PComp.rev q) := by
  rw [ ← R_A_rev_eq_B ];
  exact?

theorem revCompl_append_false (bs : List Bool) :
    revCompl (bs ++ [false]) = [true] ++ revCompl bs := by
  simp [revCompl, List.reverse_append]

theorem conj_incLast (q : PComp) : conj (PComp.incLast q) = PComp.cons 1 (conj q) := by
  rw [conj_eq_fromCuts_revCompl_cuts, conj_eq_fromCuts_revCompl_cuts,
      cuts_incLast, revCompl_append_false]
  simp [fromCuts]

theorem R_FCorrPrefix_C_FCorrSuffix (f : Forest) :
    RForest (FCorrPrefix ++ f ++ FCorrSuffix) =
    GCorrPrefix ++ RForest f ++ GCorrSuffix := by
  simp [R_append, RForest_FCorrSuffix, RForest_FCorrPrefix, Forest.append_assoc]

def E1 (q : PComp) : Forest :=
  wrap (L 1) ++
  wrap (T (C (PComp.rev (PComp.incLast q)) ++ GCorrSuffix)) ++
  (wrap (L 1) ++ L 1)

def E2_inner (q : PComp) : Forest :=
  Forest.cons (S (Forest.cons (S (L 2))
    (T (RForest (T (C (PComp.rev (PComp.incLast q)) ++ GCorrSuffix))))))
    (L 1)

theorem M_FCorr_step1 (q : PComp) : M (FCorr q) = E1 q := by
  convert T_wrap_append _ _ using 1;
  rw [ R_FCorrPrefix_C_FCorrSuffix ];
  rw [ R_C_eq_C_rev ] ; aesop;

theorem M_FCorr_step2 (q : PComp) : M (E1 q) = wrap (E2_inner q) := by
  rfl

def foldOps : List Bool → Forest → Forest
  | [], base => base
  | (false :: rest), base => wrap (foldOps rest base)
  | (true :: rest), base => foldOps rest base ++ Forest.singleton leaf

@[simp] theorem foldOps_nil (base : Forest) : foldOps [] base = base := rfl
@[simp] theorem foldOps_false (rest : List Bool) (base : Forest) :
    foldOps (false :: rest) base = wrap (foldOps rest base) := rfl
@[simp] theorem foldOps_true (rest : List Bool) (base : Forest) :
    foldOps (true :: rest) base = foldOps rest base ++ Forest.singleton leaf := rfl

theorem foldOps_append (w1 w2 : List Bool) (base : Forest) :
    foldOps (w1 ++ w2) base = foldOps w1 (foldOps w2 base) := by
  induction' w1 with b w ih generalizing base <;> simp_all +decide;
  cases b <;> simp +decide [ *, foldOps ]

theorem foldOps_replicate_false (n : Nat) (base : Forest) :
    foldOps (List.replicate n false) base = Nat.iterate wrap n base := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply' ];
  simp_all +decide [ List.replicate ]

theorem R_foldOps_replicate_false (n : Nat) (f : Forest) :
    RForest (Nat.iterate wrap n f) = Nat.iterate wrap n (RForest f) := by
  induction' n with n ih generalizing f <;> simp_all +decide [ Function.iterate_succ_apply' ];
  erw [ show RTree ( S ( _ ) ) = S ( RForest _ ) from rfl ] ; aesop;

theorem R_cons_leaf (f : Forest) :
    RForest (Forest.cons leaf f) = RForest f ++ Forest.singleton leaf := by
  rfl

theorem T_L_append_wrap (k : Nat) (f : Forest) :
    T (L k ++ wrap f) = Nat.iterate wrap k (Forest.cons leaf (T f)) := by
  induction' k with k ih generalizing f <;> simp_all +decide [ Function.iterate_succ_apply' ];
  rfl

theorem RT2_GCorrSuffix_eq :
    RForest (T (RForest (T GCorrSuffix))) = wrap (T FCorrSuffix) := by
  native_decide

theorem RT2_C_GCorrSuffix (q : PComp) :
    RForest (T (RForest (T (C q ++ GCorrSuffix)))) =
    foldOps (cuts q ++ [true]) (RForest (T (RForest (T GCorrSuffix)))) := by
  induction' q using PComp.recOn with n q ih;
  · 
    have hC_single : C (PComp.single n) = P n := by
      rfl;
    induction n using PNat.recOn <;> simp_all +decide;
    
    have hT_iter : T (L ↑‹ℕ+› ++ wrap (RForest (T GCorrSuffix))) = Nat.iterate wrap ↑‹ℕ+› (cons leaf (T (RForest (T GCorrSuffix)))) := by
      convert T_L_append_wrap _ _ using 1;
    convert congr_arg RForest hT_iter using 1;
    · congr! 2;
      
      have hRForest_cons : ∀ t f, RForest (cons t f) = RForest f ++ singleton (RTree t) := by
        aesop;
      rw [ hRForest_cons ];
      congr! 1;
      exact?;
    · rw [ show cuts ( PComp.single ( _ + 1 ) ) = List.replicate ( ↑‹ℕ+› ) false from ?_ ];
      · induction' ( ‹ℕ+› : ℕ ) with n ih <;> simp_all +decide [ Function.iterate_succ_apply' ];
        exact?;
      · 
        simp [cuts];
        exact?;
  · 
    have hC : C (PComp.cons q ih) = P q ++ C ih := by
      exact?;
    have hT : T (P q ++ C ih ++ GCorrSuffix) = wrap (T (C ih ++ GCorrSuffix)) ++ L (q.natPred) := by
      cases q using PNat.recOn <;> aesop;
    have hR : RForest (wrap (T (C ih ++ GCorrSuffix)) ++ L (q.natPred)) = L (q.natPred) ++ wrap (RForest (T (C ih ++ GCorrSuffix))) := by
      rw [ R_append ] ; aesop;
    simp_all +decide [ cuts ];
    have hT : T (L q.natPred ++ Forest.singleton (S (RForest (T (C ih ++ GCorrSuffix))))) = Nat.iterate wrap q.natPred (Forest.cons leaf (T (RForest (T (C ih ++ GCorrSuffix))))) := by
      convert T_L_append_wrap q.natPred ( RForest ( T ( C ih ++ GCorrSuffix ) ) ) using 1;
    have hR : RForest (wrap^[q.natPred] (cons leaf (T (RForest (T (C ih ++ GCorrSuffix))))) ) = wrap^[q.natPred] (RForest (cons leaf (T (RForest (T (C ih ++ GCorrSuffix))))) ) := by
      exact?;
    have hR : RForest (cons leaf (T (RForest (T (C ih ++ GCorrSuffix))))) = RForest (T (RForest (T (C ih ++ GCorrSuffix)))) ++ Forest.singleton leaf := by
      exact?
    simp_all +decide;
    induction' q.natPred with n ih <;> simp_all +decide [ Function.iterate_succ_apply', List.replicate_succ ]

theorem wrap_T_C_FCorrSuffix (q : PComp) :
    wrap (T (C q ++ FCorrSuffix)) =
    foldOps ([false] ++ List.map not (cuts q)) (wrap (T FCorrSuffix)) := by
  induction' q using PComp.recOn with n q ih;
  · induction n using PNat.recOn <;> simp_all +decide;
    rename_i n ih; rw [ show C ( PComp.single ( n + 1 ) ) = P ( n + 1 ) from rfl ] ; simp +decide;
    unfold cuts; simp +decide;
    
    have h_foldOps : ∀ n : ℕ, foldOps (List.replicate n true) (Forest.singleton (S (T FCorrSuffix))) = Forest.singleton (S (T FCorrSuffix)) ++ L n := by
      intro n; induction n <;> simp_all +decide [ List.replicate ] ;
    exact h_foldOps n ▸ by rfl;
  · 
    have hC : C (PComp.cons q ih) = P q ++ C ih := by
      rfl;
    have hT : T (wrap (P (q - 1)) ++ C ih ++ FCorrSuffix) = wrap (T (C ih ++ FCorrSuffix)) ++ L (q - 1) := by
      have hT : T (wrap (P (q - 1)) ++ C ih ++ FCorrSuffix) = wrap (T (C ih ++ FCorrSuffix)) ++ L (q - 1) := by
        have hT_step : ∀ f g : Forest, T (wrap f ++ g) = wrap (T g) ++ T f := by
          exact?
        rw [ ← T_P ];
        convert hT_step _ _ using 1
      
      apply hT;
    rcases q with ( _ | _ | q ) <;> simp_all +decide ; tauto
    (generalize_proofs at *; aesop;);
    simp_all +decide [ cuts ];
    simp +decide [ List.replicate_add, foldOps_append ];
    congr! 2
    generalize_proofs at *; (
    refine' Nat.recOn q _ _ <;> simp_all +decide [ List.replicate ];
    intro n hn; rw [ ← hn ] ; simp +decide ;)

theorem cuts_rev (q : PComp) : cuts (PComp.rev q) = (cuts q).reverse := by
  
  by_contra h_contra;
  have h_cuts_rev : ∀ q : PComp, cuts q.rev = (cuts q).reverse := by
    intro q;
    have := @R_FCorrPrefix_C_FCorrSuffix;
    contrapose! this;
    use Forest.nil; simp +decide;
    exact this ( by
      induction' q using PComp.recOn with n q ih;
      · 
        simp [PComp.rev, cuts];
      · simp_all +decide [ PComp.rev, cuts ];
        
        have h_cuts_snoc : cuts (ih.rev.snoc q) = cuts ih.rev ++ [true] ++ List.replicate q.natPred false := by
          have h_cuts_snoc : ∀ q : PComp, ∀ n : PNat, cuts (q.snoc n) = cuts q ++ [true] ++ List.replicate n.natPred false := by
            intros q n; induction' q with n q ih generalizing n <;> simp_all +decide [ PComp.snoc ] ;
            · unfold cuts; aesop;
            · simp_all +decide [ cuts ];
          apply h_cuts_snoc;
        aesop );
  exact h_contra <| h_cuts_rev q

theorem RT2_word_eq (q : PComp) :
    cuts (PComp.rev (PComp.incLast q)) ++ [true] =
    [false] ++ List.map not (cuts (PComp.incLast (conj q))) := by
  rw [ cuts_rev, cuts_incLast, cuts_incLast ];
  rw [ cuts_conj ];
  unfold revCompl; aesop;

theorem RT2_key (q : PComp) :
    RForest (T (RForest (T (C (PComp.rev (PComp.incLast q)) ++ GCorrSuffix)))) =
    wrap (T (C (PComp.incLast (conj q)) ++ FCorrSuffix)) := by
  rw [RT2_C_GCorrSuffix, RT2_GCorrSuffix_eq, wrap_T_C_FCorrSuffix, RT2_word_eq]

theorem M_FCorr_step3 (q : PComp) : M (wrap (E2_inner q)) = FCorr (conj q) := by
  unfold M E2_inner FCorr;
  unfold Forest.singleton wrap FCorrPrefix; simp_all +decide;
  convert T_wrap _ using 1;
  unfold Forest.singleton; simp +decide [ RForest ] ;
  unfold T; simp +decide [ RTree, S ] ;
  unfold T; simp +decide [ Forest.singleton, RForest ] ;
  rw [ RT2_key ] ; simp +decide [ RTree ] ;

theorem M3_FCorr (q : PComp) : M (M (M (FCorr q))) = FCorr (conj q) := by
  rw [M_FCorr_step1, M_FCorr_step2, M_FCorr_step3]

theorem conj_involutive (q : PComp) : conj (conj q) = q := by
  
  have h_simp : fromCuts (revCompl (revCompl (cuts q))) = q := by
    convert fromCuts_cuts q using 1;
    unfold revCompl;
    exact congr_arg _ ( by ext; simp +decide [ Function.comp ] );
  rw [ ← h_simp, ← cuts_conj ];
  rw [ ← cuts_conj ];
  
  simp [conj_eq_fromCuts_revCompl_cuts];
  rw [ cuts_fromCuts, cuts_fromCuts ];
  simp +decide [ revCompl ];
  exact congr_arg _ ( by ext; simp +decide [ Function.comp ] )

theorem M3_GCorr (q : PComp) : M (M (M (GCorr q))) = GCorr (conj q) := by
  
  have := M3_FCorr ( conj q ) ; simp_all +decide [ M ] ;
  rw [ show conj ( conj q ) = q from conj_involutive q ] at this; simp_all +decide [ RForest_FCorr, RForest_GCorr ] ;
  rw [ ← this ] at *; simp_all +decide;
  simp +decide [ RForest_RForest ]

theorem M3_FCorr_of_selfconj (q : PComp) (hq : conj q = q) :
    M (M (M (FCorr q))) = FCorr q := by
  rw [M3_FCorr, hq]

theorem M3_GCorr_of_selfconj (q : PComp) (hq : conj q = q) :
    M (M (M (GCorr q))) = GCorr q := by
  rw [M3_GCorr, hq]

theorem M3_of_phase_chain {α : Type} (X X1 X2 : α → Forest) (σ : α → α)
    (h0 : ∀ a, M (X a) = X1 a)
    (h1 : ∀ a, M (X1 a) = X2 a)
    (h2 : ∀ a, M (X2 a) = X (σ a)) :
    ∀ a, M (M (M (X a))) = X (σ a) := by
  intro a
  rw [h0, h1, h2]

def Minv (f : Forest) : Forest := RForest (T f)

@[simp] theorem Minv_M (f : Forest) : Minv (M f) = f := by
  simp [Minv, M, RForest_RForest, T_involutive]

@[simp] theorem M_Minv (f : Forest) : M (Minv f) = f := by
  simp [Minv, M, RForest_RForest, T_involutive]

@[simp] theorem R_M_eq_Minv_R (f : Forest) :
    RForest (M f) = Minv (RForest f) := by
  rfl

def RectC : Nat → Forest
  | 0 => Forest.nil
  | n + 1 => RectC n ++ P 2

def RectA : Nat → Forest
  | 0 => Forest.nil
  | n + 1 => bar (RectA n) (L 2)

def JCorrInnerPrefix : Forest :=
  wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf) ++ Forest.singleton leaf)

def JCorrInnerSuffix : Forest :=
  wrap (wrap (Forest.singleton leaf) ++ Forest.singleton leaf) ++
    wrap (Forest.singleton leaf)

def KCorrInnerPrefix : Forest :=
  wrap (Forest.singleton leaf) ++
    wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf))

def KCorrInnerSuffix : Forest :=
  wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf) ++ Forest.singleton leaf)

def JCorr (t : Nat) : Forest :=
  wrap (Forest.singleton leaf) ++
    wrap (JCorrInnerPrefix ++ RectC t ++ JCorrInnerSuffix) ++
    Forest.singleton leaf

def KCorr (t : Nat) : Forest :=
  Forest.singleton leaf ++
    wrap (KCorrInnerPrefix ++ RectC t ++ KCorrInnerSuffix) ++
    wrap (Forest.singleton leaf)

def FCorrPhase1BarLeft : Forest :=
  wrap (Forest.singleton leaf) ++ wrap (Forest.singleton leaf) ++ Forest.singleton leaf

def FCorrPhase1Right : Forest :=
  wrap (Forest.singleton leaf) ++ Forest.singleton leaf

def GCorrPhase1BarPref : Forest :=
  Forest.singleton leaf ++ wrap (Forest.singleton leaf ++ Forest.singleton leaf)

def GCorrPhase1BarSuff : Forest :=
  wrap (Forest.singleton leaf ++ wrap (Forest.singleton leaf ++ Forest.singleton leaf))

def FCorrPhase1 (q : PComp) : Forest :=
  wrap (Forest.singleton leaf) ++
    wrap (bar FCorrPhase1BarLeft (A (PComp.incLast q))) ++
    FCorrPhase1Right

def GCorrPhase1 (q : PComp) : Forest :=
  wrap (Forest.singleton leaf ++
    bar (bar GCorrPhase1BarPref (A (PComp.rev (PComp.incLast q)))) GCorrPhase1BarSuff)

def JCorrPhase1 (t : Nat) : Forest :=
  wrap (wrap (Forest.singleton leaf ++ Forest.singleton leaf) ++
    bar
      (Forest.singleton leaf ++
        wrap (wrap (Forest.singleton leaf) ++ Forest.singleton leaf))
      (bar (RectA t) GCorrPhase1BarSuff) ++
    Forest.singleton leaf)

def KCorrPhase1 (t : Nat) : Forest :=
  bar
    (wrap (Forest.singleton leaf) ++
      wrap
        (bar
          (wrap (Forest.singleton leaf ++ Forest.singleton leaf) ++
            wrap (Forest.singleton leaf) ++
            Forest.singleton leaf)
          (RectA t)) ++
      wrap (wrap (Forest.singleton leaf) ++ Forest.singleton leaf))
    (Forest.singleton leaf ++ Forest.singleton leaf)

def FCorrPhase2 (q : PComp) : Forest := M (FCorrPhase1 q)
def GCorrPhase2 (q : PComp) : Forest := M (GCorrPhase1 q)
def JCorrPhase2 (t : Nat) : Forest := RForest (KCorrPhase1 t)
def KCorrPhase2 (t : Nat) : Forest := RForest (JCorrPhase1 t)

@[simp] theorem R_JCorrPhase1 (t : Nat) :
    RForest (JCorrPhase1 t) = KCorrPhase2 t := by
  rfl

@[simp] theorem R_KCorrPhase1 (t : Nat) :
    RForest (KCorrPhase1 t) = JCorrPhase2 t := by
  rfl

theorem RectC_comm (t : Nat) : P 2 ++ RectC t = RectC t ++ P 2 := by
  induction t with
  | zero => simp [RectC]
  | succ t ih =>
      simp only [RectC]
      rw [← Forest.append_assoc, ih, Forest.append_assoc]

theorem R_RectC (t : Nat) : RForest (RectC t) = RectC t := by
  induction t with
  | zero => simp [RectC, RForest]
  | succ t ih =>
      simp only [RectC, R_append, R_P, ih]
      exact RectC_comm t

@[simp] theorem RForest_JCorrInnerSuffix :
    RForest JCorrInnerSuffix = KCorrInnerPrefix := by native_decide

@[simp] theorem RForest_JCorrInnerPrefix :
    RForest JCorrInnerPrefix = KCorrInnerSuffix := by native_decide

@[simp] theorem RForest_KCorrInnerPrefix :
    RForest KCorrInnerPrefix = JCorrInnerSuffix := by native_decide

@[simp] theorem RForest_KCorrInnerSuffix :
    RForest KCorrInnerSuffix = JCorrInnerPrefix := by native_decide

theorem R_JCorrInner (t : Nat) :
    RForest (JCorrInnerPrefix ++ RectC t ++ JCorrInnerSuffix) =
    KCorrInnerPrefix ++ RectC t ++ KCorrInnerSuffix := by
  simp [R_append, R_RectC, Forest.append_assoc]

theorem RForest_JCorr (t : Nat) : RForest (JCorr t) = KCorr t := by
  have h_distribute :
      RForest (wrap (JCorrInnerPrefix ++ RectC t ++ JCorrInnerSuffix) ++
          Forest.singleton leaf) =
        Forest.singleton leaf ++
          wrap (RForest (JCorrInnerPrefix ++ RectC t ++ JCorrInnerSuffix)) := by
    congr
  have h_distribute :
      RForest (wrap (JCorrInnerPrefix ++ RectC t ++ JCorrInnerSuffix) ++
          Forest.singleton leaf) =
        Forest.singleton leaf ++ wrap (KCorrInnerPrefix ++ RectC t ++ KCorrInnerSuffix) := by
    rw [h_distribute, R_JCorrInner]
  convert congr_arg (fun x => x ++ wrap (Forest.singleton leaf)) h_distribute using 1

theorem RForest_KCorr (t : Nat) : RForest (KCorr t) = JCorr t := by
  have := RForest_JCorr t
  rw [← this, RForest_RForest]

theorem M_FCorr_phase0_to_phase1 (q : PComp) :
    M (FCorr q) = FCorrPhase1 q := by
  rw [M_FCorr_step1, FCorrPhase1]
  unfold E1 FCorrPhase1BarLeft FCorrPhase1Right
  rw [← T_A_eq_C_rev]
  congr! 2

theorem M_GCorr_phase0_to_phase1 (q : PComp) :
    M (GCorr q) = GCorrPhase1 q := by
  have h_M_GCorr : M (GCorr q) = T (RForest (GCorr q)) := by
    rfl
  unfold GCorrPhase1 GCorrPhase1BarPref GCorrPhase1BarSuff
  rw [h_M_GCorr, RForest_GCorr]
  unfold FCorr FCorrPrefix FCorrSuffix
  simp +arith +decide
  unfold bar
  simp +arith +decide
  unfold Forest.singleton
  simp +arith +decide [T_A_eq_C_rev]

theorem M_JCorr_phase0_to_phase1 (t : Nat) :
    M (JCorr t) = JCorrPhase1 t := by
  unfold M JCorr JCorrPhase1
  simp +decide [JCorrInnerPrefix, JCorrInnerSuffix] at *
  simp_all +decide [RForest, Forest.singleton]
  simp_all +decide [RTree, S, bar]
  simp_all +decide [T, RForest, Forest.singleton]
  simp_all +decide [T, RTree, S, GCorrPhase1BarSuff]
  simp_all +decide [T, S, Forest.singleton]
  congr! 2
  induction' t with t ih
  · rfl
  · simp_all +decide [RectC, RectA]

theorem M_KCorr_phase0_to_phase1 (t : Nat) :
    M (KCorr t) = KCorrPhase1 t := by
  unfold KCorrPhase1 KCorr at *
  simp_all +decide [M]
  simp [RForest] at *
  simp [T, RTree, S]
  congr
  simp [T, bar] at *
  induction t <;> simp_all +decide [JCorrInnerPrefix, JCorrInnerSuffix, RectC, RectA]

theorem MM_JCorr_eq_R_KCorrPhase1 (t : Nat) :
    M (M (JCorr t)) = RForest (KCorrPhase1 t) := by
  unfold M
  unfold JCorr KCorrPhase1
  simp +decide [RForest, JCorrInnerPrefix, JCorrInnerSuffix]
  simp +decide [RTree, S, Forest.singleton, T, RForest, bar]
  induction t <;> simp_all +decide [RectC, RectA]
  simp_all +decide [RForest, T, RTree, S, Forest.singleton]

theorem MM_KCorr_eq_R_JCorrPhase1 (t : Nat) :
    M (M (KCorr t)) = RForest (JCorrPhase1 t) := by
  unfold M KCorr JCorrPhase1
  simp +decide [RTree, S, Forest.singleton, T, RForest, bar] at *
  induction t <;> simp_all +decide [JCorrInnerPrefix, JCorrInnerSuffix, GCorrPhase1BarSuff]
  simp_all +decide [RForest, T, RTree, S, Forest.singleton, RectC, RectA]

theorem M_FCorr_phase1_to_phase2 (q : PComp) :
    M (FCorrPhase1 q) = FCorrPhase2 q := by
  rfl

theorem M_GCorr_phase1_to_phase2 (q : PComp) :
    M (GCorrPhase1 q) = GCorrPhase2 q := by
  rfl

theorem M_JCorr_phase1_to_phase2 (t : Nat) :
    M (JCorrPhase1 t) = JCorrPhase2 t := by
  rw [← M_JCorr_phase0_to_phase1 t]
  unfold JCorrPhase2
  exact MM_JCorr_eq_R_KCorrPhase1 t

theorem M_KCorr_phase1_to_phase2 (t : Nat) :
    M (KCorrPhase1 t) = KCorrPhase2 t := by
  rw [← M_KCorr_phase0_to_phase1 t]
  unfold KCorrPhase2
  exact MM_KCorr_eq_R_JCorrPhase1 t

theorem M_FCorr_phase2_to_phase0 (q : PComp) :
    M (FCorrPhase2 q) = FCorr (conj q) := by
  unfold FCorrPhase2
  rw [← M_FCorr_phase0_to_phase1 q]
  exact M3_FCorr q

theorem M_GCorr_phase2_to_phase0 (q : PComp) :
    M (GCorrPhase2 q) = GCorr (conj q) := by
  unfold GCorrPhase2
  rw [← M_GCorr_phase0_to_phase1 q]
  exact M3_GCorr q

theorem M_JCorr_phase2_to_phase0 (t : Nat) :
    M (JCorrPhase2 t) = JCorr t := by
  show M (RForest (KCorrPhase1 t)) = JCorr t
  simp only [M, RForest_RForest]
  rw [show KCorrPhase1 t = M (KCorr t) from (M_KCorr_phase0_to_phase1 t).symm]
  simp only [M, T_involutive]
  exact RForest_KCorr t

theorem M_KCorr_phase2_to_phase0 (t : Nat) :
    M (KCorrPhase2 t) = KCorr t := by
  show M (RForest (JCorrPhase1 t)) = KCorr t
  simp only [M, RForest_RForest]
  rw [show JCorrPhase1 t = M (JCorr t) from (M_JCorr_phase0_to_phase1 t).symm]
  simp only [M, T_involutive]
  exact RForest_JCorr t

theorem M3_FCorr_viaFormulaPhases (q : PComp) :
    M (M (M (FCorr q))) = FCorr (conj q) := by
  simpa using
    M3_of_phase_chain FCorr FCorrPhase1 FCorrPhase2 conj
      M_FCorr_phase0_to_phase1
      M_FCorr_phase1_to_phase2
      M_FCorr_phase2_to_phase0 q

theorem M3_GCorr_viaFormulaPhases (q : PComp) :
    M (M (M (GCorr q))) = GCorr (conj q) := by
  simpa using
    M3_of_phase_chain GCorr GCorrPhase1 GCorrPhase2 conj
      M_GCorr_phase0_to_phase1
      M_GCorr_phase1_to_phase2
      M_GCorr_phase2_to_phase0 q

theorem M3_JCorr_viaFormulaPhases (t : Nat) :
    M (M (M (JCorr t))) = JCorr t := by
  simpa using
    M3_of_phase_chain JCorr JCorrPhase1 JCorrPhase2 id
      M_JCorr_phase0_to_phase1
      M_JCorr_phase1_to_phase2
      M_JCorr_phase2_to_phase0 t

theorem M3_KCorr_viaFormulaPhases (t : Nat) :
    M (M (M (KCorr t))) = KCorr t := by
  simpa using
    M3_of_phase_chain KCorr KCorrPhase1 KCorrPhase2 id
      M_KCorr_phase0_to_phase1
      M_KCorr_phase1_to_phase2
      M_KCorr_phase2_to_phase0 t

theorem FCorr_ne_A (q q' : PComp) : FCorr q ≠ A q' := by
  
  by_contra h_eq;
  
  have h_start : ∀ t rest, FCorr q = .cons t rest → t = leaf := by
    unfold FCorr; aesop;
  have h_start' : ∀ t rest, A q' = .cons t rest → t ≠ leaf := by
    intro t rest h_eq'
    by_cases hq' : q' = .single 1;
    · obtain ⟨ f, hf ⟩ := FCorr_head q;
      cases q' : q' <;> simp_all +decide [ A ];
    · rcases q' with ( _ | ⟨ n, q' ⟩ ) <;> simp_all +decide;
      · unfold A at h_eq';
        rcases n : ( ‹ℕ+› : ℕ+ ) with ( _ | _ | n ) <;> simp_all +decide [ L ];
        cases h_eq' ▸ h_eq.symm;
      · exact absurd ( A_cons_head_ne_leaf n q' _ _ h_eq' ) ( by aesop );
  rcases h : A q' with ( _ | ⟨ t, rest ⟩ ) <;> simp_all +decide;
  cases FCorr_head q ; aesop

theorem FCorr_ne_B (q q' : PComp) : FCorr q ≠ B q' := by
  have := FCorr_len q; have := B_len q'; simp_all +decide [ FCorr ] ;
  rcases q' with ( _ | ⟨ _ | _ | q' ⟩ ) <;> ( ( simp_all +decide [ B ] ; ) );
  · rcases a : ( ‹ℕ+› : ℕ+ ) with ( _ | _ | a ) <;> simp_all +decide [ L ] ; tauto;
    rintro ⟨ ⟩;
  · contradiction;
  · exact ne_of_apply_ne ( fun f => f ) ( by simp +decide [ Forest.singleton ] );
  · intro h; have := congr_arg Forest.len h; simp +decide at this; (
    cases q' <;> simp_all +decide [ L ];
    injection h ; simp_all +decide;
    rename_i k hk; have := congr_arg ( fun x => x = S ( B k ) ) ‹_›; simp_all +decide [ S ] ;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ FCorrPrefix, FCorrSuffix, B ];
    · rename_i n; replace hk := congr_arg ( fun f => f ) hk; rcases n with ( _ | _ | n ) <;> simp_all +decide [ L ] ;
    · contradiction;
    · replace hk := congr_arg ( fun f => f ) hk ; simp_all +decide [ Forest.singleton ] ;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ L ];
      exact absurd hk.2 ( by exact ne_of_apply_ne ( fun f => f.len ) ( by simp +decide [ Forest.len ] ) ));

theorem FCorr_ne_C (q q' : PComp) : FCorr q ≠ C q' := by
  
  by_cases h_len : (C q').len = 1 ∨ (C q').len ≥ 2;
  · cases h_len <;> simp_all +decide;
    · obtain ⟨f, hf⟩ := FCorr_head q; simp_all +decide;
      cases h : C q' <;> aesop ( simp_config := { decide := true } ) ;
    · intro h; have := FCorr_len q; have := P_len 0; have := P_len 1; have := P_len 2; simp_all +decide ;
      rcases q' with ( _ | ⟨ n, _ | ⟨ m, q' ⟩ ⟩ ) <;> simp_all +decide [ FCorr, C ] ; (
      cases ‹ℕ+› using PNat.recOn <;> simp_all +decide [ P ]);
      · cases n using PNat.recOn <;> cases ‹ℕ+› using PNat.recOn <;> simp_all +decide [ P ] ; (
        cases h);
        · injection h with h ; simp_all +decide [ S ] ; (
          have := congr_arg Forest.len h ; simp_all +decide [ FCorrPrefix, FCorrSuffix ] ; (
          rename_i n hn; rcases n with ( _ | _ | n ) <;> norm_cast at *;
          · cases h;
          · cases h));
        · cases h.1;
      · rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> simp_all +arith +decide ; tauto;
        all_goals have := C_len_pos q'; simp_all +decide [ Forest.singleton ] ;
  · 
    have h_contra : (C q').len = 0 := by
      omega;
    exact absurd h_contra (by linarith [C_len_pos q'])

theorem GCorr_ne_A (q q' : PComp) : GCorr q ≠ A q' := by
  have := FCorr_ne_A q ( PComp.rev q' ) ; simp_all +decide;
  convert this using 1;
  constructor <;> intro h <;> have := RForest_GCorr q <;> simp_all +decide;
  have h_conj : RForest (A q') = B (PComp.rev q') := by
    convert R_A_rev_eq_B ( PComp.rev q' ) using 1 ; aesop ( simp_config := { singlePass := true } ) ;
  have := FCorr_ne_B q ( PComp.rev q' ) ; simp_all +decide;

theorem GCorr_ne_B (q q' : PComp) : GCorr q ≠ B q' := by
  induction' q' with n q' ih;
  · unfold GCorr B;
    cases n using PNat.recOn <;> simp +decide [ L ];
    rintro ⟨ ⟩;
  · rcases q' with ( _ | _ | q' ) <;> simp +arith +decide [ *, GCorr ];
    · contradiction;
    · unfold B; simp +decide [ * ] ;
      exact ne_of_apply_ne ( fun f => f ) ( by simp +decide [ Forest.singleton ] );
    · intro h; have := congr_arg ( fun f => f.len ) h; simp +arith +decide [ * ] at this;
      cases h

theorem GCorr_ne_C (q q' : PComp) : GCorr q ≠ C q' := by
  unfold GCorr;
  cases q' <;> simp_all +decide [ Forest.singleton ];
  · cases ‹ℕ+› using PNat.recOn <;> simp_all +decide [ C ];
    · exact ne_of_apply_ne ( fun x => x ) ( by rintro ⟨ ⟩ );
    · unfold Forest.singleton; aesop;
  · rename_i n q';
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ C ];
    · contradiction;
    · exact fun h => absurd h ( by rintro ⟨ ⟩ );
    · intro h₁ h₂; replace h₁ := congr_arg ( fun f => f = S ( Forest.singleton ( S ( P n ) ) ) ) h₁; simp_all +decide [ S ] ;
      replace h₁ := congr_arg Forest.len h₁ ; simp_all +decide;
      exact absurd h₁ ( by { exact ne_of_gt ( lt_add_of_pos_of_le ( add_pos_of_pos_of_nonneg ( by decide ) ( Nat.zero_le _ ) ) ( by decide ) ) } )

end LeanM3
