import M2.Tree

namespace Primitive
namespace Tree

def squeezeMid : List Tree → List Tree
  | [] => []
  | t :: ts =>
      match ts with
      | [] => [t]
      | m :: us =>
          match t with
          | .node [] => squeezeMid (m :: us)
          | _ => t :: squeezeMid (m :: us)

def squeezeOuter : List Tree → List Tree
  | [] => []
  | t :: ts => t :: squeezeMid ts

def contractRoot : List Tree → List Tree
  | [Tree.node []] => [leaf]
  | [Tree.node (c :: cs)] => c :: cs
  | ts => ts

mutual
  def primInner : Tree → Tree
    | .node ts => .node (contractRoot (primList ts))

  def primChildrenRaw : List Tree → List Tree
    | [] => []
    | t :: ts => primInner t :: primChildrenRaw ts

  def primList : List Tree → List Tree
    | ts => squeezeOuter (primChildrenRaw ts)
end

def prim : Tree → Tree
  | .node ts => .node (primList ts)

def Prim (x : Tree) : Prop := prim x = x

@[simp] theorem primChildrenRaw_nil : primChildrenRaw [] = [] := by
  simp [primChildrenRaw]
@[simp] theorem primChildrenRaw_cons (t : Tree) (ts : List Tree) :
    primChildrenRaw (t :: ts) = primInner t :: primChildrenRaw ts := by
  simp [primChildrenRaw]
@[simp] theorem primList_eq (ts : List Tree) :
    primList ts = squeezeOuter (primChildrenRaw ts) := by
  simp [primList]

@[simp] theorem primInner_node (ts : List Tree) :
    primInner (.node ts) = .node (contractRoot (primList ts)) := by
  simp [primInner]

@[simp] theorem prim_node (ts : List Tree) :
    prim (.node ts) = .node (primList ts) := by
  simp [prim]

@[simp] theorem Prim_def (x : Tree) : Prim x ↔ prim x = x := Iff.rfl

@[simp] theorem primInner_leaf : primInner leaf = leaf := by
  simp [leaf, contractRoot, squeezeOuter]

@[simp] theorem prim_leaf : prim leaf = leaf := by
  simp [leaf, prim, squeezeOuter]

@[simp] theorem prim_node_nil : prim (.node []) = .node [] := by
  simpa [leaf] using prim_leaf

@[simp] theorem primInner_singleton_leaf : primInner (.node [leaf]) = .node [leaf] := by
  simp [contractRoot, leaf, squeezeOuter, squeezeMid]

@[simp] theorem prim_singleton_leaf : prim (.node [leaf]) = .node [leaf] := by
  simp [prim, leaf, squeezeOuter, squeezeMid, contractRoot]

theorem squeezeOuter_ne_nil_of_cons (t : Tree) (ts : List Tree) :
    squeezeOuter (t :: ts) ≠ [] := by
  simp [squeezeOuter]

theorem contractRoot_ne_nil_of_ne_nil {ts : List Tree} (h : ts ≠ []) :
    contractRoot ts ≠ [] := by
  cases ts with
  | nil => exact False.elim (h rfl)
  | cons t ts =>
      cases ts with
      | nil =>
          cases t with
          | node cs =>
              cases cs with
              | nil => simp [contractRoot, leaf]
              | cons c cs => simp [contractRoot]
      | cons m us => simp [contractRoot]

theorem primList_ne_nil_of_cons (t : Tree) (ts : List Tree) :
    primList (t :: ts) ≠ [] := by
  simpa [primList, primChildrenRaw] using
    squeezeOuter_ne_nil_of_cons (primInner t) (primChildrenRaw ts)

theorem primInner_node_cons_exists_cons (a : Tree) (as : List Tree) :
    ∃ b bs, primInner (.node (a :: as)) = .node (b :: bs) := by
  have hne : contractRoot (primList (a :: as)) ≠ [] := by
    apply contractRoot_ne_nil_of_ne_nil
    simpa using primList_ne_nil_of_cons a as
  cases hbs : contractRoot (primList (a :: as)) with
  | nil => exact False.elim (hne hbs)
  | cons b bs' =>
      exact ⟨b, bs', by
        simpa [primInner, primList] using congrArg Tree.node hbs⟩

@[simp] theorem primChildrenRaw_squeezeMid : ∀ ts : List Tree,
    primChildrenRaw (squeezeMid ts) = squeezeMid (primChildrenRaw ts)
  | [] => by simp [squeezeMid]
  | t :: ts => by
      cases ts with
      | nil => simp [squeezeMid]
      | cons m us =>
          cases t with
          | node cs =>
              cases cs with
              | nil => simpa [squeezeMid] using primChildrenRaw_squeezeMid (m :: us)
              | cons a as =>
                  rcases primInner_node_cons_exists_cons a as with ⟨b, bs, hprim⟩
                  simp [squeezeMid, hprim, primChildrenRaw_squeezeMid (m :: us)]

@[simp] theorem primChildrenRaw_squeezeOuter : ∀ ts : List Tree,
    primChildrenRaw (squeezeOuter ts) = squeezeOuter (primChildrenRaw ts)
  | [] => by simp [squeezeOuter]
  | t :: ts => by simp [squeezeOuter, primChildrenRaw_squeezeMid]

theorem squeezeMid_ne_nil_of_cons (t : Tree) (ts : List Tree) :
    squeezeMid (t :: ts) ≠ [] := by
  cases ts with
  | nil => simp [squeezeMid]
  | cons m us =>
      cases t with
      | node cs =>
          cases cs with
          | nil => simpa [squeezeMid] using squeezeMid_ne_nil_of_cons m us
          | cons a as => simp [squeezeMid]

@[simp] theorem squeezeMid_idem : ∀ ts : List Tree, squeezeMid (squeezeMid ts) = squeezeMid ts
  | [] => rfl
  | t :: ts => by
      cases ts with
      | nil => simp [squeezeMid]
      | cons m us =>
          cases t with
          | node cs =>
              cases cs with
              | nil => simpa [squeezeMid] using squeezeMid_idem (m :: us)
              | cons a as =>
                  have hne : squeezeMid (m :: us) ≠ [] := squeezeMid_ne_nil_of_cons m us
                  cases hs : squeezeMid (m :: us) with
                  | nil => exact False.elim (hne hs)
                  | cons v vs => simpa [squeezeMid, hs] using squeezeMid_idem (m :: us)

@[simp] theorem squeezeOuter_idem : ∀ ts : List Tree, squeezeOuter (squeezeOuter ts) = squeezeOuter ts
  | [] => rfl
  | t :: ts => by simp [squeezeOuter, squeezeMid_idem]

theorem primInner_eq_of_normalized_long
    {t m : Tree} {us : List Tree}
    (hchild : primChildrenRaw (t :: m :: us) = t :: m :: us)
    (hsq : squeezeOuter (t :: m :: us) = t :: m :: us) :
    primInner (.node (t :: m :: us)) = .node (t :: m :: us) := by
  simp [contractRoot, hchild, hsq]

theorem primInner_contractRoot_of_normalized
    {ts : List Tree}
    (hchild : primChildrenRaw ts = ts)
    (hsq : squeezeOuter ts = ts) :
    primInner (.node (contractRoot ts)) = .node (contractRoot ts) := by
  cases ts with
  | nil => simpa [contractRoot] using primInner_leaf
  | cons t ts =>
      cases ts with
      | nil =>
          cases t with
          | node cs =>
              cases cs with
              | nil => simpa [contractRoot, leaf] using primInner_singleton_leaf
              | cons c cs =>
                  have hprim : primInner (.node (c :: cs)) = .node (c :: cs) := by
                    simpa using hchild
                  simp [contractRoot, hprim]
      | cons m us =>
          simpa [contractRoot] using primInner_eq_of_normalized_long hchild hsq

mutual
  @[simp] theorem primInner_idem : ∀ x : Tree, primInner (primInner x) = primInner x
    | .node ts => by
        let zs := primList ts
        have hchild : primChildrenRaw zs = zs := by
          calc
            primChildrenRaw zs = primChildrenRaw (primList ts) := by simp [zs]
            _ = primChildrenRaw (squeezeOuter (primChildrenRaw ts)) := by simp
            _ = squeezeOuter (primChildrenRaw (primChildrenRaw ts)) := by rw [primChildrenRaw_squeezeOuter]
            _ = squeezeOuter (primChildrenRaw ts) := by simp [primChildrenRaw_idem]
            _ = primList ts := by simp
            _ = zs := by simp [zs]
        have hsq : squeezeOuter zs = zs := by
          calc
            squeezeOuter zs = squeezeOuter (primList ts) := by simp [zs]
            _ = squeezeOuter (squeezeOuter (primChildrenRaw ts)) := by simp
            _ = squeezeOuter (primChildrenRaw ts) := squeezeOuter_idem (primChildrenRaw ts)
            _ = primList ts := by simp
            _ = zs := by simp [zs]
        calc
          primInner (primInner (.node ts)) = primInner (.node (contractRoot zs)) := by
            simp [zs]
          _ = .node (contractRoot zs) := primInner_contractRoot_of_normalized hchild hsq
          _ = primInner (.node ts) := by simp [zs]

  @[simp] theorem primChildrenRaw_idem : ∀ ts : List Tree,
      primChildrenRaw (primChildrenRaw ts) = primChildrenRaw ts
    | [] => by simp
    | t :: ts => by simp [primInner_idem t, primChildrenRaw_idem ts]
end

@[simp] theorem primList_idem (ts : List Tree) : primList (primList ts) = primList ts := by
  calc
    primList (primList ts) = squeezeOuter (primChildrenRaw (primList ts)) := by simp
    _ = squeezeOuter (primChildrenRaw (squeezeOuter (primChildrenRaw ts))) := by simp
    _ = squeezeOuter (squeezeOuter (primChildrenRaw (primChildrenRaw ts))) := by rw [primChildrenRaw_squeezeOuter]
    _ = squeezeOuter (squeezeOuter (primChildrenRaw ts)) := by simp [primChildrenRaw_idem]
    _ = squeezeOuter (primChildrenRaw ts) := squeezeOuter_idem (primChildrenRaw ts)
    _ = primList ts := by simp

@[simp] theorem prim_idem : ∀ x : Tree, prim (prim x) = prim x
  | .node ts => by simp [prim]

@[simp] theorem Prim_prim (x : Tree) : Prim (prim x) := by
  simp [Prim]

theorem primChildrenRaw_append (xs ys : List Tree) :
    primChildrenRaw (xs ++ ys) = primChildrenRaw xs ++ primChildrenRaw ys := by
  induction xs <;> aesop

@[simp] theorem r_eq_leaf_iff {x : Tree} : r x = leaf ↔ x = leaf := by
  constructor <;> intro h;
  · rw [ ← r_involutive x, h, r_leaf ];
  · aesop

theorem rList_length (ts : List Tree) : (rList ts).length = ts.length := by
  induction' ts with t ts ih <;> simp [rList, *]

@[simp] theorem rList_singleton (t : Tree) : rList [t] = [r t] := by
  unfold rList; aesop;

def isNonLeaf : Tree → Bool
  | .node [] => false
  | .node (_ :: _) => true

@[simp] theorem isNonLeaf_leaf : isNonLeaf leaf = false := rfl
@[simp] theorem isNonLeaf_node_cons (c : Tree) (cs : List Tree) :
    isNonLeaf (.node (c :: cs)) = true := rfl

@[simp] theorem isNonLeaf_r (x : Tree) : isNonLeaf (r x) = isNonLeaf x := by
  cases' x with ts;
  have h_isNonLeaf : ∀ (ts : List Tree), isNonLeaf (.node ts) = (ts ≠ []) := by
    intro ts; cases ts <;> simp +decide ;
  by_cases h : ts = [] <;> simp_all +decide;
  have h_rList_nonempty : ∀ (ts : List Tree), ts ≠ [] → rList ts ≠ [] := by
    intro ts hts; induction ts <;> simp_all +decide [ rList ] ;
  grind

theorem squeezeMid_append_singleton (xs : List Tree) (t : Tree) :
    squeezeMid (xs ++ [t]) = xs.filter (fun x => isNonLeaf x) ++ [t] := by
  nontriviality;
  rename_i h;
  obtain ⟨ x, y, hxy ⟩ := h;
  revert x y;
  intros x y hxy
  induction' xs with x xs ih generalizing t;
  · cases t ; trivial;
  · cases xs <;> simp_all +decide [ List.filter_cons ];
    · cases x ; simp_all +decide [ squeezeMid ];
      cases ‹List Tree› <;> simp +decide [ Tree.isNonLeaf ];
    · cases x ; simp_all +decide [ squeezeMid ];
      cases ‹List Tree› <;> simp_all +decide [ isNonLeaf ]

@[simp] theorem squeezeMid_singleton (t : Tree) : squeezeMid [t] = [t] := by
  convert squeezeMid_append_singleton [] t using 1

theorem filter_isNonLeaf_rList (xs : List Tree) :
    (rList xs).filter (fun x => isNonLeaf x) = rList (xs.filter (fun x => isNonLeaf x)) := by
  induction' xs using List.reverseRecOn with xs x ih;
  · rfl;
  · by_cases h : isNonLeaf x <;> simp_all +decide

theorem squeezeOuter_rList (ts : List Tree) :
    squeezeOuter (rList ts) = rList (squeezeOuter ts) := by
  induction' ts with t ts ih;
  · rfl;
  · obtain ⟨last, middle, h⟩ : ∃ last middle, ts = middle ++ [last] ∨ ts = [] := by
      exact if h : ts = [] then ⟨ t, [ ], Or.inr h ⟩ else ⟨ ts.getLast ( by simpa using h ), ts.dropLast, Or.inl ( by rw [ List.dropLast_append_getLast ( by simpa using h ) ] ) ⟩;
    rcases h with ( rfl | rfl ) <;> simp_all +decide [ rList, squeezeOuter ];
    · rw [ squeezeMid_append_singleton, squeezeMid_append_singleton ];
      simp +decide [ rList_append, filter_isNonLeaf_rList ];
    · rfl

theorem contractRoot_rList (ts : List Tree) :
    contractRoot (rList ts) = rList (contractRoot ts) := by
  rcases ts with ( _ | ⟨ t, _ | ⟨ m, us ⟩ ⟩ );
  · rfl;
  · unfold contractRoot;
    cases t;
    cases ‹List Tree› <;> simp +decide [ *, rList ];
    cases h : rList ‹_› <;> aesop;
  · have h_contractRoot : ∀ (ts : List Tree), 2 ≤ ts.length → contractRoot ts = ts := by
      intros ts hts
      induction' ts with t ts ih;
      · contradiction;
      · cases ts <;> simp_all +decide [ contractRoot ];
    simp_all +decide [ rList ]

mutual
  theorem primInner_r : ∀ x : Tree, primInner (r x) = r (primInner x)
    | .node ts => by
        have h_ind : ∀ xs : List Tree, primChildrenRaw (rList xs) = rList (primChildrenRaw xs) := by
          intro xs; induction xs <;> simp_all +decide [ rList ] ;
          have h_split : ∀ (ts : List Tree) (t : Tree), primChildrenRaw (ts ++ [t]) = primChildrenRaw ts ++ [primInner t] := by
            intros ts t; induction ts <;> simp_all +decide;
          induction ‹Tree› using Tree.recOn ; simp_all +decide;
          rw [ ‹primChildrenRaw ( rList _ ) = rList ( primChildrenRaw _ ) › ];
          rw [ squeezeOuter_rList, contractRoot_rList ];
          · aesop;
          · simp_all +decide [ rList ];
        simp +decide [ h_ind, squeezeOuter_rList, contractRoot_rList ]

  theorem primChildrenRaw_rList : ∀ ts : List Tree,
      primChildrenRaw (rList ts) = rList (primChildrenRaw ts)
    | [] => by simp [rList]
    | t :: ts => by
        have h_primInner_r : ∀ t : Tree, primInner (r t) = r (primInner t) := by
          intro t;
          induction' t using Tree.recOn with t ih;
          simp +zetaDelta at *;
          convert contractRoot_rList _ using 1;
          rw [ show primChildrenRaw ( rList t ) = rList ( primChildrenRaw t ) from ?_ ];
          rw [ squeezeOuter_rList ];
          bv_omega;
          · aesop;
          · simp_all +decide [ rList ];
            rw [ primChildrenRaw_append, ‹primChildrenRaw ( rList _ ) = rList ( primChildrenRaw _ ) › ];
            aesop;
        convert primChildrenRaw_append ( rList ts ) [ r t ] using 1;
        induction' ts with t' ts ih generalizing t <;> simp_all +decide;
        simp_all +decide [ rList ];
        rw [ ih, primChildrenRaw_append ] ; aesop;
        exact t
end

theorem primList_rList (ts : List Tree) :
    primList (rList ts) = rList (primList ts) := by
  simp only [primList_eq]
  rw [primChildrenRaw_rList, squeezeOuter_rList]

@[simp] theorem prim_r (x : Tree) : prim (r x) = r (prim x) := by
  cases x with
  | node ts =>
      simp only [prim_node, r_node]
      exact congrArg Tree.node (primList_rList ts)

theorem contractRoot_tList_squeezeOuter (bs : List Tree) :
    contractRoot (tList (squeezeOuter bs)) = tList (squeezeMid bs) := by
  unfold squeezeOuter;
  rcases bs with ( _ | ⟨ x, _ | ⟨ y, ys ⟩ ⟩ ) <;> simp +decide [ *, squeezeMid ];
  · cases x ; simp +decide [ *, tList ];
    cases h : tList ‹_› <;> simp_all +decide [ contractRoot ];
  · rcases x with ( _ | ⟨ _ | x ⟩ ) <;> simp +decide [ * ];
    · cases h : squeezeMid ( y :: ys ) <;> simp_all +decide [ tList ];
      · exact absurd h ( by exact ne_of_apply_ne List.length ( by simp +arith +decide [ squeezeMid_ne_nil_of_cons ] ) );
      · cases h' : tList ( ‹_› :: ‹_› ) <;> simp_all +decide [ contractRoot ];
        cases ‹Tree›; cases ‹List Tree› <;> simp_all +decide [ tList ];
    · cases h : squeezeMid ( y :: ys ) <;> simp_all +decide [ tList ];
      · cases squeezeMid_ne_nil_of_cons y ys h;
      · unfold contractRoot; aesop;
    · unfold contractRoot;
      cases h : squeezeMid ( y :: ys ) <;> simp_all +decide [ tList ]

theorem squeezeMid_of_squeezeOuter_eq_tList {b : List Tree} {Q : List Tree}
    (h : squeezeOuter b = tList Q) : squeezeMid b = tList (contractRoot Q) := by
  by_contra h_contra;
  exact h_contra ( by have := contractRoot_tList_squeezeOuter b; aesop )

mutual
  @[simp] theorem prim_t : ∀ x : Tree, prim (t x) = t (prim x)
    | .node ts => by
        simp only [prim_node, t_node]
        exact congrArg Tree.node (primList_tList ts)

  theorem primList_tList : ∀ ts : List Tree,
      primList (tList ts) = tList (primList ts)
    | [] => by simp [squeezeOuter]
    | .node cs :: ts => by
        have ih_ts : primList (tList ts) = tList (primList ts) := primList_tList ts
        have ih_cs : primList (tList cs) = tList (primList cs) := by
          have h := prim_t (.node cs)
          simp only [prim_node, t_node] at h
          exact Tree.node.inj h
        simp only [tList]
        simp only [primList_eq, primChildrenRaw_cons, primInner_node]
        have eq_ts : squeezeOuter (primChildrenRaw (tList ts)) = tList (squeezeOuter (primChildrenRaw ts)) := by
          rw [← primList_eq, ← primList_eq]; exact ih_ts
        rw [eq_ts, contractRoot_tList_squeezeOuter]
        conv_lhs => rw [squeezeOuter]
        conv_rhs => rw [squeezeOuter, tList]
        congr 1
        rw [← primList_eq]
        exact squeezeMid_of_squeezeOuter_eq_tList (by rw [← primList_eq]; exact ih_cs)
end

@[simp] theorem prim_m (x : Tree) : prim (m x) = m (prim x) := by
  simp [m]

theorem Prim_m (x : Tree) (h : Prim x) : Prim (m x) := by
  unfold Prim at *; rw [prim_m, h]

theorem Prim_r (x : Tree) (h : Prim x) : Prim (r x) := by
  unfold Prim at *; rw [prim_r, h]

theorem Prim_t (x : Tree) (h : Prim x) : Prim (t x) := by
  unfold Prim at *; rw [prim_t, h]

end Tree
end Primitive
