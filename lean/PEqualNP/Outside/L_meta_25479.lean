import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25479_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma stepF_length (w : List Bool) (g : Gate) : (stepF w g).length = w.length + 1 := by
  simp [stepF]

lemma fold_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, stepF_length, List.length_cons]
    omega

lemma fold_low (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepF w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepF w g) i (by rw [stepF_length]; omega)]
    simp only [stepF]
    rw [List.getD_append _ _ _ _ hi]

lemma fold_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ gs[j].inputs, i < w.length + j) →
    (gs.foldl stepF w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepF w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hin
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hin ⊢
      rw [fold_low gs (stepF w g) w.length (by rw [stepF_length]; omega)]
      have h1 : (stepF w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepF]
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt := hin i hi
      rw [fold_low gs (stepF w g) i (by rw [stepF_length]; omega)]
      simp only [stepF]
      rw [List.getD_append _ _ _ _ hlt]
    | succ j =>
      simp only [List.getElem_cons_succ] at hin ⊢
      have h := ih (stepF w g) j (by simpa using hj)
        (by intro i hi; have := hin i hi; rw [stepF_length]; omega)
      rw [stepF_length] at h
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      rw [e]
      exact h

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

lemma wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_low _ _ _ hi

lemma wires_high (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  rw [wires_length]
  exact hi

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getElem?_eq_getElem hj]

lemma wires_gate (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  subst hx
  apply fold_gate
  intro i hi
  have h := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
  exact h

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold oneEach
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h2 : ¬ i = n + v.val := by omega
    simp [h2, Fin.ext_iff]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      simp [h3, Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      have h4 : ¬ i = n + v.val := by omega
      simp [h3, h4]


lemma reader_unique (C : Circuit) (w j1 j2 : ℕ) (h : readsIn C (Finset.range C.size) w = 1)
    (h1 : j1 < C.gates.length) (h2 : j2 < C.gates.length)
    (m1 : w ∈ (C.gates[j1]).inputs) (m2 : w ∈ (C.gates[j2]).inputs) : j1 = j2 := by
  by_contra hne
  have c1 : 0 < (gateAt C j1).inputs.count w := by
    rw [gateAt_eq C j1 h1]; exact List.count_pos_iff.mpr m1
  have c2 : 0 < (gateAt C j2).inputs.count w := by
    rw [gateAt_eq C j2 h2]; exact List.count_pos_iff.mpr m2
  have hsub : ({j1, j2} : Finset ℕ) ⊆ Finset.range C.size := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_range.mpr h1
    · exact Finset.mem_range.mpr h2
  have hle : ∑ j ∈ ({j1, j2} : Finset ℕ), (gateAt C j).inputs.count w ≤
      ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count w :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at hle
  unfold readsIn at h
  omega

lemma or_pair_true (g : Gate) (f : ℕ → Bool) (p q : ℕ) (hop : g.op = GateOp.or)
    (hin : g.inputs = [p, q] ∨ g.inputs = [q, p]) (hf : f p = true ∨ f q = true) :
    g.op.eval (g.inputs.map f) = true := by
  rw [hop]
  rcases hin with e | e <;> rcases hf with t | t <;> simp [e, t, GateOp.eval]

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (u u' : Fin n) (b b' : Fin m)
    (hu : u ≠ u') (hb : b ≠ b') (hRB : ReadsBack (n + m) C) (hRep : Represents G C)
    (hp1 : ∃ g ∈ C.gates, g.op = GateOp.or ∧
      (g.inputs = [u.val, n + b.val] ∨ g.inputs = [n + b.val, u.val]))
    (hp2 : ∃ g ∈ C.gates, g.op = GateOp.or ∧
      (g.inputs = [u'.val, n + b'.val] ∨ g.inputs = [n + b'.val, u'.val]))
    (hreads : ∀ w ∈ [u.val, u'.val, n + b.val, n + b'.val],
      readsIn C (Finset.range C.size) w = 1)
    (hout : C.output ∉ [u.val, u'.val, n + b.val, n + b'.val]) :
    G u b' = G u' b := by
  obtain ⟨g1, g1mem, g1op, g1in⟩ := hp1
  obtain ⟨g2, g2mem, g2op, g2in⟩ := hp2
  obtain ⟨j1, hj1, rfl⟩ := List.getElem_of_mem g1mem
  obtain ⟨j2, hj2, rfl⟩ := List.getElem_of_mem g2mem
  have hx : u.val ∈ (C.gates[j1]).inputs := by rcases g1in with e | e <;> simp [e]
  have hy : n + b.val ∈ (C.gates[j1]).inputs := by rcases g1in with e | e <;> simp [e]
  have hx' : u'.val ∈ (C.gates[j2]).inputs := by rcases g2in with e | e <;> simp [e]
  have hy' : n + b'.val ∈ (C.gates[j2]).inputs := by rcases g2in with e | e <;> simp [e]
  have L1 : (oneEach u b').length = n + m := oneEach_length u b'
  have L2 : (oneEach u' b).length = n + m := oneEach_length u' b
  have key : ∀ k w : ℕ, w < k → w ∉ [u.val, u'.val, n + b.val, n + b'.val] →
      (C.wires (oneEach u b')).getD w false = (C.wires (oneEach u' b)).getD w false := by
    intro k
    induction k with
    | zero => intro w hw; omega
    | succ k ih =>
      intro w hw hnot
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
      obtain ⟨n1, n2, n3, n4⟩ := hnot
      by_cases hlow : w < n + m
      · rw [wires_low C _ w (by rw [L1]; exact hlow), wires_low C _ w (by rw [L2]; exact hlow),
          oneEach_getD, oneEach_getD]
        simp [n1, n2, n3, n4]
      · by_cases hhigh : n + m + C.gates.length ≤ w
        · rw [wires_high C _ w (by rw [L1]; exact hhigh), wires_high C _ w (by rw [L2]; exact hhigh)]
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
          have hj : j < C.gates.length := by omega
          rw [wires_gate (n + m) C hRB _ L1 j hj, wires_gate (n + m) C hRB _ L2 j hj]
          by_cases hall : ∀ i ∈ (C.gates[j]).inputs, i ∉ [u.val, u'.val, n + b.val, n + b'.val]
          · congr 1
            apply List.map_congr_left
            intro i hi
            have hlt := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
            exact ih i (by omega) (hall i hi)
          · push_neg at hall
            obtain ⟨i, hi, hfour⟩ := hall
            have hread := hreads i hfour
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hfour
            have hx1 : (C.wires (oneEach u b')).getD u.val false = true := by
              rw [wires_low C _ _ (by rw [L1]; omega), oneEach_getD]; simp
            have hy1 : (C.wires (oneEach u b')).getD (n + b'.val) false = true := by
              rw [wires_low C _ _ (by rw [L1]; omega), oneEach_getD]; simp
            have hx2 : (C.wires (oneEach u' b)).getD u'.val false = true := by
              rw [wires_low C _ _ (by rw [L2]; omega), oneEach_getD]; simp
            have hy2 : (C.wires (oneEach u' b)).getD (n + b.val) false = true := by
              rw [wires_low C _ _ (by rw [L2]; omega), oneEach_getD]; simp
            have hjj : j = j1 ∨ j = j2 := by
              rcases hfour with rfl | rfl | rfl | rfl
              · exact Or.inl (reader_unique C _ j j1 hread hj hj1 hi hx)
              · exact Or.inr (reader_unique C _ j j2 hread hj hj2 hi hx')
              · exact Or.inl (reader_unique C _ j j1 hread hj hj1 hi hy)
              · exact Or.inr (reader_unique C _ j j2 hread hj hj2 hi hy')
            rcases hjj with rfl | rfl
            · rw [or_pair_true _ _ _ _ g1op g1in (Or.inl hx1),
                or_pair_true _ _ _ _ g1op g1in (Or.inr hy2)]
            · rw [or_pair_true _ _ _ _ g2op g2in (Or.inr hy1),
                or_pair_true _ _ _ _ g2op g2in (Or.inl hx2)]
  have e := key (C.output + 1) C.output (by omega) hout
  have r1 := hRep u b'
  have r2 := hRep u' b
  unfold Circuit.eval at r1 r2
  rw [← r1, ← r2]
  exact e

end PEqualNP.Outside.L_meta_25479_aux

theorem PEqualNP.Outside.L_meta_25479 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (u u' : Fin n) (b b' : Fin m),
  let x := u.val
  let x' := u'.val
  let y := n + b.val
  let y' := n + b'.val
  let paired := fun (r c : ℕ) =>
    ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (g.inputs = [r, c] ∨ g.inputs = [c, r])
  u ≠ u' → b ≠ b' →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  paired x y → paired x' y' →
  (∀ w ∈ [x, x', y, y'],
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1) →
  C.output ∉ [x, x', y, y'] →
  G u b' = G u' b) := by
  intro n m G C u u' b b'
  exact PEqualNP.Outside.L_meta_25479_aux.main n m G C u u' b b'
