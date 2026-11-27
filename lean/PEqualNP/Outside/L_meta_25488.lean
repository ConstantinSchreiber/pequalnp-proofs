import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25488_aux

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


lemma colOnly_length (n : ℕ) {m : ℕ} (v : Fin m) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).length = n + m := by
  simp

lemma colOnly_getD (n : ℕ) {m : ℕ} (v : Fin m) (i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD i false =
      decide (i = n + v.val) := by
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h3 : ¬ i = n + v.val := by omega
    simp [h3]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp [Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = n + v.val := by omega
      simp [h3]

lemma mono (N : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ k w : ℕ, w < k → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro k
  induction k with
  | zero => intro w hw; omega
  | succ k ih =>
    intro w hw hval
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow)] at hval
      rw [wires_low C _ w (by rw [hy]; exact hlow)]
      exact hxy w hval
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh)] at hval
        exact absurd hval (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [wires_gate N C hRB _ hx j hj] at hval
        rw [wires_gate N C hRB _ hy j hj]
        have hlt : ∀ i ∈ (C.gates[j]).inputs, i < N + j := by
          intro i hi
          exact hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
        rcases hAO (C.gates[j]) (List.getElem_mem hj) with hop | hop
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, id_eq] at hval ⊢
          intro i hi
          exact ih i (by have := hlt i hi; omega) (hval i hi)
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
            id_eq] at hval ⊢
          obtain ⟨i, hi, hv⟩ := hval
          exact ⟨i, hi, ih i (by have := hlt i hi; omega) hv⟩

lemma reader_unique (C : Circuit) (w j1 j2 : ℕ)
    (h : readsIn C (Finset.range C.gates.length) w = 1)
    (h1 : j1 < C.gates.length) (h2 : j2 < C.gates.length)
    (m1 : w ∈ (C.gates[j1]).inputs) (m2 : w ∈ (C.gates[j2]).inputs) : j1 = j2 := by
  by_contra hne
  have c1 : 0 < (gateAt C j1).inputs.count w := by
    rw [gateAt_eq C j1 h1]; exact List.count_pos_iff.mpr m1
  have c2 : 0 < (gateAt C j2).inputs.count w := by
    rw [gateAt_eq C j2 h2]; exact List.count_pos_iff.mpr m2
  have hsub : ({j1, j2} : Finset ℕ) ⊆ Finset.range C.gates.length := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_range.mpr h1
    · exact Finset.mem_range.mpr h2
  have hle : ∑ j ∈ ({j1, j2} : Finset ℕ), (gateAt C j).inputs.count w ≤
      ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hne] at hle
  unfold readsIn at h
  omega

lemma and_pair (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.and)
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    g.op.eval (g.inputs.map f) = (f a && f b) := by
  rw [hop]
  rcases hin with e | e
  · simp [e, GateOp.eval]
  · simp [e, GateOp.eval, Bool.and_comm]

lemma or_pair (g : Gate) (f : ℕ → Bool) (a b : ℕ) (hop : g.op = GateOp.or)
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) :
    g.op.eval (g.inputs.map f) = (f a || f b) := by
  rw [hop]
  rcases hin with e | e
  · simp [e, GateOp.eval]
  · simp [e, GateOp.eval, Bool.or_comm]

lemma agree (N : ℕ) (C : Circuit) (hRB : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (S : ℕ → Prop) (B : ℕ)
    (hin : ∀ w, w < N → ¬ S w → x.getD w false = y.getD w false)
    (hgate : ∀ k (hk : k < C.gates.length), N + k < B → ¬ S (N + k) →
      (∀ a ∈ (C.gates[k]).inputs, ¬ S a) ∨
        (C.wires x).getD (N + k) false = (C.wires y).getD (N + k) false) :
    ∀ w, w < B → ¬ S w → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hS
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow), wires_low C _ w (by rw [hy]; exact hlow)]
      exact hin w hlow hS
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh), wires_high C _ w (by rw [hy]; exact hhigh)]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hgate k hk hwB hS with hall | heq
        · rw [wires_gate N C hRB _ hx k hk, wires_gate N C hRB _ hy k hk]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
          exact ih a (by omega) (by omega) (hall a ha)
        · exact heq

lemma both_length {n m : ℕ} (u v : Fin n) (c : Fin m) : (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))).length = n + m := by
  simp

lemma both_getD {n m : ℕ} (u v : Fin n) (c : Fin m) (w : ℕ) :
    (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))).getD w false = (decide (w = u.val) || decide (w = v.val) || decide (w = n + c.val)) := by
  by_cases h1 : w < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    have h2 : ¬ w = n + c.val := by omega
    simp [h2, Fin.ext_iff]
  · by_cases h2 : w < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have h3 : ¬ w = u.val := by omega
      have h4 : ¬ w = v.val := by omega
      simp [h3, h4, Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ w = u.val := by omega
      have h4 : ¬ w = v.val := by omega
      have h5 : ¬ w = n + c.val := by omega
      simp [h3, h4, h5]

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (u v : Fin n) (c : Fin m)
    (i j : Fin C.gates.length) (p q : ℕ)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (huv : u ≠ v)
    (hi : (gateAt C i.val).op = GateOp.or ∧
      ((gateAt C i.val).inputs = [u.val, p] ∨ (gateAt C i.val).inputs = [p, u.val]))
    (hj : (gateAt C j.val).op = GateOp.or ∧
      ((gateAt C j.val).inputs = [v.val, q] ∨ (gateAt C j.val).inputs = [q, v.val]))
    (ru : readsIn C (Finset.range C.gates.length) u.val = 1)
    (hout : C.output ∉ [u.val, n + m + i.val]) (huc : G u c = true) (hvc : G v c = false) :
    (C.wires (oneEach v c)).getD (n + m + i.val) false = false ∧
      ∀ t : Fin C.gates.length,
        ((gateAt C t.val).op = GateOp.or ∧
          ((gateAt C t.val).inputs = [n + m + i.val, n + m + j.val] ∨
            (gateAt C t.val).inputs = [n + m + j.val, n + m + i.val])) →
        ∃ h : Fin C.gates.length, h ≠ t ∧ n + m + i.val ∈ (gateAt C h.val).inputs := by
  rw [gateAt_eq C i.val i.isLt] at hi
  rw [gateAt_eq C j.val j.isLt] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
  obtain ⟨hou, hoi⟩ := hout
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have L4 : (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))).length = n + m := both_length u v c
  have L2 : (oneEach v c).length = n + m := oneEach_length v c
  have L1 : (oneEach u c).length = n + m := oneEach_length u c
  have mu : u.val ∈ (C.gates[i.val]).inputs := by rcases hi.2 with e | e <;> simp [e]
  have huvv : ¬ u.val = v.val := fun e => huv (Fin.ext e)
  have o2 : (C.wires (oneEach v c)).getD C.output false = false := by
    have h := hRep v c
    unfold Circuit.eval at h
    rw [h, hvc]
  have o1 : (C.wires (oneEach u c)).getD C.output false = true := by
    have h := hRep u c
    unfold Circuit.eval at h
    rw [h, huc]
  have o4 : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD C.output false = true :=
    mono (n + m) C hAO hRB (oneEach u c) (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))) L1 L4
      (by
        intro a ha
        rw [oneEach_getD] at ha
        rw [both_getD]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at ha ⊢
        rcases ha with e | e
        · exact Or.inl (Or.inl e)
        · exact Or.inr e) (C.output + 1) C.output (by omega) o1
  have u4 : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD u.val false = true := by
    rw [wires_low C _ _ (by rw [L4]; omega), both_getD]
    simp
  have I4 : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD (n + m + i.val) false = true := by
    rw [wires_gate (n + m) C hRB _ L4 i.val i.isLt, or_pair _ _ _ _ hi.1 hi.2, u4]
    simp
  have hin : ∀ w, w < n + m → ¬ w = u.val → (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))).getD w false = (oneEach v c).getD w false := by
    intro w _ h3
    rw [both_getD, oneEach_getD]
    simp [h3]
  constructor
  · by_contra hne
    have hI2 : (C.wires (oneEach v c)).getD (n + m + i.val) false = true := by simpa using hne
    have hA := agree (n + m) C hRB (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))) (oneEach v c) L4 L2 (fun w => w = u.val) (C.output + 1)
      (by
        intro w hw hS
        exact hin w hw hS)
      (by
        intro k hk _ _
        by_cases hki : k = i.val
        · right
          rw [hki, I4, hI2]
        · left
          intro a ha e
          have e' : a = u.val := e
          rw [e'] at ha
          exact hki (reader_unique C _ k i.val ru hk i.isLt ha mu))
      C.output (by omega) hou
    rw [o4, o2] at hA
    exact absurd hA (by simp)
  · intro t ht
    rw [gateAt_eq C t.val t.isLt] at ht
    by_contra hno
    have hno' : ∀ k (hk : k < C.gates.length), k ≠ t.val →
        n + m + i.val ∉ (C.gates[k]).inputs := by
      intro k hk hkt hmem
      exact hno ⟨⟨k, hk⟩, fun e => hkt (congrArg Fin.val e), by
        rw [gateAt_eq C k hk]; exact hmem⟩
    have v4 : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD v.val false = true := by
      rw [wires_low C _ _ (by rw [L4]; omega), both_getD]
      simp
    have v2 : (C.wires (oneEach v c)).getD v.val false = true := by
      rw [wires_low C _ _ (by rw [L2]; omega), oneEach_getD]
      simp
    have J4 : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD (n + m + j.val) false = true := by
      rw [wires_gate (n + m) C hRB _ L4 j.val j.isLt, or_pair _ _ _ _ hj.1 hj.2, v4]
      simp
    have J2 : (C.wires (oneEach v c)).getD (n + m + j.val) false = true := by
      rw [wires_gate (n + m) C hRB _ L2 j.val j.isLt, or_pair _ _ _ _ hj.1 hj.2, v2]
      simp
    have hP : (C.wires (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c)))).getD (n + m + t.val) false =
        (C.wires (oneEach v c)).getD (n + m + t.val) false := by
      rw [wires_gate (n + m) C hRB _ L4 t.val t.isLt, or_pair _ _ _ _ ht.1 ht.2,
        wires_gate (n + m) C hRB _ L2 t.val t.isLt, or_pair _ _ _ _ ht.1 ht.2, J4, J2]
      simp
    have hA := agree (n + m) C hRB (List.ofFn (fun r : Fin n => decide (r = u) || decide (r = v)) ++ List.ofFn (fun col : Fin m => decide (col = c))) (oneEach v c) L4 L2
      (fun w => w = u.val ∨ w = n + m + i.val) (C.output + 1)
      (by
        intro w hw hS
        exact hin w hw (fun e => hS (Or.inl e)))
      (by
        intro k hk _ hS
        by_cases hkt : k = t.val
        · right
          rw [hkt]
          exact hP
        · left
          intro a ha hSa
          rcases hSa with e | e
          · rw [e] at ha
            have h := reader_unique C _ k i.val ru hk i.isLt ha mu
            exact hS (Or.inr (by rw [h]))
          · rw [e] at ha
            exact hno' k hk hkt ha)
      C.output (by omega) (by
        intro h
        rcases h with e | e
        · exact hou e
        · exact hoi e)
    rw [o4, o2] at hA
    exact absurd hA (by simp)

end PEqualNP.Outside.L_meta_25488_aux

theorem PEqualNP.Outside.L_meta_25488 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n) (c : Fin m)
    (i j : Fin C.gates.length) (p q : ℕ),
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let isOr := fun (z : Fin C.gates.length) (a b : ℕ) =>
    (g z.val).op = .or ∧ ((g z.val).inputs = [a, b] ∨ (g z.val).inputs = [b, a])
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v → i ≠ j → isOr i u.val p → isOr j v.val q →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ∉ [u.val, wire i] → G u c = true → G v c = false →
  (C.wires (PEqualNP.Represents.oneEach v c)).getD (wire i) false = false ∧
    ∀ t : Fin C.gates.length, isOr t (wire i) (wire j) →
      ∃ h : Fin C.gates.length, h ≠ t ∧ wire i ∈ (g h.val).inputs) := by
  intro n m G C u v c i j p q g wire isOr hM hRB hRep huv _ hi hj ru hout huc hvc
  exact PEqualNP.Outside.L_meta_25488_aux.main n m G C u v c i j p q hM hRB hRep huv hi hj ru hout huc hvc
