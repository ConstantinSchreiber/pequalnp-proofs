import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25491

namespace PEqualNP.Outside.L_meta_25529_aux

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

lemma bad_input (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h1 : g.op.eval (g.inputs.map f) = true) (h2 : g.op.eval (g.inputs.map f') = false) :
    ∃ i ∈ g.inputs, f i = true ∧ f' i = false := by
  by_contra hne
  have hall : ∀ i ∈ g.inputs, f i = true → f' i = true := by
    intro i hi hf
    by_contra hf'
    exact hne ⟨i, hi, hf, by simpa using hf'⟩
  have ht : g.op.eval (g.inputs.map f') = true := by
    rcases hop with hop | hop
    · rw [hop] at h1 ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, id_eq] at h1 ⊢
      intro i hi
      exact hall i hi (h1 i hi)
    · rw [hop] at h1 ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
        id_eq] at h1 ⊢
      obtain ⟨i, hi, hv⟩ := h1
      exact ⟨i, hi, hall i hi hv⟩
  rw [ht] at h2
  exact absurd h2 (by simp)

lemma dom (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (v w : Fin n) (iv : ℕ) (hiv : iv < C.gates.length)
    (rv : readsIn C (Finset.range C.gates.length) v.val = 1) (mv : v.val ∈ (C.gates[iv]).inputs)
    (hout : C.output ≠ v.val) (c : Fin m)
    (HI : (C.wires (oneEach w c)).getD (n + m + iv) false = true) :
    G v c = true → G w c = true := by
  intro hvc
  have L1 : (oneEach v c).length = n + m := oneEach_length v c
  have L2 : (oneEach w c).length = n + m := oneEach_length w c
  have key : ∀ t, t ≠ v.val → (C.wires (oneEach v c)).getD t false = true →
      (C.wires (oneEach w c)).getD t false = true := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htv h1
      by_cases hlow : t < n + m
      · rw [wires_low C _ t (by rw [L1]; exact hlow), oneEach_getD] at h1
        rw [wires_low C _ t (by rw [L2]; exact hlow), oneEach_getD]
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1 ⊢
        rcases h1 with e | e
        · exact absurd e htv
        · exact Or.inr e
      · by_cases hhigh : n + m + C.gates.length ≤ t
        · rw [wires_high C _ t (by rw [L1]; exact hhigh)] at h1
          exact absurd h1 (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, t = n + m + k := ⟨t - (n + m), by omega⟩
          have hk : k < C.gates.length := by omega
          by_cases hkv : k = iv
          · rw [hkv]
            exact HI
          · by_contra h2
            have h2' : (C.wires (oneEach w c)).getD (n + m + k) false = false := by simpa using h2
            rw [wires_gate (n + m) C hRB _ L1 k hk] at h1
            rw [wires_gate (n + m) C hRB _ L2 k hk] at h2'
            obtain ⟨a, ha, ha1, ha2⟩ :=
              bad_input _ (hAO (C.gates[k]) (List.getElem_mem hk)) _ _ h1 h2'
            have hlt : a < n + m + k := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
            have hav : a ≠ v.val := by
              intro e
              rw [e] at ha
              exact hkv (reader_unique C _ k iv rv hk hiv ha mv)
            rw [ih a hlt hav ha1] at ha2
            exact absurd ha2 (by simp)
  have r1 := hRep v c
  have r2 := hRep w c
  unfold Circuit.eval at r1 r2
  rw [← r2]
  exact key C.output hout (by rw [r1, hvc])

lemma mtrans (N : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (S : ℕ → Prop) (B : ℕ)
    (hin : ∀ w, w < N → ¬ S w → x.getD w false = true → y.getD w false = true)
    (hgate : ∀ k (hk : k < C.gates.length), N + k < B → ¬ S (N + k) →
      (∀ a ∈ (C.gates[k]).inputs, ¬ S a) ∨
        ((C.wires x).getD (N + k) false = true → (C.wires y).getD (N + k) false = true)) :
    ∀ w, w < B → ¬ S w → (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hS hval
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow)] at hval
      rw [wires_low C _ w (by rw [hy]; exact hlow)]
      exact hin w hlow hS hval
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh)] at hval
        exact absurd hval (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hgate k hk hwB hS with hall | himp
        · by_contra h2
          have h2' : (C.wires y).getD (N + k) false = false := by simpa using h2
          rw [wires_gate N C hRB _ hx k hk] at hval
          rw [wires_gate N C hRB _ hy k hk] at h2'
          obtain ⟨a, ha, ha1, ha2⟩ :=
            bad_input _ (hAO (C.gates[k]) (List.getElem_mem hk)) _ _ hval h2'
          have hlt : a < N + k := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
          rw [ih a hlt (by omega) (hall a ha) ha1] at ha2
          exact absurd ha2 (by simp)
        · exact himp hval

lemma dom1 (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (v : Fin n) (iv : ℕ) (hiv : iv < C.gates.length)
    (rv : readsIn C (Finset.range C.gates.length) v.val = 1) (mv : v.val ∈ (C.gates[iv]).inputs)
    (hout : C.output ≠ v.val) (c : Fin m) (y : List Bool) (hy : y.length = n + m)
    (hyc : y.getD (n + c.val) false = true)
    (HI : (C.wires y).getD (n + m + iv) false = true) :
    G v c = true → C.eval y = true := by
  intro hvc
  have L1 : (oneEach v c).length = n + m := oneEach_length v c
  have key := mtrans (n + m) C hAO hRB (oneEach v c) y L1 hy (fun t => t = v.val) (C.output + 1)
    (by
      intro w _ hS h1
      rw [oneEach_getD] at h1
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with e | e
      · exact absurd e hS
      · rw [e]; exact hyc)
    (by
      intro k hk _ _
      by_cases hkv : k = iv
      · right
        intro _
        rw [hkv]
        exact HI
      · left
        intro a ha e
        have e' : a = v.val := e
        rw [e'] at ha
        exact hkv (reader_unique C _ k iv rv hk hiv ha mv))
    C.output (by omega) hout
  have r1 := hRep v c
  unfold Circuit.eval at r1 ⊢
  exact key (by rw [r1, hvc])

lemma dom2 (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C) (u : Fin n) (iu : ℕ) (hiu : iu < C.gates.length)
    (ru : readsIn C (Finset.range C.gates.length) u.val = 1) (mu : u.val ∈ (C.gates[iu]).inputs)
    (hout : C.output ≠ u.val) (hout2 : C.output ≠ n + m + iu) (c : Fin m) (y : List Bool)
    (hy : y.length = n + m) (hyc : y.getD (n + c.val) false = true)
    (HT : ∀ k (hk : k < C.gates.length), n + m + iu ∈ (C.gates[k]).inputs →
      (C.wires (oneEach u c)).getD (n + m + k) false = true →
        (C.wires y).getD (n + m + k) false = true) :
    G u c = true → C.eval y = true := by
  intro huc
  have L1 : (oneEach u c).length = n + m := oneEach_length u c
  have key := mtrans (n + m) C hAO hRB (oneEach u c) y L1 hy
    (fun t => t = u.val ∨ t = n + m + iu) (C.output + 1)
    (by
      intro w _ hS h1
      rw [oneEach_getD] at h1
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with e | e
      · exact absurd (Or.inl e) hS
      · rw [e]; exact hyc)
    (by
      intro k hk _ hS
      by_cases hr : n + m + iu ∈ (C.gates[k]).inputs
      · right
        exact HT k hk hr
      · left
        intro a ha e
        rcases e with e | e
        · rw [e] at ha
          have hkk : k = iu := reader_unique C _ k iu ru hk hiu ha mu
          exact hS (Or.inr (by rw [hkk]))
        · rw [e] at ha
          exact hr ha)
    C.output (by omega) (by
      intro e
      rcases e with e | e
      · exact hout e
      · exact hout2 e)
  have r1 := hRep u c
  unfold Circuit.eval at r1 ⊢
  exact key (by rw [r1, huc])

lemma pair_of_mem (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at ha
  · simp at ha hb
    omega
  · simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · left; rfl
    · right; rfl
    · exact absurd rfl hab
  · simp at hl

lemma three_mem (l : List ℕ) (hl : l.length ≤ 2) (a b c : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hc : c ∈ l) : a = b ∨ a = c ∨ b = c := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at ha
  · simp at ha hb hc
    omega
  · simp at ha hb hc
    omega
  · simp at hl

lemma third (n : ℕ) (hn : 3 ≤ n) (u v : Fin n) : ∃ w : Fin n, w ≠ u ∧ w ≠ v := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases a : u.val ≠ 0 ∧ v.val ≠ 0
  · refine ⟨⟨0, by omega⟩, fun e => a.1 ?_, fun e => a.2 ?_⟩
    · rw [← e]
    · rw [← e]
  · by_cases b : u.val ≠ 1 ∧ v.val ≠ 1
    · refine ⟨⟨1, by omega⟩, fun e => b.1 ?_, fun e => b.2 ?_⟩
      · rw [← e]
      · rw [← e]
    · refine ⟨⟨2, by omega⟩, fun e => ?_, fun e => ?_⟩
      · have h2 : u.val = 2 := by rw [← e]
        omega
      · have h2 : v.val = 2 := by rw [← e]
        omega

lemma inc_of_tri (n m : ℕ) (G : Fin n → Fin m → Bool) (hn : 3 ≤ n)
    (htri : ∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) :
    ∀ u v : Fin n, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false := by
  intro u v huv
  obtain ⟨w, hwu, hwv⟩ := third n hn u v
  obtain ⟨c, h1, _, h3⟩ := htri u w v (fun e => hwu e.symm) huv hwv
  exact ⟨c, h1, h3⟩

lemma support (N : ℕ) (C : Circuit) (hRB : ReadsBack N C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ d k : ℕ, k + d = C.gates.length → ∃ A : Finset ℕ, A.card ≤ d + 1 ∧
      (∀ w ∈ A, w < N + k ∨ N + C.gates.length ≤ w) ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ w ∈ A, (C.wires x).getD w false = (C.wires y).getD w false) →
        (C.wires x).getD C.output false = (C.wires y).getD C.output false := by
  intro d
  induction d with
  | zero =>
    intro k hk
    refine ⟨{C.output}, by simp, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_singleton] at hw
      omega
    · intro x y _ _ h
      exact h C.output (Finset.mem_singleton_self _)
  | succ d ih =>
    intro k hk
    obtain ⟨A, hc, hb, hs⟩ := ih (k + 1) (by omega)
    have hk' : k < C.gates.length := by omega
    by_cases hmem : N + k ∈ A
    · refine ⟨A.erase (N + k) ∪ (C.gates[k]).inputs.toFinset, ?_, ?_, ?_⟩
      · have h1 := Finset.card_union_le (A.erase (N + k)) (C.gates[k]).inputs.toFinset
        have h2 := Finset.card_erase_of_mem hmem
        have h3 := List.toFinset_card_le (C.gates[k]).inputs
        have h4 := hlen _ (List.getElem_mem hk')
        have h5 : 0 < A.card := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      · intro w hw
        rcases Finset.mem_union.mp hw with h | h
        · have h1 := Finset.mem_erase.mp h
          have h2 := hb w h1.2
          have h3 := h1.1
          omega
        · left
          exact hRB k hk' w (by rw [gateAt_eq C k hk']; exact List.mem_toFinset.mp h)
      · intro x y hx hy h
        apply hs x y hx hy
        intro w hw
        by_cases e : w = N + k
        · rw [e, wires_gate N C hRB _ hx k hk', wires_gate N C hRB _ hy k hk']
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e, hw⟩))
    · refine ⟨A, by omega, ?_, hs⟩
      intro w hw
      have h2 := hb w hw
      have h3 : w ≠ N + k := fun e => hmem (e ▸ hw)
      omega

lemma support' (N : ℕ) (C : Circuit) (hRB : ReadsBack N C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ A : Finset ℕ, A.card ≤ C.gates.length + 1 ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ w ∈ A, w < N → x.getD w false = y.getD w false) → C.eval x = C.eval y := by
  obtain ⟨A, hc, hb, hs⟩ := support N C hRB hlen C.gates.length 0 (by omega)
  refine ⟨A, hc, ?_⟩
  intro x y hx hy h
  unfold Circuit.eval
  apply hs x y hx hy
  intro w hw
  rcases hb w hw with h1 | h1
  · rw [wires_low C _ w (by rw [hx]; omega), wires_low C _ w (by rw [hy]; omega)]
    exact h w hw (by omega)
  · rw [wires_high C _ w (by rw [hx]; exact h1), wires_high C _ w (by rw [hy]; exact h1)]

def inp (N : ℕ) (P : ℕ → Bool) : List Bool := (List.range N).map P

lemma inp_length (N : ℕ) (P : ℕ → Bool) : (inp N P).length = N := by simp [inp]

lemma inp_getD (N : ℕ) (P : ℕ → Bool) (i : ℕ) :
    (inp N P).getD i false = (decide (i < N) && P i) := by
  unfold inp
  by_cases h : i < N
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [h]

lemma irrel (N : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack N C) (A : Finset ℕ)
    (hA : ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ w ∈ A, w < N → x.getD w false = y.getD w false) → C.eval x = C.eval y)
    (i : ℕ) (hi : i ∉ A) (x z : List Bool) (hx : x.length = N) (hz : z.length = N)
    (h : ∀ w, w ≠ i → x.getD w false = true → z.getD w false = true) :
    C.eval x = true → C.eval z = true := by
  intro hev
  have e := hA x (inp N (fun w => decide (w ≠ i) && x.getD w false)) hx (inp_length _ _)
    (by
      intro w hw hwN
      have hwi : w ≠ i := fun e => hi (e ▸ hw)
      rw [inp_getD]
      simp [hwN, hwi])
  rw [e] at hev
  unfold Circuit.eval at hev ⊢
  exact mono N C hAO hRB _ z (inp_length _ _) hz
    (by
      intro w hw
      rw [inp_getD] at hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      exact h w hw.2.1 hw.2.2) (C.output + 1) C.output (by omega) hev

lemma two_rows (m : ℕ) (H : Fin 2 → Fin m → Bool) (c1 c2 c3 : Fin m)
    (h01 : H 0 c1 = true) (h11 : H 1 c1 = true) (h02 : H 0 c2 = true) (h12 : H 1 c2 = false)
    (h03 : H 0 c3 = false) (h13 : H 1 c3 = true) (t : ℕ) (hrep : RepSizeAtMost H t) :
    4 ≤ t := by
  obtain ⟨C0, hM0, hs0, hR0⟩ := hrep
  obtain ⟨C, hM, hRB, hsz, hRep⟩ :=
    PEqualNP.Outside.L_meta_25491_aux.same_rep 2 m H C0 hM0 hR0 ⟨0, c1, h01⟩ ⟨1, c2, h12⟩ ∅
      (by simp)
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  obtain ⟨A, hc, hA⟩ := support' (2 + m) C hRB (fun g hg => (hM g hg).2)
  have key : ∀ (i : ℕ), i ∉ A → ∀ (r r' : Fin 2) (c c' : Fin m),
      (∀ w, w ≠ i → (oneEach r c).getD w false = true → (oneEach r' c').getD w false = true) →
      H r c = true → H r' c' = true := by
    intro i hi r r' c c' h hrc
    rw [← hRep r c] at hrc
    rw [← hRep r' c']
    exact irrel (2 + m) C hAO hRB A hA i hi _ _ (oneEach_length r c) (oneEach_length r' c') h hrc
  have col : ∀ c : Fin m, 2 + c.val ∉ A → ∀ (r : Fin 2) (c' : Fin m),
      H r c = true → H r c' = true := by
    intro c hcA r c'
    refine key (2 + c.val) hcA r r c c' ?_
    intro w hw hval
    rw [oneEach_getD] at hval ⊢
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hval ⊢
    rcases hval with e | e
    · exact Or.inl e
    · exact absurd e hw
  have row : ∀ r : Fin 2, r.val ∉ A → ∀ (r' : Fin 2) (c : Fin m),
      H r c = true → H r' c = true := by
    intro r hrA r' c
    refine key r.val hrA r r' c c ?_
    intro w hw hval
    rw [oneEach_getD] at hval ⊢
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hval ⊢
    rcases hval with e | e
    · exact absurd e hw
    · exact Or.inr e
  have m0 : (0 : ℕ) ∈ A := by
    by_contra h
    have h' := row 0 (by simpa using h) 1 c2 h02
    rw [h12] at h'
    exact absurd h' (by simp)
  have m1 : (1 : ℕ) ∈ A := by
    by_contra h
    have h' := row 1 (by simpa using h) 0 c3 h13
    rw [h03] at h'
    exact absurd h' (by simp)
  have m2 : 2 + c1.val ∈ A := by
    by_contra h
    have h' := col c1 h 1 c2 h11
    rw [h12] at h'
    exact absurd h' (by simp)
  have m3 : 2 + c2.val ∈ A := by
    by_contra h
    have h' := col c2 h 0 c3 h02
    rw [h03] at h'
    exact absurd h' (by simp)
  have m4 : 2 + c3.val ∈ A := by
    by_contra h
    have h' := col c3 h 1 c2 h13
    rw [h12] at h'
    exact absurd h' (by simp)
  have d12 : c1.val ≠ c2.val := by
    intro e
    have e' : c1 = c2 := Fin.ext e
    rw [e', h12] at h11
    exact absurd h11 (by simp)
  have d13 : c1.val ≠ c3.val := by
    intro e
    have e' : c1 = c3 := Fin.ext e
    rw [e', h03] at h01
    exact absurd h01 (by simp)
  have d23 : c2.val ≠ c3.val := by
    intro e
    have e' : c2 = c3 := Fin.ext e
    rw [e', h03] at h02
    exact absurd h02 (by simp)
  have hsub : ({0, 1, 2 + c1.val, 2 + c2.val, 2 + c3.val} : Finset ℕ) ⊆ A := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
  have a1 : (0 : ℕ) ∉ ({1, 2 + c1.val, 2 + c2.val, 2 + c3.val} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have a2 : (1 : ℕ) ∉ ({2 + c1.val, 2 + c2.val, 2 + c3.val} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have a3 : 2 + c1.val ∉ ({2 + c2.val, 2 + c3.val} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have a4 : 2 + c2.val ∉ ({2 + c3.val} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have h5 : ({0, 1, 2 + c1.val, 2 + c2.val, 2 + c3.val} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem a1, Finset.card_insert_of_notMem a2,
      Finset.card_insert_of_notMem a3, Finset.card_insert_of_notMem a4, Finset.card_singleton]
  have h6 := Finset.card_le_card hsub
  unfold Circuit.size at hsz hs0
  rw [Finset.card_empty, Nat.add_zero] at hsz
  omega

lemma rcount (n K : ℕ) (E : Fin n → ℕ → Prop)
    (ha : ∀ u, ∃ k, k < K ∧ E u k)
    (hb : ∀ k, k < K → ∀ u v w, E u k → E v k → E w k → u = v ∨ u = w ∨ v = w)
    (hc : ∀ u k, k < K → E u k → (∀ k', k' < K → E u k' → k' = k) → ∀ v, E v k → v = u) :
    ∃ R : Finset ℕ, (∀ k ∈ R, k < K ∧ ∃ u, E u k) ∧ n ≤ R.card := by
  classical
  refine ⟨(Finset.range K).filter (fun k => ∃ u, E u k), ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact hk
  · obtain ⟨wt, hwt⟩ : ∃ wt : Fin n → ℕ, ∀ u, wt u =
        if ((Finset.range K).filter (fun k => E u k)).card = 1 then 2 else 1 :=
      ⟨fun u => if ((Finset.range K).filter (fun k => E u k)).card = 1 then 2 else 1,
        fun _ => rfl⟩
    have hwt2 : ∀ u, wt u ≤ 2 := by
      intro u
      rw [hwt u]
      split_ifs <;> omega
    have h1 : ∀ u : Fin n, 2 ≤ ∑ k ∈ Finset.range K, (if E u k then wt u else 0) := by
      intro u
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      have hpos : 0 < ((Finset.range K).filter (fun k => E u k)).card := by
        obtain ⟨k, hk, hE⟩ := ha u
        exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hE⟩⟩
      by_cases h : ((Finset.range K).filter (fun k => E u k)).card = 1
      · rw [hwt u, ite_eq_left h, h]
      · rw [hwt u, ite_eq_right h]
        omega
    have h2 : ∀ k ∈ Finset.range K, (∑ u : Fin n, (if E u k then wt u else 0)) ≤
        (if (∃ u, E u k) then 2 else 0) := by
      intro k hk
      have hkK : k < K := Finset.mem_range.mp hk
      by_cases hex : ∃ u, E u k
      · rw [ite_eq_left hex]
        by_cases hone : ∃ u, E u k ∧ ((Finset.range K).filter (fun k => E u k)).card = 1
        · obtain ⟨u, hE, hcard⟩ := hone
          obtain ⟨a, hsing⟩ := Finset.card_eq_one.mp hcard
          have hka : k = a := by
            have hmem : k ∈ (Finset.range K).filter (fun k => E u k) :=
              Finset.mem_filter.mpr ⟨hk, hE⟩
            rw [hsing] at hmem
            exact Finset.mem_singleton.mp hmem
          have huniq : ∀ k', k' < K → E u k' → k' = k := by
            intro k' hk' hE'
            have hmem : k' ∈ (Finset.range K).filter (fun k => E u k) :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk', hE'⟩
            rw [hsing] at hmem
            rw [hka]
            exact Finset.mem_singleton.mp hmem
          have hall := hc u k hkK hE huniq
          calc (∑ v : Fin n, (if E v k then wt v else 0))
              ≤ ∑ v : Fin n, (if v = u then 2 else 0) := by
                apply Finset.sum_le_sum
                intro v _
                by_cases hv : E v k
                · rw [ite_eq_left hv, ite_eq_left (hall v hv)]
                  exact hwt2 v
                · rw [ite_eq_right hv]
                  exact Nat.zero_le _
            _ = 2 := by simp
        · push Not at hone
          have hw1 : ∀ v, E v k → wt v = 1 := by
            intro v hv
            rw [hwt v, ite_eq_right (hone v hv)]
          have e : (∑ v : Fin n, (if E v k then wt v else 0)) =
              (Finset.univ.filter (fun v => E v k)).card := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro v _
            by_cases hv : E v k
            · rw [ite_eq_left hv, ite_eq_left hv, hw1 v hv]
            · rw [ite_eq_right hv, ite_eq_right hv]
          rw [e]
          by_contra hgt
          have hgt' : 2 < (Finset.univ.filter (fun v => E v k)).card := by omega
          obtain ⟨a, b, c, ha', hb', hc', hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hgt'
          rcases hb k hkK a b c (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb').2
            (Finset.mem_filter.mp hc').2 with e1 | e1 | e1
          · exact hab e1
          · exact hac e1
          · exact hbc e1
      · rw [ite_eq_right hex]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro v _
        rw [ite_eq_right (fun hv => hex ⟨v, hv⟩)]
    have h3 : 2 * n ≤ 2 * ((Finset.range K).filter (fun k => ∃ u, E u k)).card := by
      calc 2 * n = ∑ _u : Fin n, 2 := by simp [mul_comm]
        _ ≤ ∑ u : Fin n, ∑ k ∈ Finset.range K, (if E u k then wt u else 0) :=
            Finset.sum_le_sum (fun u _ => h1 u)
        _ = ∑ k ∈ Finset.range K, ∑ u : Fin n, (if E u k then wt u else 0) := Finset.sum_comm
        _ ≤ ∑ k ∈ Finset.range K, (if (∃ u, E u k) then 2 else 0) := Finset.sum_le_sum h2
        _ = 2 * ((Finset.range K).filter (fun k => ∃ u, E u k)).card := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    omega

lemma norm_bound (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (hn : 3 ≤ n)
    (htri : ∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C)
    (r : Fin n → Fin C.gates.length) (s : Fin n → ℕ)
    (hrd : ∀ u : Fin n, readsIn C (Finset.range C.gates.length) u.val = 1)
    (ho : ∀ u : Fin n, (C.gates[(r u).val]).op = GateOp.or)
    (hin : ∀ u : Fin n, (C.gates[(r u).val]).inputs = [u.val, s u] ∨
      (C.gates[(r u).val]).inputs = [s u, u.val]) :
    2 * n ≤ C.gates.length := by
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have hinc := inc_of_tri n m G hn htri
  have mu : ∀ u : Fin n, u.val ∈ (C.gates[(r u).val]).inputs := by
    intro u
    rcases hin u with e | e <;> simp [e]
  have ms : ∀ u : Fin n, s u ∈ (C.gates[(r u).val]).inputs := by
    intro u
    rcases hin u with e | e <;> simp [e]
  have honly : ∀ (u : Fin n) (k : ℕ) (hk : k < C.gates.length),
      u.val ∈ (C.gates[k]).inputs → k = (r u).val := by
    intro u k hk hmem
    exact reader_unique C _ k (r u).val (hrd u) hk (r u).isLt hmem (mu u)
  have hmiss : ∀ u : Fin n, ∃ c, G u c = false := by
    intro u
    obtain ⟨w, hwu, _⟩ := third n hn u u
    obtain ⟨c, _, h⟩ := hinc w u hwu
    exact ⟨c, h⟩

  have Ion : ∀ (u : Fin n) (c : Fin m),
      (C.wires (oneEach u c)).getD (n + m + (r u).val) false = true := by
    intro u c
    have L : (oneEach u c).length = n + m := oneEach_length u c
    have hu : (C.wires (oneEach u c)).getD u.val false = true := by
      rw [wires_low C _ _ (by rw [L]; omega), oneEach_getD]
      simp
    rw [wires_gate (n + m) C hRB _ L (r u).val (r u).isLt, or_pair _ _ _ _ (ho u) (hin u), hu]
    simp
  have hout : ∀ u : Fin n, C.output ≠ u.val := by
    intro u e
    obtain ⟨c, hc⟩ := hmiss u
    have h := hRep u c
    unfold Circuit.eval at h
    rw [e, wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD, hc] at h
    simp at h
  have hout2 : ∀ u : Fin n, C.output ≠ n + m + (r u).val := by
    intro u e
    obtain ⟨c, hc⟩ := hmiss u
    have h := hRep u c
    unfold Circuit.eval at h
    rw [e, Ion u c, hc] at h
    exact absurd h (by simp)

  have hrinj : ∀ u v : Fin n, (r u).val = (r v).val → u = v := by
    intro u v e
    by_contra huv
    obtain ⟨c, hvc, huc⟩ := hinc v u (fun e' => huv e'.symm)
    have HI : (C.wires (oneEach u c)).getD (n + m + (r v).val) false = true := by
      rw [← e]
      exact Ion u c
    have h := dom n m G C hAO hRB hRep v u (r v).val (r v).isLt (hrd v) (mu v) (hout v) c HI hvc
    rw [huc] at h
    exact absurd h (by simp)

  have hnoread : ∀ v w : Fin n, n + m + (r w).val ∉ (C.gates[(r v).val]).inputs := by
    intro v w hmem
    have hlt : n + m + (r w).val < n + m + (r v).val :=
      hRB (r v).val (r v).isLt _ (by rw [gateAt_eq C _ (r v).isLt]; exact hmem)
    have hwv : w ≠ v := by
      intro e
      rw [e] at hlt
      omega
    obtain ⟨c, hvc, hwc⟩ := hinc v w (fun e => hwv e.symm)
    have L : (oneEach w c).length = n + m := oneEach_length w c
    have HI : (C.wires (oneEach w c)).getD (n + m + (r v).val) false = true := by
      rw [wires_gate (n + m) C hRB _ L (r v).val (r v).isLt, ho v]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
      exact ⟨_, hmem, Ion w c⟩
    have h := dom n m G C hAO hRB hRep v w (r v).val (r v).isLt (hrd v) (mu v) (hout v) c HI hvc
    rw [hwc] at h
    exact absurd h (by simp)

  have hread : ∀ u : Fin n, ∃ k, k < C.gates.length ∧
      n + m + (r u).val ∈ (gateAt C k).inputs := by
    intro u
    by_contra hno
    obtain ⟨w, hwu, _⟩ := third n hn u u
    obtain ⟨c, huc, hwc⟩ := hinc u w (fun e => hwu e.symm)
    have h := dom2 n m G C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u) (hout2 u) c
      (oneEach w c) (oneEach_length w c) (by rw [oneEach_getD]; simp)
      (by
        intro k hk hmem
        exact absurd ⟨k, hk, by rw [gateAt_eq C k hk]; exact hmem⟩ hno) huc
    rw [hRep w c, hwc] at h
    exact absurd h (by simp)

  have hstep4 : ∀ (u v : Fin n) (T : ℕ) (hT : T < C.gates.length), u ≠ v →
      n + m + (r u).val ∈ (C.gates[T]).inputs → n + m + (r v).val ∈ (C.gates[T]).inputs →
      ¬ (∀ k (hk : k < C.gates.length), n + m + (r u).val ∈ (C.gates[k]).inputs → k = T) := by
    intro u v T hT huv hTu hTv huniq
    have hne : n + m + (r u).val ≠ n + m + (r v).val := by
      intro e
      exact huv (hrinj u v (by omega))
    have hTin := pair_of_mem (C.gates[T]).inputs ((hM _ (List.getElem_mem hT)).2) _ _ hTu hTv hne
    rcases hAO _ (List.getElem_mem hT) with hop | hop
    ·
      obtain ⟨w, hwu, hwv⟩ := third n hn u v
      obtain ⟨c, huc, hvc, hwc⟩ := htri u v w huv (fun e => hwu e.symm) (fun e => hwv e.symm)
      obtain ⟨z, hzdef⟩ : ∃ z : List Bool,
          z = List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)) := ⟨_, rfl⟩
      have Lz : z.length = n + m := by
        rw [hzdef]
        exact colOnly_length n c
      have hzc : z.getD (n + c.val) false = true := by
        rw [hzdef, colOnly_getD]
        simp
      have Lu : (oneEach u c).length = n + m := oneEach_length u c

      have hz0 : C.eval z = false := by
        by_contra hne0
        have htr : C.eval z = true := by simpa using hne0
        unfold Circuit.eval at htr
        have h := mono (n + m) C hAO hRB z (oneEach w c) Lz (oneEach_length w c)
          (by
            intro a ha
            rw [hzdef, colOnly_getD] at ha
            rw [oneEach_getD, ha]
            simp) (C.output + 1) C.output (by omega) htr
        have h2 := hRep w c
        unfold Circuit.eval at h2
        rw [h, hwc] at h2
        exact absurd h2 (by simp)
      by_cases hq : (C.wires z).getD (s v) false = true
      ·
        have HI : (C.wires z).getD (n + m + (r v).val) false = true := by
          rw [wires_gate (n + m) C hRB _ Lz (r v).val (r v).isLt,
            or_pair _ _ _ _ (ho v) (hin v), hq]
          simp
        have h := dom1 n m G C hAO hRB hRep v (r v).val (r v).isLt (hrd v) (mu v) (hout v) c z Lz
          hzc HI hvc
        rw [hz0] at h
        exact absurd h (by simp)
      ·
        have hq0 : (C.wires z).getD (s v) false = false := by simpa using hq
        have hsv_lt : s v < n + m + (r v).val :=
          hRB (r v).val (r v).isLt (s v) (by rw [gateAt_eq C _ (r v).isLt]; exact ms v)
        have hrv_lt : n + m + (r v).val < n + m + T :=
          hRB T hT _ (by rw [gateAt_eq C T hT]; exact hTv)
        have hsvu : s v ≠ u.val := by
          intro e
          have h1 := ms v
          rw [e] at h1
          have h2 := honly u (r v).val (r v).isLt h1
          exact huv (hrinj u v h2.symm)
        have hsvI : s v ≠ n + m + (r u).val := by
          intro e
          have h1 := ms v
          rw [e] at h1
          exact hnoread v u h1
        have hqx : (C.wires (oneEach u c)).getD (s v) false = false := by
          by_contra hne1
          have hon1 : (C.wires (oneEach u c)).getD (s v) false = true := by simpa using hne1
          have h := mtrans (n + m) C hAO hRB (oneEach u c) z Lu Lz
            (fun t => t = u.val ∨ t = n + m + (r u).val) (n + m + T)
            (by
              intro a _ hS h1
              rw [oneEach_getD] at h1
              simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
              rcases h1 with e | e
              · exact absurd (Or.inl e) hS
              · rw [e]; exact hzc)
            (by
              intro k hk hkB hS
              left
              intro a ha e
              rcases e with e | e
              · rw [e] at ha
                have hkk := honly u k hk ha
                exact hS (Or.inr (by rw [hkk]))
              · rw [e] at ha
                have hkT := huniq k hk ha
                omega)
            (s v) (by omega) (by
              intro e
              rcases e with e | e
              · exact hsvu e
              · exact hsvI e) hon1
          rw [hq0] at h
          exact absurd h (by simp)
        have hvx : (C.wires (oneEach u c)).getD v.val false = false := by
          rw [wires_low C _ _ (by rw [Lu]; omega), oneEach_getD]
          have h1 : ¬ v.val = u.val := fun e => huv (Fin.ext e.symm)
          have h2 : ¬ v.val = n + c.val := by omega
          simp [h1, h2]
        have hIvx : (C.wires (oneEach u c)).getD (n + m + (r v).val) false = false := by
          rw [wires_gate (n + m) C hRB _ Lu (r v).val (r v).isLt, or_pair _ _ _ _ (ho v) (hin v)]
          simp only [hvx, hqx, Bool.or_false]
        have h := dom2 n m G C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u)
          (hout2 u) c z Lz hzc
          (by
            intro k hk hmem hon
            have hkT : k = T := huniq k hk hmem
            rw [hkT, wires_gate (n + m) C hRB _ Lu T hT, and_pair _ _ _ _ hop hTin, hIvx] at hon
            simp at hon) huc
        rw [hz0] at h
        exact absurd h (by simp)
    ·
      obtain ⟨c, huc, hvc⟩ := hinc u v huv
      have Lv : (oneEach v c).length = n + m := oneEach_length v c
      have h := dom2 n m G C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u)
        (hout2 u) c (oneEach v c) Lv (by rw [oneEach_getD]; simp)
        (by
          intro k hk hmem _
          have hkT : k = T := huniq k hk hmem
          rw [hkT, wires_gate (n + m) C hRB _ Lv T hT, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
          exact ⟨_, hTv, Ion v c⟩) huc
      rw [hRep v c, hvc] at h
      exact absurd h (by simp)

  obtain ⟨R, hR, hRn⟩ := rcount n C.gates.length
    (fun u k => n + m + (r u).val ∈ (gateAt C k).inputs) hread
    (by
      intro k hk u v w hu hv hw
      have hu' : n + m + (r u).val ∈ (gateAt C k).inputs := hu
      have hv' : n + m + (r v).val ∈ (gateAt C k).inputs := hv
      have hw' : n + m + (r w).val ∈ (gateAt C k).inputs := hw
      rw [gateAt_eq C k hk] at hu' hv' hw'
      have h3 := three_mem _ ((hM _ (List.getElem_mem hk)).2) _ _ _ hu' hv' hw'
      rcases h3 with e | e | e
      · left
        exact hrinj u v (by omega)
      · right; left
        exact hrinj u w (by omega)
      · right; right
        exact hrinj v w (by omega))
    (by
      intro u k hk hE huniq v hEv
      have hE' : n + m + (r u).val ∈ (gateAt C k).inputs := hE
      have hEv' : n + m + (r v).val ∈ (gateAt C k).inputs := hEv
      rw [gateAt_eq C k hk] at hE' hEv'
      by_contra hvu
      exact hstep4 u v k hk (fun e => hvu e.symm) hE' hEv'
        (by
          intro k' hk' hmem
          exact huniq k' hk' (by
            rw [gateAt_eq C k' hk']
            exact hmem)))
  have hrows : (Finset.univ.image (fun u : Fin n => (r u).val)).card = n := by
    rw [Finset.card_image_of_injective _ (fun u v e => hrinj u v e)]
    simp
  have hdisj : Disjoint R (Finset.univ.image (fun u : Fin n => (r u).val)) := by
    rw [Finset.disjoint_left]
    intro k hkR hkI
    obtain ⟨hk, u, hE⟩ := hR k hkR
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hkI
    have hE' : n + m + (r u).val ∈ (gateAt C k).inputs := hE
    rw [gateAt_eq C k hk] at hE'
    have hv' : (r v).val = k := hv
    subst hv'
    exact hnoread v u hE'
  have hsub : R ∪ Finset.univ.image (fun u : Fin n => (r u).val) ⊆
      Finset.range C.gates.length := by
    intro k hk
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hk with h | h
    · exact (hR k h).1
    · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
      have hv' : (r v).val = k := hv
      rw [← hv']
      exact (r v).isLt
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, hrows] at hcard
  omega

lemma step (n : ℕ)
    (ih : ∀ (m s : ℕ) (G : Fin n → Fin m → Bool), 3 ≤ n →
      (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
        ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
      RepSizeAtMost G s → 2 * n ≤ s)
    (m s : ℕ) (G : Fin (n + 1) → Fin m → Bool) (hn : 3 ≤ n + 1)
    (htri : ∀ u v w : Fin (n + 1), u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (hrep : RepSizeAtMost G s) : 2 * (n + 1) ≤ s := by
  have hinc := inc_of_tri (n + 1) m G hn htri
  rcases PEqualNP.Outside.L_meta_25491 n m s G (by omega) hinc hrep with
    ⟨u, t, hts, hdel⟩ | ⟨C, hM, hCs, hRB, hRep, hrow⟩
  · by_cases h3 : 3 ≤ n
    · have h := ih m t (fun a c => G (u.succAbove a) c) h3
        (by
          intro a b c hab hac hbc
          exact htri _ _ _ (fun e => hab (Fin.succAbove_right_injective e))
            (fun e => hac (Fin.succAbove_right_injective e))
            (fun e => hbc (Fin.succAbove_right_injective e))) hdel
      omega
    · have hn2 : n = 2 := by omega
      subst hn2
      have hsa : ∀ a : Fin 2, u.succAbove a ≠ u := fun a => Fin.succAbove_ne u a
      have h01 : u.succAbove 0 ≠ u.succAbove 1 := by
        intro e
        have h := Fin.succAbove_right_injective e
        exact absurd h (by decide)
      obtain ⟨c1, a1, a2, _⟩ := htri (u.succAbove 0) (u.succAbove 1) u h01 (hsa 0) (hsa 1)
      obtain ⟨c2, b1, _, b3⟩ :=
        htri (u.succAbove 0) u (u.succAbove 1) (hsa 0) h01 (fun e => hsa 1 e.symm)
      obtain ⟨c3, d1, _, d3⟩ :=
        htri (u.succAbove 1) u (u.succAbove 0) (hsa 1) (fun e => h01 e.symm)
          (fun e => hsa 0 e.symm)
      have h := two_rows m (fun a c => G (u.succAbove a) c) c1 c2 c3 a1 a2 b1 b3 d3 d1 t hdel
      omega
  · choose r sp hr using fun u => (hrow u).2
    have h := norm_bound (n + 1) m G C hn htri hM hRB hRep r sp
      (fun u => (hrow u).1) (fun u => (hr u).1) (fun u => (hr u).2)
    unfold Circuit.size at hCs
    omega

end PEqualNP.Outside.L_meta_25529_aux

theorem PEqualNP.Outside.L_meta_25529 : (∀ (n m s : ℕ) (G : Fin n → Fin m → Bool),
  3 ≤ n →
  (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
    ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
  PEqualNP.Represents.RepSizeAtMost G s →
  2 * n ≤ s) := by
  intro n
  induction n with
  | zero =>
    intro m s G hn
    omega
  | succ n ih =>
    intro m s G hn htri hrep
    exact PEqualNP.Outside.L_meta_25529_aux.step n ih m s G hn htri hrep
