import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25480_aux

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

lemma rowOnly_length {n : ℕ} (m : ℕ) (u : Fin n) :
    (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false).length = n + m := by
  simp

lemma colOnly_length (n : ℕ) {m : ℕ} (v : Fin m) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).length = n + m := by
  simp

lemma rowOnly_getD {n : ℕ} (m : ℕ) (u : Fin n) (i : ℕ) :
    (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false).getD i false =
      decide (i = u.val) := by
  by_cases h1 : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h1)]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
    simp [Fin.ext_iff]
  · by_cases h2 : i < n + m
    · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      simp [h3]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      have h3 : ¬ i = u.val := by omega
      simp [h3]

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

lemma mono (N : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hRB : ReadsBack N C)
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

lemma bool_split (ra rb ka kb : Bool) (h1 : (ra && rb) = false) (h2 : (ka && kb) = false)
    (h3 : ¬ (ra = false ∧ ka = false)) (h4 : ¬ (rb = false ∧ kb = false)) :
    (ra = true ∧ rb = false ∧ kb = true ∧ ka = false) ∨
      (rb = true ∧ ra = false ∧ ka = true ∧ kb = false) := by
  cases ra <;> cases rb <;> cases ka <;> cases kb <;> simp_all

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (hAO2 : PEqualNP.TopForm.IsAO2 (n + m) C) (hRep : Represents G C)
    (u : Fin n) (v : Fin m) (huv : G u v = true)
    (hc : ∃ c : Fin m, G u c = false) (hr : ∃ r : Fin n, G r v = false) :
    ∃ (j : Fin C.gates.length) (a b : ℕ),
      (C.gates.get j).op = GateOp.and ∧
      (C.gates.get j).inputs = [a, b] ∧
      (C.wires (oneEach u v)).getD (n + m + j.val) false = true ∧
      (((C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD a false = true ∧
        (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD b false = false ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD b false = true ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD a false = false) ∨
       ((C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD b false = true ∧
        (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD a false = false ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD a false = true ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD b false = false)) := by
  obtain ⟨hAO, hRB, hlen2⟩ := hAO2
  obtain ⟨c, hc⟩ := hc
  obtain ⟨r, hr⟩ := hr
  have LE : (oneEach u v).length = n + m := oneEach_length u v
  have LR := rowOnly_length m u
  have LK := colOnly_length n v

  have oE : (C.wires (oneEach u v)).getD C.output false = true := by
    have h := hRep u v
    unfold Circuit.eval at h
    rw [h, huv]
  have oR : (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD
      C.output false = false := by
    by_contra hne
    have ht : (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD
        C.output false = true := by simpa using hne
    have h := mono (n + m) C hAO hRB _ (oneEach u c) LR (oneEach_length u c)
      (by
        intro i hi
        rw [rowOnly_getD] at hi
        rw [oneEach_getD, hi]
        rfl) (C.output + 1) C.output (by omega) ht
    have h2 := hRep u c
    unfold Circuit.eval at h2
    rw [h, hc] at h2
    exact absurd h2 (by simp)
  have oK : (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD
      C.output false = false := by
    by_contra hne
    have ht : (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD
        C.output false = true := by simpa using hne
    have h := mono (n + m) C hAO hRB _ (oneEach r v) LK (oneEach_length r v)
      (by
        intro i hi
        rw [colOnly_getD] at hi
        rw [oneEach_getD, hi]
        simp) (C.output + 1) C.output (by omega) ht
    have h2 := hRep r v
    unfold Circuit.eval at h2
    rw [h, hr] at h2
    exact absurd h2 (by simp)

  have key : ∀ k w : ℕ, w < k →
      (C.wires (oneEach u v)).getD w false = true →
      (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD w false = false →
      (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD w false = false →
      ∃ (j : Fin C.gates.length) (a b : ℕ),
      (C.gates.get j).op = GateOp.and ∧
      (C.gates.get j).inputs = [a, b] ∧
      (C.wires (oneEach u v)).getD (n + m + j.val) false = true ∧
      (((C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD a false = true ∧
        (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD b false = false ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD b false = true ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD a false = false) ∨
       ((C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD b false = true ∧
        (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD a false = false ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD a false = true ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD b false = false)) := by
    intro k
    induction k with
    | zero => intro w hw; omega
    | succ k ih =>
      intro w hw hE hR hK
      by_cases hlow : w < n + m
      · rw [wires_low C _ w (by rw [LE]; exact hlow), oneEach_getD] at hE
        rw [wires_low C _ w (by rw [LR]; exact hlow), rowOnly_getD] at hR
        rw [wires_low C _ w (by rw [LK]; exact hlow), colOnly_getD] at hK
        rw [hR, hK] at hE
        exact absurd hE (by simp)
      · by_cases hhigh : n + m + C.gates.length ≤ w
        · rw [wires_high C _ w (by rw [LE]; exact hhigh)] at hE
          exact absurd hE (by simp)
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
          have hj : j < C.gates.length := by omega
          have hE0 := hE
          rw [wires_gate (n + m) C hRB _ LE j hj] at hE
          rw [wires_gate (n + m) C hRB _ LR j hj] at hR
          rw [wires_gate (n + m) C hRB _ LK j hj] at hK
          obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen2 (C.gates[j]) (List.getElem_mem hj))
          have ha : a < n + m + j := hRB j hj a (by rw [gateAt_eq C j hj, hab]; simp)
          have hb : b < n + m + j := hRB j hj b (by rw [gateAt_eq C j hj, hab]; simp)
          rw [hab] at hE hR hK
          rcases hAO (C.gates[j]) (List.getElem_mem hj) with hop | hop
          · rw [hop] at hE hR hK
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true] at hE hR hK
            by_cases pa : (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD a false = false ∧
                (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD a false = false
            · exact ih a (by omega) hE.1 pa.1 pa.2
            · by_cases pb : (C.wires (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false)).getD b false = false ∧
                  (C.wires (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v)))).getD b false = false
              · exact ih b (by omega) hE.2 pb.1 pb.2
              · exact ⟨⟨j, hj⟩, a, b, by simpa using hop, by simpa using hab, hE0,
                  bool_split _ _ _ _ hR hK pa pb⟩
          · rw [hop] at hE hR hK
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff] at hE hR hK
            rcases hE with hEa | hEb
            · exact ih a (by omega) hEa hR.1 hK.1
            · exact ih b (by omega) hEb hR.2 hK.2
  exact key (C.output + 1) C.output (by omega) oE oR oK

end PEqualNP.Outside.L_meta_25480_aux

theorem PEqualNP.Outside.L_meta_25480 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.Represents.Represents G C →
  ∀ (u : Fin n) (v : Fin m), G u v = true →
    (∃ c : Fin m, G u c = false) → (∃ r : Fin n, G r v = false) →
    let rowOnly := List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false
    let colOnly := List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))
    let value := fun (x : List Bool) (w : ℕ) => (C.wires x).getD w false
    let split := fun (left right : ℕ) =>
      value rowOnly left = true ∧ value rowOnly right = false ∧
      value colOnly right = true ∧ value colOnly left = false
    ∃ (j : Fin C.gates.length) (a b : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.gates.get j).inputs = [a, b] ∧
      value (PEqualNP.Represents.oneEach u v) (n + m + j.val) = true ∧
      (split a b ∨ split b a)) := by
  intro n m G C hAO hRep u v huv hc hr
  exact PEqualNP.Outside.L_meta_25480_aux.main n m G C hAO hRep u v huv hc hr
