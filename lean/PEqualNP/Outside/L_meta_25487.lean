import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25487_aux

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

lemma trace (n m : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack (n + m) C) (r : Fin n) (c : Fin m) (z : ℕ) :
    ∀ w, (C.wires (oneEach r c)).getD w false = true → (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD w false = false →
      Relation.ReflTransGen (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ ∃ idx : Fin C.gates.length, next = n + m + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) r.val w ∨
        ((C.wires (oneEach r c)).getD z false = true ∧ (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD z false = false) := by
  have L1 : (oneEach r c).length = n + m := oneEach_length r c
  have L0 : (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := colOnly_length n c
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h1 h0
    by_cases hwz : w = z
    · right
      rw [← hwz]
      exact ⟨h1, h0⟩
    · by_cases hlow : w < n + m
      · left
        rw [wires_low C _ w (by rw [L1]; exact hlow), oneEach_getD] at h1
        rw [wires_low C _ w (by rw [L0]; exact hlow), colOnly_getD] at h0
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        simp only [decide_eq_false_iff_not] at h0
        rcases h1 with e | e
        · rw [e]
        · exact absurd e h0
      · by_cases hhigh : n + m + C.gates.length ≤ w
        · rw [wires_high C _ w (by rw [L1]; exact hhigh)] at h1
          exact absurd h1 (by simp)
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
          have hk : k < C.gates.length := by omega
          have h1' := h1
          have h0' := h0
          rw [wires_gate (n + m) C hRB _ L1 k hk] at h1'
          rw [wires_gate (n + m) C hRB _ L0 k hk] at h0'
          obtain ⟨a, ha, ha1, ha0⟩ :=
            bad_input _ (hAO (C.gates[k]) (List.getElem_mem hk)) _ _ h1' h0'
          have hlt : a < n + m + k := hRB k hk a (by rw [gateAt_eq C k hk]; exact ha)
          rcases ih a hlt ha1 ha0 with path | hz
          · by_cases haz : a = z
            · right
              rw [← haz]
              exact ⟨ha1, ha0⟩
            · left
              exact Relation.ReflTransGen.tail path
                ⟨haz, hwz, ⟨k, hk⟩, rfl, by rw [gateAt_eq C k hk]; exact ha⟩
          · exact Or.inr hz

lemma path_weaken (N : ℕ) (C : Circuit) (z a b : ℕ)
    (h : Relation.ReflTransGen (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧
      ∃ idx : Fin C.gates.length, next = N + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) a b) :
    Relation.ReflTransGen (fun source target : ℕ =>
      ∃ idx : Fin C.gates.length, target = N + idx.val ∧ source ∈ (gateAt C idx.val).inputs) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih hab.2.2

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C)
    (hop : (gateAt C j.val).op = GateOp.and) (hq : q ∈ (gateAt C j.val).inputs)
    (hcg : ¬ (u.val ≠ n + m + j.val ∧ C.output ≠ n + m + j.val ∧
      Relation.ReflTransGen (fun prev next : ℕ => prev ≠ (n + m + j.val) ∧ next ≠ (n + m + j.val) ∧ ∃ idx : Fin C.gates.length, next = n + m + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) u.val C.output))
    (hcq : ¬ (v.val ≠ q ∧ C.output ≠ q ∧ Relation.ReflTransGen (fun prev next : ℕ => prev ≠ q ∧ next ≠ q ∧ ∃ idx : Fin C.gates.length, next = n + m + idx.val ∧ prev ∈ (gateAt C idx.val).inputs) v.val C.output))
    (hnp : ¬ Relation.ReflTransGen (fun source target : ℕ => ∃ idx : Fin C.gates.length, target = n + m + idx.val ∧ source ∈ (gateAt C idx.val).inputs) u.val q)
    (c : Fin m) (hw : ∃ w : Fin n, G w c = false) :
    (G u c = true → (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD q false = true) ∧
      (G v c = true → (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD q false = false) := by
  obtain ⟨z, hz⟩ := hw
  rw [gateAt_eq C j.val j.isLt] at hop hq
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  have L0 : (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).length = n + m := colOnly_length n c
  have o0 : (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD C.output false = false := by
    by_contra hne
    have htr : (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD C.output false = true := by simpa using hne
    have h := mono (n + m) C hAO hRB _ (oneEach z c) L0 (oneEach_length z c)
      (by
        intro a ha
        rw [colOnly_getD] at ha
        rw [oneEach_getD, ha]
        simp) (C.output + 1) C.output (by omega) htr
    have h2 := hRep z c
    unfold Circuit.eval at h2
    rw [h, hz] at h2
    exact absurd h2 (by simp)
  constructor
  · intro huc
    have L1 : (oneEach u c).length = n + m := oneEach_length u c
    have o1 : (C.wires (oneEach u c)).getD C.output false = true := by
      have h := hRep u c
      unfold Circuit.eval at h
      rw [h, huc]
    have hg : (C.wires (oneEach u c)).getD (n + m + j.val) false = true ∧
        (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD (n + m + j.val) false = false := by
      rcases trace n m C hAO hRB u c (n + m + j.val) C.output o1 o0 with path | h
      · by_cases hog : C.output = n + m + j.val
        · rw [← hog]
          exact ⟨o1, o0⟩
        · exact absurd ⟨by omega, hog, path⟩ hcg
      · exact h
    have g1 := hg.1
    rw [wires_gate (n + m) C hRB _ L1 j.val j.isLt, hop] at g1
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id_eq] at g1
    have q1 := g1 q hq
    by_contra hq0
    have hq0' : (C.wires (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c)))).getD q false = false := by simpa using hq0
    rcases trace n m C hAO hRB u c (n + m + C.gates.length) q q1 hq0' with path | h
    · exact hnp (path_weaken (n + m) C _ _ _ path)
    · have hf := h.1
      rw [wires_high C _ _ (by rw [L1])] at hf
      exact absurd hf (by simp)
  · intro hvc
    have o2 : (C.wires (oneEach v c)).getD C.output false = true := by
      have h := hRep v c
      unfold Circuit.eval at h
      rw [h, hvc]
    rcases trace n m C hAO hRB v c q C.output o2 o0 with path | h
    · by_cases hvq : v.val = q
      · rw [← hvq, wires_low C _ _ (by rw [L0]; omega), colOnly_getD]
        have h3 : ¬ v.val = n + c.val := by omega
        simp [h3]
      · by_cases hoq : C.output = q
        · rw [← hoq]
          exact o0
        · exact absurd ⟨hvq, hoq, path⟩ hcq
    · exact h.2

end PEqualNP.Outside.L_meta_25487_aux

theorem PEqualNP.Outside.L_meta_25487 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n)
    (j : Fin C.gates.length) (q : ℕ),
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let g := n + m + j.val
  let edge := fun source target : ℕ => ∃ idx : Fin C.gates.length,
    target = n + m + idx.val ∧ source ∈ (gate idx.val).inputs
  let cuts := fun (z start : ℕ) =>
    ¬ (start ≠ z ∧ C.output ≠ z ∧ Relation.ReflTransGen
      (fun prev next : ℕ => prev ≠ z ∧ next ≠ z ∧ edge prev next) start C.output)
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C → u ≠ v →
  (gate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  q ∈ (gate j.val).inputs →
  cuts g u.val → cuts q v.val → ¬ Relation.ReflTransGen edge u.val q →
  ∀ c : Fin m, (∃ w : Fin n, G w c = false) →
    let col := List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))
    let value := (C.wires col).getD q false
    (G u c = true → value = true) ∧ (G v c = true → value = false)) := by
  intro n m G C u v j q gate g edge cuts hM hRB hRep _ hop hq hcg hcq hnp c hw
  exact PEqualNP.Outside.L_meta_25487_aux.main n m G C u v j q hM hRB hRep hop hq hcg hcq hnp c hw
