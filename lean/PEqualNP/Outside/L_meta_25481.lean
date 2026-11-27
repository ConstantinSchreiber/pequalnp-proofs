import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25481_aux

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

lemma main (n m : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit) (u v : Fin n) (O : ℕ)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + m) C)
    (hRep : Represents G C)
    (hO : ∀ c : Fin m, (C.wires (oneEach v c)).getD O false = true)
    (hout : C.output ≠ u.val)
    (hpath : ¬ Relation.TransGen (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧ ∃ j : Fin C.gates.length, b = n + m + j.val ∧ a ∈ (gateAt C j.val).inputs) u.val C.output) :
    ∀ c : Fin m, G u c = true → G v c = true := by
  intro c huc
  have L1 := oneEach_length u c
  have L2 := oneEach_length v c
  have key : ∀ k w : ℕ, w < k → (C.wires (oneEach u c)).getD w false = true →
      (C.wires (oneEach v c)).getD w false = false →
      w = u.val ∨ Relation.TransGen (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧ ∃ j : Fin C.gates.length, b = n + m + j.val ∧ a ∈ (gateAt C j.val).inputs) u.val w := by
    intro k
    induction k with
    | zero => intro w hw; omega
    | succ k ih =>
      intro w hw h1 h2
      by_cases hlow : w < n + m
      · left
        rw [wires_low C _ w (by rw [L1]; exact hlow), oneEach_getD] at h1
        rw [wires_low C _ w (by rw [L2]; exact hlow), oneEach_getD] at h2
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
        rcases h1 with h | h
        · exact h
        · exact absurd h h2.2
      · by_cases hhigh : n + m + C.gates.length ≤ w
        · rw [wires_high C _ w (by rw [L1]; exact hhigh)] at h1
          exact absurd h1 (by simp)
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + m + j := ⟨w - (n + m), by omega⟩
          have hj : j < C.gates.length := by omega
          have h1' := h1
          have h2' := h2
          rw [wires_gate (n + m) C hRB _ L1 j hj] at h1'
          rw [wires_gate (n + m) C hRB _ L2 j hj] at h2'
          have hop : (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or := by
            have h := (hM (C.gates[j]) (List.getElem_mem hj)).1
            simpa using h
          obtain ⟨i, hi, hi1, hi2⟩ := bad_input _ hop _ _ h1' h2'
          have hlt : i < n + m + j := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
          have hiO : i ≠ O := by
            intro e
            rw [e, hO c] at hi2
            exact absurd hi2 (by simp)
          have hwO : n + m + j ≠ O := by
            intro e
            rw [e, hO c] at h2
            exact absurd h2 (by simp)
          have hR : (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧ ∃ j : Fin C.gates.length, b = n + m + j.val ∧ a ∈ (gateAt C j.val).inputs) i (n + m + j) :=
            ⟨hiO, hwO, ⟨j, hj⟩, rfl, by rw [gateAt_eq C j hj]; exact hi⟩
          right
          rcases ih i (by omega) hi1 hi2 with e | t
          · have hiO' : u.val ≠ O := by rw [← e]; exact hiO
            have hi' : u.val ∈ (gateAt C j).inputs := by rw [← e, gateAt_eq C j hj]; exact hi
            exact Relation.TransGen.single ⟨hiO', hwO, ⟨j, hj⟩, rfl, hi'⟩
          · exact Relation.TransGen.tail t hR
  by_contra hvc
  have r1 := hRep u c
  have r2 := hRep v c
  unfold Circuit.eval at r1 r2
  have o1 : (C.wires (oneEach u c)).getD C.output false = true := by rw [r1, huc]
  have o2 : (C.wires (oneEach v c)).getD C.output false = false := by
    rw [r2]
    simpa using hvc
  rcases key (C.output + 1) C.output (by omega) o1 o2 with e | t
  · exact hout e
  · exact hpath t

end PEqualNP.Outside.L_meta_25481_aux

theorem PEqualNP.Outside.L_meta_25481 : (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (u v : Fin n) (O : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ≠ u.val →
  O < n + m + C.gates.length →
  (∀ c : Fin m, (C.wires (PEqualNP.Represents.oneEach v c)).getD O false = true) →
  (¬ Relation.TransGen
    (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
      ∃ j : Fin C.gates.length, b = n + m + j.val ∧
        a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs)
    u.val C.output) →
  ∀ c : Fin m, G u c = true → G v c = true) := by
  intro n m G C u v O hM hRB hRep _ _ hout _ hO hpath
  exact PEqualNP.Outside.L_meta_25481_aux.main n m G C u v O hM hRB hRep hO hout hpath
