import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25551_aux

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


lemma before_top (N : ℕ) (C : Circuit) (S region : Finset ℕ) (top : ℕ) (hRB : ReadsBack N C)
    (hout : ∀ k < C.gates.length, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ S ∧ ((N ≤ w ∧ w - N ∈ region) → w = N + top))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, w < N → w ∉ S → x.getD w false = y.getD w false) :
    ∀ w, w < N + top → w ∉ S → ¬ (N ≤ w ∧ w - N ∈ region) →
      (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwt hS hin
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow), wires_low C _ w (by rw [hy]; exact hlow)]
      exact hxy w hlow hS
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh), wires_high C _ w (by rw [hy]; exact hhigh)]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        have hkr : k ∉ region := by
          intro h
          exact hin ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact h⟩
        rw [wires_gate N C hRB _ hx k hk, wires_gate N C hRB _ hy k hk]
        congr 1
        apply List.map_congr_left
        intro a ha
        have ha' : a ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hk]; exact ha
        have hlt := hRB k hk a ha'
        obtain ⟨hs, htp⟩ := hout k hk hkr a ha'
        exact ih a hlt (by omega) hs (fun hi => by have := htp hi; omega)

lemma inside_agree (N : ℕ) (C : Circuit) (S region entry : Finset ℕ) (hRB : ReadsBack N C)
    (hreg : region ⊆ Finset.range C.gates.length) (hS : ∀ w ∈ S, w < N)
    (hin : ∀ k ∈ region, ∀ w ∈ (gateAt C k).inputs, w ∈ S ∨ (N ≤ w ∧ w - N ∈ region) ∨ w ∈ entry)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w ∈ S, x.getD w false = y.getD w false)
    (hent : ∀ w ∈ entry, (C.wires x).getD w false = (C.wires y).getD w false) :
    ∀ k, k ∈ region → (C.wires x).getD (N + k) false = (C.wires y).getD (N + k) false := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hkl : k < C.gates.length := Finset.mem_range.mp (hreg hk)
    rw [wires_gate N C hRB _ hx k hkl, wires_gate N C hRB _ hy k hkl]
    congr 1
    apply List.map_congr_left
    intro a ha
    have ha' : a ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hkl]; exact ha
    have hlt := hRB k hkl a ha'
    rcases hin k hk a ha' with h | h | h
    · have hl := hS a h
      rw [wires_low C _ a (by rw [hx]; exact hl), wires_low C _ a (by rw [hy]; exact hl)]
      exact hxy a h
    · obtain ⟨k', rfl⟩ : ∃ k', a = N + k' := ⟨a - N, by omega⟩
      have hk' : k' ∈ region := by
        have h2 := h.2
        rw [Nat.add_sub_cancel_left] at h2
        exact h2
      exact ih k' (by omega) hk'
    · exact hent a h

lemma inside_mono (N : ℕ) (C : Circuit) (S region entry : Finset ℕ) (hRB : ReadsBack N C)
    (hreg : region ⊆ Finset.range C.gates.length) (hS : ∀ w ∈ S, w < N)
    (hop : ∀ k ∈ region, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hin : ∀ k ∈ region, ∀ w ∈ (gateAt C k).inputs, w ∈ S ∨ (N ≤ w ∧ w - N ∈ region) ∨ w ∈ entry)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w ∈ S, x.getD w false = y.getD w false)
    (hent : ∀ w ∈ entry, (C.wires x).getD w false = true → (C.wires y).getD w false = true) :
    ∀ k, k ∈ region → (C.wires x).getD (N + k) false = true →
      (C.wires y).getD (N + k) false = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h1
    have hkl : k < C.gates.length := Finset.mem_range.mp (hreg hk)
    by_contra h2
    have h2' : (C.wires y).getD (N + k) false = false := by simpa using h2
    rw [wires_gate N C hRB _ hx k hkl] at h1
    rw [wires_gate N C hRB _ hy k hkl] at h2'
    have hop' : (C.gates[k]).op = GateOp.and ∨ (C.gates[k]).op = GateOp.or := by
      have h := hop k hk
      rw [gateAt_eq C k hkl] at h
      exact h
    obtain ⟨a, ha, ha1, ha2⟩ := bad_input _ hop' _ _ h1 h2'
    have ha' : a ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hkl]; exact ha
    have hlt := hRB k hkl a ha'
    rcases hin k hk a ha' with h | h | h
    · have hl := hS a h
      rw [wires_low C _ a (by rw [hx]; exact hl)] at ha1
      rw [wires_low C _ a (by rw [hy]; exact hl), ← hxy a h, ha1] at ha2
      exact absurd ha2 (by simp)
    · obtain ⟨k', rfl⟩ : ∃ k', a = N + k' := ⟨a - N, by omega⟩
      have hk' : k' ∈ region := by
        have h2 := h.2
        rw [Nat.add_sub_cancel_left] at h2
        exact h2
      rw [ih k' (by omega) hk' ha1] at ha2
      exact absurd ha2 (by simp)
    · rw [hent a h ha1] at ha2
      exact absurd ha2 (by simp)

lemma after_top (N : ℕ) (C : Circuit) (S region : Finset ℕ) (top : ℕ) (hRB : ReadsBack N C)
    (hout : ∀ k < C.gates.length, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ S ∧ ((N ≤ w ∧ w - N ∈ region) → w = N + top))
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ w, w < N → w ∉ S → x.getD w false = y.getD w false)
    (htopv : (C.wires x).getD (N + top) false = (C.wires y).getD (N + top) false) :
    ∀ w, w ∉ S → ((N ≤ w ∧ w - N ∈ region) → w = N + top) →
      (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hS hin
    by_cases hlow : w < N
    · rw [wires_low C _ w (by rw [hx]; exact hlow), wires_low C _ w (by rw [hy]; exact hlow)]
      exact hxy w hlow hS
    · by_cases hhigh : N + C.gates.length ≤ w
      · rw [wires_high C _ w (by rw [hx]; exact hhigh), wires_high C _ w (by rw [hy]; exact hhigh)]
      · obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hkr : k ∈ region
        · have h := hin ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hkr⟩
          have hkt : k = top := by omega
          rw [hkt]
          exact htopv
        · rw [wires_gate N C hRB _ hx k hk, wires_gate N C hRB _ hy k hk]
          congr 1
          apply List.map_congr_left
          intro a ha
          have ha' : a ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hk]; exact ha
          have hlt := hRB k hk a ha'
          obtain ⟨hs, htp⟩ := hout k hk hkr a ha'
          exact ih a hlt hs htp

lemma core (N : ℕ) (C : Circuit) (S region entry : Finset ℕ) (top : ℕ)
    (hRB : ReadsBack N C) (hreg : region ⊆ Finset.range C.gates.length) (htop : top ∈ region)
    (hS : ∀ w ∈ S, w < N) (hent : entry.card ≤ 1)
    (hentry : ∀ w ∈ entry, w < N + top ∧ w ∉ S ∧ ¬ (N ≤ w ∧ w - N ∈ region))
    (hin : ∀ k ∈ region, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ S ∨ (N ≤ w ∧ w - N ∈ region) ∨ w ∈ entry)
    (hout : ∀ k < C.gates.length, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ S ∧ ((N ≤ w ∧ w - N ∈ region) → w = N + top))
    (ho1 : C.output ∉ S) (ho2 : (N ≤ C.output ∧ C.output - N ∈ region) → C.output = N + top)
    {ι κ : Type} (P : Finset ι) (Q : κ → Prop) (inp : ι → κ → List Bool)
    (hlen : ∀ p q, (inp p q).length = N)
    (h1 : ∀ p ∈ P, ∀ p' ∈ P, ∀ q, ∀ w, w < N → w ∉ S →
      (inp p q).getD w false = (inp p' q).getD w false)
    (h2 : ∀ p ∈ P, ∀ q, Q q → ∀ q', Q q' → ∀ w ∈ S,
      (inp p q).getD w false = (inp p q').getD w false)
    (hcard : 2 + entry.card < P.card) :
    ∃ p ∈ P, ∃ p' ∈ P, p ≠ p' ∧ ∀ q, Q q → C.eval (inp p q) = C.eval (inp p' q) := by
  classical
  have hPne : P.Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨pstar, hpstar⟩ := hPne
  obtain ⟨E, hEdef⟩ : ∃ E : κ → Bool, ∀ q, E q =
      decide (∃ w ∈ entry, (C.wires (inp pstar q)).getD w false = true) := ⟨_, fun _ => rfl⟩
  have hE : ∀ p ∈ P, ∀ q, ∀ w ∈ entry, (C.wires (inp p q)).getD w false = E q := by
    intro p hp q w hw
    obtain ⟨hw1, hw2, hw3⟩ := hentry w hw
    have e := before_top N C S region top hRB hout (inp p q) (inp pstar q) (hlen p q)
      (hlen pstar q) (h1 p hp pstar hpstar q) w hw1 hw2 hw3
    rw [e, hEdef]
    by_cases hv : (C.wires (inp pstar q)).getD w false = true
    · rw [hv]
      symm
      rw [decide_eq_true_eq]
      exact ⟨w, hw, hv⟩
    · have hv' : (C.wires (inp pstar q)).getD w false = false := by simpa using hv
      rw [hv']
      symm
      rw [decide_eq_false_iff_not]
      rintro ⟨w', hw', hv2⟩
      have hww : w' = w := Finset.card_le_one.mp hent w' hw' w hw
      rw [hww, hv'] at hv2
      exact absurd hv2 (by simp)
  have htopE : ∀ p ∈ P, ∀ q, Q q → ∀ q', Q q' → E q = E q' →
      (C.wires (inp p q)).getD (N + top) false = (C.wires (inp p q')).getD (N + top) false := by
    intro p hp q hq q' hq' hEq
    exact inside_agree N C S region entry hRB hreg hS (fun k hk => (hin k hk).2) (inp p q) (inp p q')
      (hlen p q) (hlen p q') (h2 p hp q hq q' hq')
      (by intro w hw; rw [hE p hp q w hw, hE p hp q' w hw, hEq]) top htop
  have htopM : ∀ p ∈ P, ∀ q, Q q → ∀ q', Q q' → E q = false →
      (C.wires (inp p q)).getD (N + top) false = true →
      (C.wires (inp p q')).getD (N + top) false = true := by
    intro p hp q hq q' hq' hEq
    exact inside_mono N C S region entry hRB hreg hS (fun k hk => (hin k hk).1)
      (fun k hk => (hin k hk).2) (inp p q) (inp p q') (hlen p q) (hlen p q')
      (h2 p hp q hq q' hq')
      (by
        intro w hw hv
        rw [hE p hp q w hw, hEq] at hv
        exact absurd hv (by simp)) top htop
  obtain ⟨f, hfdef⟩ : ∃ f : ι → Bool × Bool, ∀ p, f p =
      (if h : ∃ q, Q q ∧ E q = false then
          (C.wires (inp p (Classical.choose h))).getD (N + top) false else false,
        if h : ∃ q, Q q ∧ E q = true then
          (C.wires (inp p (Classical.choose h))).getD (N + top) false else true) :=
    ⟨_, fun _ => rfl⟩
  have hf1 : ∀ p ∈ P, f p ≠ (true, false) := by
    intro p hp hfp
    rw [hfdef] at hfp
    by_cases h0 : ∃ q, Q q ∧ E q = false
    · by_cases h1' : ∃ q, Q q ∧ E q = true
      · rw [dif_pos h0, dif_pos h1'] at hfp
        have ha := (Prod.mk.inj hfp).1
        have hb := (Prod.mk.inj hfp).2
        have hs0 := Classical.choose_spec h0
        have hs1 := Classical.choose_spec h1'
        rw [htopM p hp _ hs0.1 _ hs1.1 hs0.2 ha] at hb
        exact absurd hb (by simp)
      · rw [dif_pos h0, dif_neg h1'] at hfp
        exact absurd (Prod.mk.inj hfp).2 (by simp)
    · rw [dif_neg h0] at hfp
      exact absurd (Prod.mk.inj hfp).1 (by simp)
  have hf2 : entry = ∅ → ∀ p ∈ P, f p = ((f p).1, true) := by
    intro he p _
    have hno : ¬ ∃ q, Q q ∧ E q = true := by
      rintro ⟨q, _, hq⟩
      rw [hEdef, decide_eq_true_eq] at hq
      obtain ⟨w, hw, _⟩ := hq
      rw [he] at hw
      exact absurd hw (Finset.notMem_empty w)
    rw [hfdef, dif_neg hno]
  have hT : ∃ T : Finset (Bool × Bool), T.card < P.card ∧ ∀ p ∈ P, f p ∈ T := by
    by_cases he : entry = ∅
    · refine ⟨{(false, true), (true, true)}, ?_, ?_⟩
      · have h0 : entry.card = 0 := by rw [he]; rfl
        have hc : ({(false, true), (true, true)} : Finset (Bool × Bool)).card = 2 := by decide
        omega
      · intro p hp
        rw [hf2 he p hp]
        cases (f p).1 <;> simp
    · refine ⟨Finset.univ.erase (true, false), ?_, ?_⟩
      · have hpos : 0 < entry.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        have hc : (Finset.univ.erase ((true, false) : Bool × Bool)).card = 3 := by decide
        omega
      · intro p hp
        exact Finset.mem_erase.mpr ⟨hf1 p hp, Finset.mem_univ _⟩
  obtain ⟨T, hTc, hTm⟩ := hT
  obtain ⟨p, hp, p', hp', hne, hfe⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hTc hTm
  refine ⟨p, hp, p', hp', hne, ?_⟩
  intro q hq
  have htq : (C.wires (inp p q)).getD (N + top) false =
      (C.wires (inp p' q)).getD (N + top) false := by
    rw [hfdef p, hfdef p'] at hfe
    by_cases hEq : E q = false
    · have h0 : ∃ q, Q q ∧ E q = false := ⟨q, hq, hEq⟩
      have hs := Classical.choose_spec h0
      rw [dif_pos h0, dif_pos h0] at hfe
      have e1 := (Prod.mk.inj hfe).1
      rw [htopE p hp q hq _ hs.1 (by rw [hEq, hs.2]),
        htopE p' hp' q hq _ hs.1 (by rw [hEq, hs.2])]
      exact e1
    · have hEq' : E q = true := by simpa using hEq
      have h1' : ∃ q, Q q ∧ E q = true := ⟨q, hq, hEq'⟩
      have hs := Classical.choose_spec h1'
      rw [dif_pos h1', dif_pos h1'] at hfe
      have e1 := (Prod.mk.inj hfe).2
      rw [htopE p hp q hq _ hs.1 (by rw [hEq', hs.2]),
        htopE p' hp' q hq _ hs.1 (by rw [hEq', hs.2])]
      exact e1
  unfold Circuit.eval
  exact after_top N C S region top hRB hout (inp p q) (inp p' q) (hlen p q) (hlen p' q)
    (h1 p hp p' hp' q) htq C.output ho1 ho2

lemma main_abs (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ) (S : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + m) (hrowS : ∀ r ∈ R, r.val ∈ S) (hcolS : ∀ c ∈ B, n + c.val ∈ S)
    (hmemS : ∀ w ∈ S, (∃ r ∈ R, w = r.val) ∨ (∃ c ∈ B, w = n + c.val))
    (hRow : ∀ firstRow secondRow : Fin n, firstRow ≠ secondRow →
      d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card)
    (hCol : ∀ firstCol secondCol : Fin m, firstCol ≠ secondCol →
      d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card)
    (hRB : ReadsBack (n + m) C) (hRep : Represents G C)
    (hreg : region ⊆ Finset.range C.size) (htop : top ∈ region) (hent : entry.card ≤ 1)
    (hentry : ∀ w ∈ entry, w < n + m + top ∧ w ∉ S ∧ ¬ (n + m ≤ w ∧ w - (n + m) ∈ region))
    (hin : ∀ k ∈ region, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ S ∨ (n + m ≤ w ∧ w - (n + m) ∈ region) ∨ w ∈ entry)
    (hout : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ S ∧ ((n + m ≤ w ∧ w - (n + m) ∈ region) → w = n + m + top))
    (ho1 : C.output ∉ S)
    (ho2 : (n + m ≤ C.output ∧ C.output - (n + m) ∈ region) → C.output = n + m + top) :
    (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  have hout' : ∀ k < C.gates.length, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ S ∧ ((n + m ≤ w ∧ w - (n + m) ∈ region) → w = n + m + top) := hout
  have hreg' : region ⊆ Finset.range C.gates.length := hreg
  constructor
  · intro hB
    by_contra hR
    have hcard : 2 + entry.card < R.card := by omega
    obtain ⟨p, hp, p', hp', hne, hagree⟩ := core (n + m) C S region entry top hRB hreg' htop hS hent
      hentry hin hout' ho1 ho2 (ι := Fin n) (κ := Fin m) R (fun c : Fin m => c ∉ B)
      (fun (a : Fin n) (c : Fin m) => oneEach a c) (fun (a : Fin n) (c : Fin m) => oneEach_length a c)
      (by
        intro a ha a' ha' c w _ hw
        rw [oneEach_getD, oneEach_getD]
        have e1 : ¬ w = a.val := fun e => hw (e ▸ hrowS a ha)
        have e2 : ¬ w = a'.val := fun e => hw (e ▸ hrowS a' ha')
        simp [e1, e2])
      (by
        intro a _ c hc c' hc' w hw
        rw [oneEach_getD, oneEach_getD]
        rcases hmemS w hw with h | h
        · obtain ⟨r, _, rfl⟩ := h
          have e1 : ¬ r.val = n + c.val := by have := r.isLt; omega
          have e2 : ¬ r.val = n + c'.val := by have := r.isLt; omega
          simp [e1, e2]
        · obtain ⟨c0, hc0, rfl⟩ := h
          have e1 : ¬ c0 = c := fun e => hc (e ▸ hc0)
          have e2 : ¬ c0 = c' := fun e => hc' (e ▸ hc0)
          have e3 : ¬ c0.val = c.val := fun e => e1 (Fin.ext e)
          have e4 : ¬ c0.val = c'.val := fun e => e2 (Fin.ext e)
          simp [e1, e2, e3, e4])
      hcard
    have hd := hRow p p' hne
    have hsub : (Finset.univ.filter (fun col => G p col ≠ G p' col)) ⊆ B := by
      intro c hc
      by_contra hcB
      have e := hagree c hcB
      rw [hRep p c, hRep p' c] at e
      exact (Finset.mem_filter.mp hc).2 e
    have := Finset.card_le_card hsub
    omega
  · intro hR
    by_contra hB
    have hcard : 2 + entry.card < B.card := by omega
    obtain ⟨p, hp, p', hp', hne, hagree⟩ := core (n + m) C S region entry top hRB hreg' htop hS hent
      hentry hin hout' ho1 ho2 (ι := Fin m) (κ := Fin n) B (fun a : Fin n => a ∉ R)
      (fun (c : Fin m) (a : Fin n) => oneEach a c) (fun (c : Fin m) (a : Fin n) => oneEach_length a c)
      (by
        intro c hc c' hc' a w _ hw
        rw [oneEach_getD, oneEach_getD]
        have e1 : ¬ w = n + c.val := fun e => hw (e ▸ hcolS c hc)
        have e2 : ¬ w = n + c'.val := fun e => hw (e ▸ hcolS c' hc')
        simp [e1, e2])
      (by
        intro c _ a ha a' ha' w hw
        rw [oneEach_getD, oneEach_getD]
        rcases hmemS w hw with h | h
        · obtain ⟨r, hr, rfl⟩ := h
          have e1 : ¬ r = a := fun e => ha (e ▸ hr)
          have e2 : ¬ r = a' := fun e => ha' (e ▸ hr)
          have e3 : ¬ r.val = a.val := fun e => e1 (Fin.ext e)
          have e4 : ¬ r.val = a'.val := fun e => e2 (Fin.ext e)
          simp [e1, e2, e3, e4]
        · obtain ⟨c0, _, rfl⟩ := h
          have e1 : ¬ n + c0.val = a.val := by have := a.isLt; omega
          have e2 : ¬ n + c0.val = a'.val := by have := a'.isLt; omega
          simp [e1, e2])
      hcard
    have hd := hCol p p' hne
    have hsub : (Finset.univ.filter (fun row => G row p ≠ G row p')) ⊆ R := by
      intro a ha
      by_contra haR
      have e := hagree a haR
      rw [hRep a p, hRep a p'] at e
      exact (Finset.mem_filter.mp ha).2 e
    have := Finset.card_le_card hsub
    omega

lemma main (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ)
    (hRow : ∀ firstRow secondRow : Fin n, firstRow ≠ secondRow →
      d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card)
    (hCol : ∀ firstCol secondCol : Fin m, firstCol ≠ secondCol →
      d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card)
    (hRB : ReadsBack (n + m) C) (hRep : Represents G C)
    (hreg : region ⊆ Finset.range C.size) (htop : top ∈ region) (hent : entry.card ≤ 1)
    (hentry : ∀ w ∈ entry, w < n + m + top ∧ w ∉ (R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)) ∧ ¬ (n + m ≤ w ∧ w - (n + m) ∈ region))
    (hin : ∀ k ∈ region, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∀ w ∈ (gateAt C k).inputs, w ∈ (R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)) ∨ (n + m ≤ w ∧ w - (n + m) ∈ region) ∨ w ∈ entry)
    (hout : ∀ k < C.size, k ∉ region → ∀ w ∈ (gateAt C k).inputs,
      w ∉ (R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)) ∧ ((n + m ≤ w ∧ w - (n + m) ∈ region) → w = n + m + top))
    (ho1 : C.output ∉ (R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)))
    (ho2 : (n + m ≤ C.output ∧ C.output - (n + m) ∈ region) → C.output = n + m + top) :
    (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  refine main_abs n m d G C R B region entry top (R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)) ?_ ?_ ?_ ?_ hRow hCol hRB hRep hreg htop hent
    hentry hin hout ho1 ho2
  · intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp h
      have := r.isLt
      omega
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp h
      have := c.isLt
      omega
  · intro r hr
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨r, hr, rfl⟩))
  · intro c hc
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨c, hc, rfl⟩))
  · intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨r, hr, rfl⟩
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨c, hc, rfl⟩

end PEqualNP.Outside.L_meta_25551_aux

theorem PEqualNP.Outside.L_meta_25551 : (∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)) := by
  intro n m d G C R B region entry top raw sources inside gate hRow hCol hRB hRep hreg htop hent hentry hin hout ho1 ho2
  exact PEqualNP.Outside.L_meta_25551_aux.main n m d G C R B region entry top hRow hCol hRB hRep hreg htop hent hentry hin hout ho1 ho2
