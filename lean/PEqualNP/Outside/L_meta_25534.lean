import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25491

namespace PEqualNP.Outside.L_meta_25534_aux

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

def cin {n m p : ℕ} (code : Fin m → Fin p → Bool) (u : Fin n) (c : Fin m) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c)

def zin (n : ℕ) {m p : ℕ} (code : Fin m → Fin p → Bool) (c : Fin m) : List Bool :=
  List.replicate n false ++ List.ofFn (code c)

lemma cin_length {n m p : ℕ} (code : Fin m → Fin p → Bool) (u : Fin n) (c : Fin m) :
    (cin code u c).length = n + p := by
  simp [cin]

lemma zin_length (n : ℕ) {m p : ℕ} (code : Fin m → Fin p → Bool) (c : Fin m) :
    (zin n code c).length = n + p := by
  simp [zin]

lemma cin_low {n m p : ℕ} (code : Fin m → Fin p → Bool) (u : Fin n) (c : Fin m) (i : ℕ)
    (h : i < n) : (cin code u c).getD i false = decide (i = u.val) := by
  unfold cin
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp [Fin.ext_iff]

lemma cin_code {n m p : ℕ} (code : Fin m → Fin p → Bool) (u : Fin n) (c : Fin m) (i : ℕ)
    (h : n ≤ i) : (cin code u c).getD i false = (List.ofFn (code c)).getD (i - n) false := by
  unfold cin
  rw [List.getD_append_right _ _ _ _ (by simpa using h)]
  simp only [List.length_ofFn]

lemma zin_low (n : ℕ) {m p : ℕ} (code : Fin m → Fin p → Bool) (c : Fin m) (i : ℕ)
    (h : i < n) : (zin n code c).getD i false = false := by
  unfold zin
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

lemma zin_code (n : ℕ) {m p : ℕ} (code : Fin m → Fin p → Bool) (c : Fin m) (i : ℕ)
    (h : n ≤ i) : (zin n code c).getD i false = (List.ofFn (code c)).getD (i - n) false := by
  unfold zin
  rw [List.getD_append_right _ _ _ _ (by simpa using h)]
  simp only [List.length_replicate]

lemma cin_self {n m p : ℕ} (code : Fin m → Fin p → Bool) (u : Fin n) (c : Fin m) :
    (cin code u c).getD u.val false = true :=
  (cin_low code u c _ u.isLt).trans (decide_eq_true rfl)

lemma cin_other {n m p : ℕ} (code : Fin m → Fin p → Bool) (u v : Fin n) (c : Fin m)
    (h : v ≠ u) : (cin code u c).getD v.val false = false :=
  (cin_low code u c _ v.isLt).trans (decide_eq_false (fun e => h (Fin.ext e)))

lemma hyc_cin {n m p : ℕ} (code : Fin m → Fin p → Bool) (v w : Fin n) (c : Fin m) :
    ∀ t, n ≤ t → (cin code v c).getD t false = true → (cin code w c).getD t false = true := by
  intro t ht h
  rw [cin_code code w c t ht]
  rw [cin_code code v c t ht] at h
  exact h

lemma hyc_zin {n m p : ℕ} (code : Fin m → Fin p → Bool) (v : Fin n) (c : Fin m) :
    ∀ t, n ≤ t → (cin code v c).getD t false = true → (zin n code c).getD t false = true := by
  intro t ht h
  rw [zin_code n code c t ht]
  rw [cin_code code v c t ht] at h
  exact h

open PEqualNP.Outside.L_meta_25491_aux in
theorem same_rep' (n m p : ℕ) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hr : ∀ (u : Fin n) (c : Fin m), C.eval (cin code u c) = G u c)
    (ht : ∃ a c, G a c = true) (hf : ∃ a c, G a c = false) (F : Finset ℕ)
    (hF : ∀ j ∈ F, j < C.gates.length ∧
      ((∃ b, ∀ q : Fin n × Fin m, (run C.gates (cin code q.1 q.2)).getD (n + p + j) false = b) ∨
      ∃ w < n + p + j, ∀ q : Fin n × Fin m,
        (run C.gates (cin code q.1 q.2)).getD (n + p + j) false =
          (run C.gates (cin code q.1 q.2)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ ReadsBack (n + p) D ∧
      D.size + F.card ≤ C.size ∧ ∀ (u : Fin n) (c : Fin m), D.eval (cin code u c) = G u c := by
  obtain ⟨D, h1, h2, h3, h4⟩ := engine (X := Fin n × Fin m) (n + p) (n + p) C
    (fun q => cin code q.1 q.2) (fun q => cin code q.1 q.2)
    (fun q => cin_length _ _ _) (fun q => cin_length _ _ _) F hC
    (fun w _ => Or.inr ⟨w, by omega, fun _ => rfl⟩)
    (by
      rintro ⟨b, hb⟩
      obtain ⟨a, c, hac⟩ := ht
      obtain ⟨a', c', hac'⟩ := hf
      have e1 : G a c = b := (hr a c).symm.trans (hb (a, c))
      have e2 : G a' c' = b := (hr a' c').symm.trans (hb (a', c'))
      rw [e1] at hac; rw [e2] at hac'; rw [hac] at hac'; exact absurd hac' (by simp)) hF
  exact ⟨D, h1, h2, h3, fun a c => (h4 (a, c)).trans (hr a c)⟩

open PEqualNP.Outside.L_meta_25491_aux in
theorem del_rep' (n m p : ℕ) (G : Fin (n + 1) → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (u : Fin (n + 1)) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hr : ∀ (a : Fin (n + 1)) (c : Fin m), C.eval (cin code a c) = G a c)
    (ht : ∃ a c, G (u.succAbove a) c = true)
    (hf : ∃ a c, G (u.succAbove a) c = false) (F : Finset ℕ)
    (hF : ∀ j ∈ F, j < C.gates.length ∧
      ((∃ b, ∀ q : Fin n × Fin m,
        (run C.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false = b) ∨
      ∃ w < n + 1 + p + j, ∀ q : Fin n × Fin m,
        (run C.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false =
        (run C.gates (cin code (u.succAbove q.1) q.2)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧
      ∀ (a : Fin n) (c : Fin m), D.eval (cin code a c) = G (u.succAbove a) c := by
  have hu := u.isLt
  obtain ⟨D, h1, _, h3, h4⟩ := engine (X := Fin n × Fin m) (n + 1 + p) (n + p) C
    (fun q => cin code (u.succAbove q.1) q.2) (fun q => cin code q.1 q.2)
    (fun q => cin_length _ _ _) (fun q => cin_length _ _ _) F hC
    (by
      intro w hw
      by_cases hrow : w < n + 1
      · rcases lt_trichotomy w u with h | h | h
        · refine Or.inr ⟨w, by omega, fun q => ?_⟩
          have hq := q.1.isLt
          rw [cin_low _ _ _ _ hrow, cin_low _ _ _ _ (by omega), decide_eq_decide, sa_val]
          split_ifs <;> omega
        · refine Or.inl ⟨false, fun q => ?_⟩
          have hq := q.1.isLt
          rw [cin_low _ _ _ _ hrow]
          simp only [decide_eq_false_iff_not]
          rw [sa_val]
          split_ifs <;> omega
        · refine Or.inr ⟨w - 1, by omega, fun q => ?_⟩
          have hq := q.1.isLt
          rw [cin_low _ _ _ _ hrow, cin_low _ _ _ _ (by omega), decide_eq_decide, sa_val]
          split_ifs <;> omega
      · refine Or.inr ⟨w - 1, by omega, fun q => ?_⟩
        rw [cin_code _ _ _ _ (by omega), cin_code _ _ _ _ (by omega)]
        congr 1
        omega)
    (by
      rintro ⟨b, hb⟩
      obtain ⟨a, c, hac⟩ := ht
      obtain ⟨a', c', hac'⟩ := hf
      have e1 : G (u.succAbove a) c = b := (hr _ c).symm.trans (hb (a, c))
      have e2 : G (u.succAbove a') c' = b := (hr _ c').symm.trans (hb (a', c'))
      rw [e1] at hac; rw [e2] at hac'; rw [hac] at hac'; exact absurd hac' (by simp)) hF
  exact ⟨D, h1, h3, fun a c => (h4 (a, c)).trans (hr _ c)⟩

lemma dom1 (n m p : ℕ) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + p) C)
    (hRep : ∀ (u : Fin n) (c : Fin m), C.eval (cin code u c) = G u c)
    (v : Fin n) (iv : ℕ) (hiv : iv < C.gates.length)
    (rdv : readsIn C (Finset.range C.gates.length) v.val = 1)
    (mv : v.val ∈ (C.gates[iv]).inputs)
    (hout : C.output ≠ v.val) (c : Fin m) (y : List Bool) (hy : y.length = n + p)
    (hyc : ∀ t, n ≤ t → (cin code v c).getD t false = true → y.getD t false = true)
    (HI : (C.wires y).getD (n + p + iv) false = true) :
    G v c = true → C.eval y = true := by
  intro hvc
  have L1 : (cin code v c).length = n + p := cin_length code v c
  have key := mtrans (n + p) C hAO hRB (cin code v c) y L1 hy (fun t => t = v.val) (C.output + 1)
    (by
      intro w _ hS h1
      by_cases hw : w < n
      · rw [cin_low code v c w hw] at h1
        simp only [decide_eq_true_eq] at h1
        exact absurd h1 hS
      · exact hyc w (by omega) h1)
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
        exact hkv (reader_unique C _ k iv rdv hk hiv ha mv))
    C.output (by omega) hout
  have r1 := hRep v c
  unfold Circuit.eval at r1 ⊢
  exact key (by rw [r1, hvc])

lemma dom2 (n m p : ℕ) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool) (C : Circuit)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hRB : ReadsBack (n + p) C)
    (hRep : ∀ (u : Fin n) (c : Fin m), C.eval (cin code u c) = G u c)
    (u : Fin n) (iu : ℕ) (hiu : iu < C.gates.length)
    (rdu : readsIn C (Finset.range C.gates.length) u.val = 1)
    (mu : u.val ∈ (C.gates[iu]).inputs)
    (hout : C.output ≠ u.val) (hout2 : C.output ≠ n + p + iu) (c : Fin m) (y : List Bool)
    (hy : y.length = n + p)
    (hyc : ∀ t, n ≤ t → (cin code u c).getD t false = true → y.getD t false = true)
    (HT : ∀ k (hk : k < C.gates.length), n + p + iu ∈ (C.gates[k]).inputs →
      (C.wires (cin code u c)).getD (n + p + k) false = true →
        (C.wires y).getD (n + p + k) false = true) :
    G u c = true → C.eval y = true := by
  intro huc
  have L1 : (cin code u c).length = n + p := cin_length code u c
  have key := mtrans (n + p) C hAO hRB (cin code u c) y L1 hy
    (fun t => t = u.val ∨ t = n + p + iu) (C.output + 1)
    (by
      intro w _ hS h1
      by_cases hw : w < n
      · rw [cin_low code u c w hw] at h1
        simp only [decide_eq_true_eq] at h1
        exact absurd (Or.inl h1) hS
      · exact hyc w (by omega) h1)
    (by
      intro k hk _ hS
      by_cases hr : n + p + iu ∈ (C.gates[k]).inputs
      · right
        exact HT k hk hr
      · left
        intro a ha e
        rcases e with e | e
        · rw [e] at ha
          have hkk : k = iu := reader_unique C _ k iu rdu hk hiu ha mu
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

lemma irrel2 (N : ℕ) (C : Circuit) (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hRB : ReadsBack N C) (A : Finset ℕ)
    (hA : ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ w ∈ A, w < N → x.getD w false = y.getD w false) → C.eval x = C.eval y)
    (x z : List Bool) (hx : x.length = N) (hz : z.length = N)
    (h : ∀ w ∈ A, x.getD w false = true → z.getD w false = true) :
    C.eval x = true → C.eval z = true := by
  intro hev
  have e := hA x (inp N (fun w => decide (w ∈ A) && x.getD w false)) hx (inp_length _ _)
    (by
      intro w hw hwN
      rw [inp_getD]
      simp [hwN, hw])
  rw [e] at hev
  unfold Circuit.eval at hev ⊢
  exact mono N C hAO hRB _ z (inp_length _ _) hz
    (by
      intro w hw
      rw [inp_getD] at hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      exact h w hw.2.1 hw.2.2) (C.output + 1) C.output (by omega) hev

lemma two_rows (n m p : ℕ) (hn2 : n = 2) (H : Fin n → Fin m → Bool)
    (code : Fin m → Fin p → Bool) (C0 : Circuit)
    (hM0 : PEqualNP.MetaComplexity.Monotone2 C0)
    (hR0 : ∀ (u : Fin n) (c : Fin m), C0.eval (cin code u c) = H u c)
    (a b : Fin n) (hab : a ≠ b) (c1 c2 : Fin m)
    (h1 : H a c1 = true) (h2 : H b c1 = false) (h3 : H b c2 = true) (h4 : H a c2 = false) :
    3 ≤ C0.size := by
  obtain ⟨C, hM, hRB, hsz, hRep⟩ := same_rep' n m p H code C0 hM0 hR0 ⟨a, c1, h1⟩ ⟨b, c1, h2⟩ ∅
    (by simp)
  have hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa using h
  obtain ⟨A, hc, hA⟩ := support' (n + p) C hRB (fun g hg => (hM g hg).2)
  have hal := a.isLt
  have hbl := b.isLt
  have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have key : ∀ (r r' : Fin n) (c c' : Fin m),
      (∀ w ∈ A, (cin code r c).getD w false = true → (cin code r' c').getD w false = true) →
      H r c = true → H r' c' = true := by
    intro r r' c c' h hrc
    rw [← hRep r c] at hrc
    rw [← hRep r' c']
    exact irrel2 (n + p) C hAO hRB A hA _ _ (cin_length code r c) (cin_length code r' c') h hrc
  have ma : a.val ∈ A := by
    by_contra h
    have h' := key a b c1 c1 (by
      intro w hw hval
      by_cases hlow : w < n
      · rw [cin_low code a c1 w hlow] at hval
        simp only [decide_eq_true_eq] at hval
        rw [hval] at hw
        exact absurd hw h
      · exact hyc_cin code a b c1 w (by omega) hval) h1
    rw [h2] at h'
    exact absurd h' (by simp)
  have mb : b.val ∈ A := by
    by_contra h
    have h' := key b a c2 c2 (by
      intro w hw hval
      by_cases hlow : w < n
      · rw [cin_low code b c2 w hlow] at hval
        simp only [decide_eq_true_eq] at hval
        rw [hval] at hw
        exact absurd hw h
      · exact hyc_cin code b a c2 w (by omega) hval) h3
    rw [h4] at h'
    exact absurd h' (by simp)
  have hcard : 4 ≤ A.card := by
    by_contra hlt
    have hmb' : b.val ∈ A.erase a.val := Finset.mem_erase.mpr ⟨fun e => hab' e.symm, mb⟩
    have e1 := Finset.card_erase_of_mem ma
    have e2 := Finset.card_erase_of_mem hmb'
    have hB : ((A.erase a.val).erase b.val).card ≤ 1 := by omega
    obtain ⟨w0, hcov⟩ : ∃ w0 : ℕ, ∀ w ∈ A, w = a.val ∨ w = b.val ∨ w = w0 := by
      by_cases hne : ((A.erase a.val).erase b.val).Nonempty
      · obtain ⟨w0, hw0⟩ := hne
        refine ⟨w0, fun w hw => ?_⟩
        by_cases ea : w = a.val
        · exact Or.inl ea
        · by_cases eb : w = b.val
          · exact Or.inr (Or.inl eb)
          · right; right
            exact Finset.card_le_one.mp hB w
              (Finset.mem_erase.mpr ⟨eb, Finset.mem_erase.mpr ⟨ea, hw⟩⟩) w0 hw0
      · refine ⟨0, fun w hw => ?_⟩
        by_cases ea : w = a.val
        · exact Or.inl ea
        · by_cases eb : w = b.val
          · exact Or.inr (Or.inl eb)
          · exact absurd ⟨w, Finset.mem_erase.mpr ⟨eb, Finset.mem_erase.mpr ⟨ea, hw⟩⟩⟩ hne
    by_cases hbit : (cin code a c1).getD w0 false = true → (cin code a c2).getD w0 false = true
    · have h' := key a a c1 c2 (by
        intro w hw hval
        rcases hcov w hw with e | e | e
        · rw [e]
          exact cin_self code a c2
        · rw [e, cin_other code a b c1 (fun e' => hab e'.symm)] at hval
          exact absurd hval (by simp)
        · rw [e] at hval ⊢
          exact hbit hval) h1
      rw [h4] at h'
      exact absurd h' (by simp)
    · have hb1 : (cin code a c1).getD w0 false = true := by
        by_contra h
        exact hbit (fun h' => absurd h' h)
      have hb2 : ¬ (cin code a c2).getD w0 false = true := fun h => hbit (fun _ => h)
      have h' := key b b c2 c1 (by
        intro w hw hval
        rcases hcov w hw with e | e | e
        · rw [e, cin_other code b a c2 hab] at hval
          exact absurd hval (by simp)
        · rw [e]
          exact cin_self code b c1
        · rw [e] at hval ⊢
          by_cases hlow : w0 < n
          · rw [cin_low code a c1 w0 hlow] at hb1
            rw [cin_low code a c2 w0 hlow] at hb2
            exact absurd hb1 hb2
          · exact absurd (hyc_cin code b a c2 w0 (by omega) hval) hb2) h3
      rw [h2] at h'
      exact absurd h' (by simp)
  unfold Circuit.size at hsz ⊢
  rw [Finset.card_empty, Nat.add_zero] at hsz
  omega

lemma norm_bound (n m p : ℕ) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (C : Circuit) (hn : 3 ≤ n)
    (hinc : ∀ u v : Fin n, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (htri : ∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (hM : PEqualNP.MetaComplexity.Monotone2 C) (hRB : ReadsBack (n + p) C)
    (hRep : ∀ (u : Fin n) (c : Fin m), C.eval (cin code u c) = G u c)
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
      (C.wires (cin code u c)).getD (n + p + (r u).val) false = true := by
    intro u c
    have L : (cin code u c).length = n + p := cin_length code u c
    have hu : (C.wires (cin code u c)).getD u.val false = true := by
      rw [wires_low C _ _ (by rw [L]; omega)]
      exact cin_self code u c
    rw [wires_gate (n + p) C hRB _ L (r u).val (r u).isLt, or_pair _ _ _ _ (ho u) (hin u), hu]
    simp
  have hout : ∀ u : Fin n, C.output ≠ u.val := by
    intro u e
    obtain ⟨c, hc⟩ := hmiss u
    have h := hRep u c
    unfold Circuit.eval at h
    rw [e, wires_low C _ _ (by rw [cin_length]; omega), cin_self code u c, hc] at h
    exact absurd h (by simp)
  have hout2 : ∀ u : Fin n, C.output ≠ n + p + (r u).val := by
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
    have HI : (C.wires (cin code u c)).getD (n + p + (r v).val) false = true := by
      rw [← e]
      exact Ion u c
    have h := dom1 n m p G code C hAO hRB hRep v (r v).val (r v).isLt (hrd v) (mu v) (hout v) c
      (cin code u c) (cin_length code u c) (hyc_cin code v u c) HI hvc
    rw [hRep u c, huc] at h
    exact absurd h (by simp)

  have hnoread : ∀ v w : Fin n, n + p + (r w).val ∉ (C.gates[(r v).val]).inputs := by
    intro v w hmem
    have hlt : n + p + (r w).val < n + p + (r v).val :=
      hRB (r v).val (r v).isLt _ (by rw [gateAt_eq C _ (r v).isLt]; exact hmem)
    have hwv : w ≠ v := by
      intro e
      rw [e] at hlt
      omega
    obtain ⟨c, hvc, hwc⟩ := hinc v w (fun e => hwv e.symm)
    have L : (cin code w c).length = n + p := cin_length code w c
    have HI : (C.wires (cin code w c)).getD (n + p + (r v).val) false = true := by
      rw [wires_gate (n + p) C hRB _ L (r v).val (r v).isLt, ho v]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
      exact ⟨_, hmem, Ion w c⟩
    have h := dom1 n m p G code C hAO hRB hRep v (r v).val (r v).isLt (hrd v) (mu v) (hout v) c
      (cin code w c) L (hyc_cin code v w c) HI hvc
    rw [hRep w c, hwc] at h
    exact absurd h (by simp)

  have hread : ∀ u : Fin n, ∃ k, k < C.gates.length ∧
      n + p + (r u).val ∈ (gateAt C k).inputs := by
    intro u
    by_contra hno
    obtain ⟨w, hwu, _⟩ := third n hn u u
    obtain ⟨c, huc, hwc⟩ := hinc u w (fun e => hwu e.symm)
    have h := dom2 n m p G code C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u)
      (hout2 u) c (cin code w c) (cin_length code w c) (hyc_cin code u w c)
      (by
        intro k hk hmem
        exact absurd ⟨k, hk, by rw [gateAt_eq C k hk]; exact hmem⟩ hno) huc
    rw [hRep w c, hwc] at h
    exact absurd h (by simp)

  have hstep4 : ∀ (u v : Fin n) (T : ℕ) (hT : T < C.gates.length), u ≠ v →
      n + p + (r u).val ∈ (C.gates[T]).inputs → n + p + (r v).val ∈ (C.gates[T]).inputs →
      ¬ (∀ k (hk : k < C.gates.length), n + p + (r u).val ∈ (C.gates[k]).inputs → k = T) := by
    intro u v T hT huv hTu hTv huniq
    have hne : n + p + (r u).val ≠ n + p + (r v).val := by
      intro e
      exact huv (hrinj u v (by omega))
    have hTin := pair_of_mem (C.gates[T]).inputs ((hM _ (List.getElem_mem hT)).2) _ _ hTu hTv hne
    rcases hAO _ (List.getElem_mem hT) with hop | hop
    ·
      obtain ⟨w, hwu, hwv⟩ := third n hn u v
      obtain ⟨c, huc, hvc, hwc⟩ := htri u v w huv (fun e => hwu e.symm) (fun e => hwv e.symm)
      have Lz : (zin n code c).length = n + p := zin_length n code c
      have Lu : (cin code u c).length = n + p := cin_length code u c

      have hz0 : C.eval (zin n code c) = false := by
        by_contra hne0
        have htr : C.eval (zin n code c) = true := by simpa using hne0
        unfold Circuit.eval at htr
        have h := mono (n + p) C hAO hRB (zin n code c) (cin code w c) Lz (cin_length code w c)
          (by
            intro a ha
            by_cases hlow : a < n
            · rw [zin_low n code c a hlow] at ha
              exact absurd ha (by simp)
            · rw [cin_code code w c a (by omega)]
              rw [zin_code n code c a (by omega)] at ha
              exact ha) (C.output + 1) C.output (by omega) htr
        have h2 := hRep w c
        unfold Circuit.eval at h2
        rw [h, hwc] at h2
        exact absurd h2 (by simp)
      by_cases hq : (C.wires (zin n code c)).getD (s v) false = true
      ·
        have HI : (C.wires (zin n code c)).getD (n + p + (r v).val) false = true := by
          rw [wires_gate (n + p) C hRB _ Lz (r v).val (r v).isLt,
            or_pair _ _ _ _ (ho v) (hin v), hq]
          simp
        have h := dom1 n m p G code C hAO hRB hRep v (r v).val (r v).isLt (hrd v) (mu v) (hout v)
          c (zin n code c) Lz (hyc_zin code v c) HI hvc
        rw [hz0] at h
        exact absurd h (by simp)
      ·
        have hq0 : (C.wires (zin n code c)).getD (s v) false = false := by simpa using hq
        have hsv_lt : s v < n + p + (r v).val :=
          hRB (r v).val (r v).isLt (s v) (by rw [gateAt_eq C _ (r v).isLt]; exact ms v)
        have hrv_lt : n + p + (r v).val < n + p + T :=
          hRB T hT _ (by rw [gateAt_eq C T hT]; exact hTv)
        have hsvu : s v ≠ u.val := by
          intro e
          have h1 := ms v
          rw [e] at h1
          have h2 := honly u (r v).val (r v).isLt h1
          exact huv (hrinj u v h2.symm)
        have hsvI : s v ≠ n + p + (r u).val := by
          intro e
          have h1 := ms v
          rw [e] at h1
          exact hnoread v u h1
        have hqx : (C.wires (cin code u c)).getD (s v) false = false := by
          by_contra hne1
          have hon1 : (C.wires (cin code u c)).getD (s v) false = true := by simpa using hne1
          have h := mtrans (n + p) C hAO hRB (cin code u c) (zin n code c) Lu Lz
            (fun t => t = u.val ∨ t = n + p + (r u).val) (n + p + T)
            (by
              intro a _ hS h1
              by_cases hlow : a < n
              · rw [cin_low code u c a hlow] at h1
                simp only [decide_eq_true_eq] at h1
                exact absurd (Or.inl h1) hS
              · exact hyc_zin code u c a (by omega) h1)
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
        have hvx : (C.wires (cin code u c)).getD v.val false = false := by
          rw [wires_low C _ _ (by rw [Lu]; omega)]
          exact cin_other code u v c (fun e => huv e.symm)
        have hIvx : (C.wires (cin code u c)).getD (n + p + (r v).val) false = false := by
          rw [wires_gate (n + p) C hRB _ Lu (r v).val (r v).isLt, or_pair _ _ _ _ (ho v) (hin v)]
          simp only [hvx, hqx, Bool.or_false]
        have h := dom2 n m p G code C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u)
          (hout2 u) c (zin n code c) Lz (hyc_zin code u c)
          (by
            intro k hk hmem hon
            have hkT : k = T := huniq k hk hmem
            rw [hkT, wires_gate (n + p) C hRB _ Lu T hT, and_pair _ _ _ _ hop hTin, hIvx] at hon
            simp at hon) huc
        rw [hz0] at h
        exact absurd h (by simp)
    ·
      obtain ⟨c, huc, hvc⟩ := hinc u v huv
      have Lv : (cin code v c).length = n + p := cin_length code v c
      have h := dom2 n m p G code C hAO hRB hRep u (r u).val (r u).isLt (hrd u) (mu u) (hout u)
        (hout2 u) c (cin code v c) Lv (hyc_cin code u v c)
        (by
          intro k hk hmem _
          have hkT : k = T := huniq k hk hmem
          rw [hkT, wires_gate (n + p) C hRB _ Lv T hT, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
          exact ⟨_, hTv, Ion v c⟩) huc
      rw [hRep v c, hvc] at h
      exact absurd h (by simp)

  obtain ⟨R, hR, hRn⟩ := rcount n C.gates.length
    (fun u k => n + p + (r u).val ∈ (gateAt C k).inputs) hread
    (by
      intro k hk u v w hu hv hw
      have hu' : n + p + (r u).val ∈ (gateAt C k).inputs := hu
      have hv' : n + p + (r v).val ∈ (gateAt C k).inputs := hv
      have hw' : n + p + (r w).val ∈ (gateAt C k).inputs := hw
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
      have hE' : n + p + (r u).val ∈ (gateAt C k).inputs := hE
      have hEv' : n + p + (r v).val ∈ (gateAt C k).inputs := hEv
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
    have hE' : n + p + (r u).val ∈ (gateAt C k).inputs := hE
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

open PEqualNP.Outside.L_meta_25491_aux in
theorem dich (n m p : ℕ) (G : Fin (n + 1) → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (C0 : Circuit) (hn : 2 ≤ n)
    (hinc : ∀ u v : Fin (n + 1), u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (hC0m : PEqualNP.MetaComplexity.Monotone2 C0)
    (hC0r : ∀ (u : Fin (n + 1)) (c : Fin m), C0.eval (cin code u c) = G u c) :
    (∃ (u : Fin (n + 1)) (D : Circuit), PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size + 2 ≤ C0.size ∧
      ∀ (a : Fin n) (c : Fin m), D.eval (cin code a c) = G (u.succAbove a) c) ∨
    (∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ C0.size ∧
      ReadsBack (n + 1 + p) C ∧
      (∀ (u : Fin (n + 1)) (c : Fin m), C.eval (cin code u c) = G u c) ∧
      ∀ u : Fin (n + 1), readsIn C (Finset.range C.size) u.val = 1 ∧
        ∃ (j : Fin C.gates.length) (w : ℕ), (C.gates.get j).op = GateOp.or ∧
          ((C.gates.get j).inputs = [u.val, w] ∨ (C.gates.get j).inputs = [w, u.val])) := by
  classical
  have ev : ∀ (C : Circuit) (x : List Bool),
      C.eval x = (run C.gates x).getD C.output false := fun _ _ => rfl
  obtain ⟨c01, hc01, hc01'⟩ := hinc ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  have ht : ∃ a c, G a c = true := ⟨_, c01, hc01⟩
  have hf : ∃ a c, G a c = false := ⟨_, c01, hc01'⟩
  obtain ⟨D0, h01, h02, h03, h04⟩ := same_rep' (n + 1) m p G code C0 hC0m hC0r ht hf ∅ (by simp)
  have hex : ∃ k, ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      ReadsBack (n + 1 + p) D ∧ D.size ≤ k ∧
      ∀ (u : Fin (n + 1)) (c : Fin m), D.eval (cin code u c) = G u c :=
    ⟨C0.size, D0, h01, h02, by simpa using h03, h04⟩
  have hs0 : Nat.find hex ≤ C0.size :=
    Nat.find_min' hex ⟨D0, h01, h02, by simpa using h03, h04⟩
  obtain ⟨D, hDm, hDb, hDs, hDr⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, PEqualNP.MetaComplexity.Monotone2 D' →
      ReadsBack (n + 1 + p) D' →
      (∀ (u : Fin (n + 1)) (c : Fin m), D'.eval (cin code u c) = G u c) →
      Nat.find hex ≤ D'.size := fun D' a b c => Nat.find_min' hex ⟨D', a, b, le_rfl, c⟩
  by_cases hgood : ∀ u : Fin (n + 1), readsIn D (Finset.range D.size) u.val = 1 ∧
      ∃ (j : Fin D.gates.length) (w : ℕ), (D.gates.get j).op = GateOp.or ∧
        ((D.gates.get j).inputs = [u.val, w] ∨ (D.gates.get j).inputs = [w, u.val])
  · exact Or.inr ⟨D, hDm, hDs.trans hs0, hDb, hDr, hgood⟩
  left
  obtain ⟨u, hu⟩ := not_forall.mp hgood
  refine ⟨u, ?_⟩
  have huN := u.isLt
  have hsa : ∀ a : Fin n, u.succAbove a ≠ u := fun a => Fin.succAbove_ne u a
  obtain ⟨cd, hcd1, hcd2⟩ := hinc (u.succAbove ⟨0, by omega⟩) (u.succAbove ⟨1, by omega⟩) (by
    intro h
    have := Fin.succAbove_right_injective h
    simp [Fin.ext_iff] at this)
  have ht' : ∃ a c, G (u.succAbove a) c = true := ⟨_, cd, hcd1⟩
  have hf' : ∃ a c, G (u.succAbove a) c = false := ⟨_, cd, hcd2⟩

  have hoffu : ∀ q : Fin n × Fin m,
      (run D.gates (cin code (u.succAbove q.1) q.2)).getD u false = false := by
    intro q
    rw [run_input _ _ _ (by rw [cin_length]; omega)]
    exact cin_other code (u.succAbove q.1) u q.2 (fun e => hsa q.1 e.symm)
  have hlenS : ∀ q : Fin n × Fin m,
      (cin code (u.succAbove q.1) q.2).length = (n + 1 + p) := fun q => cin_length _ _ _

  have readerF : ∀ j, j < D.gates.length → ∀ a ∈ (gateAt D j).inputs,
      (∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD a false = false) →
      ((∃ b, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false = b) ∨
      ∃ w < n + 1 + p + j, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false =
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD w false) := by
    intro j hj a ha hoff
    obtain ⟨hop, hl⟩ := gok D hDm j hj
    rcases shape _ hop _ hl a ha with h | ⟨w, hw, h⟩
    · exact Or.inl ⟨false, fun q => by
        rw [gv (n + 1 + p) D hDb _ (hlenS q) j hj]; exact h _ (hoff q)⟩
    · exact Or.inr ⟨w, hDb j hj w hw, fun q => by
        rw [gv (n + 1 + p) D hDb _ (hlenS q) j hj]; exact h _ (hoff q)⟩
  have fin2 : ∀ j k : ℕ, j ≠ k → j < D.gates.length → k < D.gates.length →
      ((∃ b, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false = b) ∨
      ∃ w < n + 1 + p + j, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false =
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD w false) →
      ((∃ b, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + k) false = b) ∨
      ∃ w < n + 1 + p + k, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + k) false =
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD w false) →
      ∃ D' : Circuit, PEqualNP.MetaComplexity.Monotone2 D' ∧ D'.size + 2 ≤ C0.size ∧
        ∀ (a : Fin n) (c : Fin m), D'.eval (cin code a c) = G (u.succAbove a) c := by
    intro j k hjk hj hk Fj Fk
    obtain ⟨D', h1, h2, h3⟩ := del_rep' n m p G code u D hDm hDr ht' hf' {j, k} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨hj, Fj⟩
      · exact ⟨hk, Fk⟩)
    rw [Finset.card_pair hjk] at h2
    refine ⟨D', h1, ?_, h3⟩
    have : D.size ≤ C0.size := hDs.trans hs0
    omega
  by_cases hA : ∃ j, j < D.gates.length ∧ u.val ∈ (gateAt D j).inputs
  swap
  ·
    exfalso
    push Not at hA
    obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1), v = u.succAbove ⟨0, by omega⟩ := ⟨_, rfl⟩
    have hvu : v ≠ u := by
      rw [hv]
      exact hsa _
    have le : ∀ c : Fin m, ∀ i, i ≠ u.val →
        (run D.gates (cin code u c)).getD i false = true →
        (run D.gates (cin code v c)).getD i false = true := by
      intro c i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi h
        by_cases hlo : i < (n + 1 + p)
        · rw [run_input _ _ _ (by rw [cin_length]; exact hlo)] at h ⊢
          by_cases hrow : i < n + 1
          · rw [cin_low code u c i hrow] at h
            simp only [decide_eq_true_eq] at h
            exact absurd h hi
          · exact hyc_cin code u v c i (by omega) h
        by_cases hhi : (n + 1 + p) + D.gates.length ≤ i
        · rw [past _ _ _ (by rw [cin_length]; omega)] at h
          exact absurd h (by simp)
        have hk : i - (n + 1 + p) < D.gates.length := by omega
        have hik : i = (n + 1 + p) + (i - (n + 1 + p)) := by omega
        rw [hik, gv (n + 1 + p) D hDb _ (cin_length _ _ _) _ hk] at h ⊢
        refine op_le _ (gok D hDm _ hk).1 _ _ _ (fun i' hi' => ih i' ?_ ?_) h
        · have := hDb _ hk i' hi'; omega
        · rintro rfl; exact hA _ hk hi'
    by_cases ho : D.output = u.val
    · obtain ⟨c, hc1, _⟩ := hinc v u hvu
      rw [← hDr, ev, ho, run_input _ _ _ (by rw [cin_length]; omega),
        cin_other code v u c (Ne.symm hvu)] at hc1
      exact absurd hc1 (by simp)
    · obtain ⟨c, hc1, hc2⟩ := hinc u v (Ne.symm hvu)
      rw [← hDr, ev] at hc1 hc2
      rw [le c _ ho hc1] at hc2
      exact absurd hc2 (by simp)
  obtain ⟨j, hj, hju⟩ := hA
  by_cases hB : ∃ k, k < D.gates.length ∧ k ≠ j ∧ u.val ∈ (gateAt D k).inputs
  · obtain ⟨k, hk, hkj, hku⟩ := hB
    exact fin2 j k (Ne.symm hkj) hj hk (readerF j hj _ hju hoffu) (readerF k hk _ hku hoffu)
  push Not at hB
  have hcount : readsIn D (Finset.range D.size) u.val = (gateAt D j).inputs.count u.val := by
    unfold readsIn
    refine Finset.sum_eq_single j
      (fun k hk hkj => List.count_eq_zero.mpr (hB k (Finset.mem_range.mp hk) hkj))
      (fun h => absurd (Finset.mem_range.mpr hj) h)

  have hzero : ∀ x : List Bool, x.length = (n + 1 + p) → (run D.gates x).getD u false = false →
      (run D.gates x).getD ((n + 1 + p) + j) false = false := by
    intro x hx hxu
    rw [gv (n + 1 + p) D hDb x hx j hj]
    obtain ⟨hop, hl⟩ := gok D hDm j hj
    rcases hop with hop | hop
    · rw [hop]; exact and_off _ _ hju _ hxu
    · rw [hop]
      refine or_off _ u.val
        (allu _ hl _ hju fun ⟨h1, w, h2⟩ => hu ⟨hcount.trans h1, ⟨j, hj⟩, w, ?_⟩) _ hxu
      have he : D.gates.get ⟨j, hj⟩ = gateAt D j := (List.getD_eq_getElem _ _ hj).symm
      rw [he]
      exact ⟨hop, h2⟩
  have Fj : (∃ b, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false = b) ∨
      ∃ w < n + 1 + p + j, ∀ q : Fin n × Fin m,
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD (n + 1 + p + j) false =
        (run D.gates (cin code (u.succAbove q.1) q.2)).getD w false :=
    Or.inl ⟨false, fun q => hzero _ (hlenS q) (hoffu q)⟩
  by_cases hC : ∃ k, k < D.gates.length ∧ (n + 1 + p) + j ∈ (gateAt D k).inputs
  · obtain ⟨k, hk, hkj⟩ := hC
    have hjk : j ≠ k := by
      rintro rfl
      have := hDb j hj _ hkj
      omega
    exact fin2 j k hjk hj hk Fj (readerF k hk _ hkj fun q => hzero _ (hlenS q) (hoffu q))
  push Not at hC
  exfalso
  by_cases ho : D.output = (n + 1 + p) + j
  · obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1), v = u.succAbove ⟨0, by omega⟩ := ⟨_, rfl⟩
    have hvu : v ≠ u := by
      rw [hv]
      exact hsa _
    obtain ⟨c, hc1, _⟩ := hinc v u hvu
    rw [← hDr, ev, ho, hzero _ (cin_length _ _ _) (by
      rw [run_input _ _ _ (by rw [cin_length]; omega)]
      exact cin_other code v u c (Ne.symm hvu))] at hc1
    exact absurd hc1 (by simp)
  · obtain ⟨p1, p2, p3, p4, p5⟩ := prune (n + 1 + p) D hDm hDb j hj hC ho
    obtain ⟨D'', q1, q2, q3, q4⟩ := same_rep' (n + 1) m p G code _ p1
      (fun a c => (p4 _ (cin_length _ _ _)).trans (hDr a c)) ht hf {j}
      (by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact ⟨by simpa using hj, Or.inl ⟨false, fun q => p5 _ (cin_length _ _ _)⟩⟩)
    have := hmin D'' q1 q2 q4
    rw [Finset.card_singleton, p3] at q3
    omega

lemma step (n : ℕ)
    (ih : ∀ (m p : ℕ) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool) (C : Circuit),
      2 ≤ n →
      (∀ u v : Fin n, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false) →
      (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
        ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (u : Fin n) (c : Fin m), C.eval (cin code u c) = G u c) →
      2 * n - 1 ≤ C.size)
    (m p : ℕ) (G : Fin (n + 1) → Fin m → Bool) (code : Fin m → Fin p → Bool) (C : Circuit)
    (hn : 2 ≤ n + 1)
    (hinc : ∀ u v : Fin (n + 1), u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false)
    (htri : ∀ u v w : Fin (n + 1), u ≠ v → u ≠ w → v ≠ w →
      ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false)
    (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hRep : ∀ (u : Fin (n + 1)) (c : Fin m), C.eval (cin code u c) = G u c) :
    2 * (n + 1) - 1 ≤ C.size := by
  by_cases h2 : 2 ≤ n
  · rcases dich n m p G code C h2 hinc hM hRep with
      ⟨u, D, hDm, hDs, hDr⟩ | ⟨D, hDm, hDs, hRB, hDr, hrow⟩
    · have h := ih m p (fun a c => G (u.succAbove a) c) code D h2
        (by
          intro a b hab
          exact hinc _ _ (fun e => hab (Fin.succAbove_right_injective e)))
        (by
          intro a b c hab hac hbc
          exact htri _ _ _ (fun e => hab (Fin.succAbove_right_injective e))
            (fun e => hac (Fin.succAbove_right_injective e))
            (fun e => hbc (Fin.succAbove_right_injective e))) hDm hDr
      omega
    · choose r sp hr using fun u => (hrow u).2
      have h := norm_bound (n + 1) m p G code D (by omega) hinc htri hDm hRB hDr r sp
        (fun u => (hrow u).1) (fun u => (hr u).1) (fun u => (hr u).2)
      unfold Circuit.size at hDs ⊢
      omega
  · have ha : (0 : ℕ) < n + 1 := by omega
    have hb : (1 : ℕ) < n + 1 := by omega
    have hab : (⟨0, ha⟩ : Fin (n + 1)) ≠ ⟨1, hb⟩ := by
      intro e
      have e' := congrArg Fin.val e
      simp at e'
    obtain ⟨c1, a1, a2⟩ := hinc ⟨0, ha⟩ ⟨1, hb⟩ hab
    obtain ⟨c2, b1, b2⟩ := hinc ⟨1, hb⟩ ⟨0, ha⟩ (fun e => hab e.symm)
    have h := two_rows (n + 1) m p (by omega) G code C hM hRep ⟨0, ha⟩ ⟨1, hb⟩ hab c1 c2
      a1 a2 b1 b2
    omega

end PEqualNP.Outside.L_meta_25534_aux

theorem PEqualNP.Outside.L_meta_25534 : (∀ (n m p : Nat) (G : Fin n → Fin m → Bool) (code : Fin m → Fin p → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ n →
  (∀ u v : Fin n, u ≠ v →
    ∃ c : Fin m, G u c = true ∧ G v c = false) →
  (∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
    ∃ c : Fin m, G u c = true ∧ G v c = true ∧ G w c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  (∀ (u : Fin n) (c : Fin m),
    C.eval (List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (code c)) = G u c) →
  2 * n - 1 ≤ C.size) := by
  intro n
  induction n with
  | zero =>
    intro m p G code C hn
    omega
  | succ n ih =>
    intro m p G code C hn hinc htri hM hRep
    exact PEqualNP.Outside.L_meta_25534_aux.step n ih m p G code C hn hinc htri hM hRep
