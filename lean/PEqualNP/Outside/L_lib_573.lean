import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_573_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

noncomputable def cst (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))

lemma cst_pos (g : Gate) (gs : List Gate) (h : g.op = .and ∨ g.op = .or) :
    cst (g :: gs) = cst gs + 1 := by
  simp [cst, h]

lemma cst_neg (g : Gate) (gs : List Gate) (h : ¬ (g.op = .and ∨ g.op = .or)) :
    cst (g :: gs) = cst gs := by
  simp [cst, h]

def Aff {n : ℕ} (w : (Fin n → ZMod 2) → List Bool) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (p : Fin n → ZMod 2) : Prop :=
  ∀ wire : ℕ, ∃ (weight : Fin n → ZMod 2) (offset : ZMod 2), ∀ point : Fin n → ZMod 2,
    point - p ∈ U → (w point).getD wire false = decide (dotProduct weight point + offset = 1)

lemma Aff.mono {n : ℕ} {w : (Fin n → ZMod 2) → List Bool}
    {U U' : Submodule (ZMod 2) (Fin n → ZMod 2)} {p p' : Fin n → ZMod 2} (h : Aff w U p)
    (hs : ∀ x, x - p' ∈ U' → x - p ∈ U) : Aff w U' p' := by
  intro wire
  obtain ⟨a, b, hab⟩ := h wire
  exact ⟨a, b, fun x hx => hab x (hs x hx)⟩

lemma step_aff {n : ℕ} (g : Gate) (w : (Fin n → ZMod 2) → List Bool)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p : Fin n → ZMod 2) (L : ℕ)
    (hL : ∀ x, (w x).length = L) (hA : Aff w U p)
    (hval : ∃ (weight : Fin n → ZMod 2) (offset : ZMod 2), ∀ x : Fin n → ZMod 2, x - p ∈ U →
      g.op.eval (g.inputs.map fun i => (w x).getD i false) =
        decide (dotProduct weight x + offset = 1)) :
    Aff (fun x => stepF (w x) g) U p := by
  intro wire
  rcases lt_trichotomy wire L with h | h | h
  · obtain ⟨a, b, hab⟩ := hA wire
    refine ⟨a, b, fun x hx => ?_⟩
    rw [← hab x hx]
    simp only [stepF]
    rw [List.getD_append _ _ _ _ (by rw [hL]; exact h)]
  · obtain ⟨a, b, hab⟩ := hval
    refine ⟨a, b, fun x hx => ?_⟩
    rw [← hab x hx]
    have hw : wire = (w x).length := by rw [hL]; exact h
    rw [hw]
    simp [stepF]
  · refine ⟨0, 0, fun x hx => ?_⟩
    rw [List.getD_eq_default _ _ (by simp [stepF, hL]; omega)]
    simp

lemma z2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

lemma gate_lin {n : ℕ} (g : Gate)
    (hg : (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (w : (Fin n → ZMod 2) → List Bool) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (p : Fin n → ZMod 2) (hA : Aff w U p) :
    ∃ (weight : Fin n → ZMod 2) (offset : ZMod 2), ∀ x : Fin n → ZMod 2, x - p ∈ U →
      g.op.eval (g.inputs.map fun i => (w x).getD i false) =
        decide (dotProduct weight x + offset = 1) := by
  obtain ⟨op, ins⟩ := g
  simp only at hg ⊢
  rcases hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · subst hop
    match ins, hlen with
    | [], _ => exact ⟨0, 1, fun x _ => by simp [GateOp.eval]⟩
    | [a], _ =>
      obtain ⟨wa, oa, ha⟩ := hA a
      refine ⟨wa, oa + 1, fun x hx => ?_⟩
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [ha x hx, ← add_assoc]
      generalize dotProduct wa x + oa = s
      revert s; decide
    | [a, b], _ =>
      obtain ⟨wa, oa, ha⟩ := hA a
      obtain ⟨wb, ob, hb⟩ := hA b
      refine ⟨wa + wb, oa + ob + 1, fun x hx => ?_⟩
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [ha x hx, hb x hx, add_dotProduct]
      have e : (dotProduct wa x + dotProduct wb x + (oa + ob + 1)) =
          (dotProduct wa x + oa) + (dotProduct wb x + ob) + 1 := by ring
      rw [e]
      generalize dotProduct wa x + oa = s
      generalize dotProduct wb x + ob = t
      revert s t; decide
    | _ :: _ :: _ :: _, h => exact absurd h (by simp)
  · subst hop
    match ins, hlen with
    | [a], _ =>
      obtain ⟨wa, oa, ha⟩ := hA a
      refine ⟨wa, oa + 1, fun x hx => ?_⟩
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      rw [ha x hx, ← add_assoc]
      generalize dotProduct wa x + oa = s
      revert s; decide

lemma gate_andor {n : ℕ} (g : Gate) (hop : g.op = .and ∨ g.op = .or) (a b : ℕ)
    (hin : g.inputs = [a, b]) (w : (Fin n → ZMod 2) → List Bool)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2)) (p : Fin n → ZMod 2) (hA : Aff w U p) (c : Bool)
    (hc : ∀ x, x - p ∈ U → (w x).getD a false = c) :
    ∃ (weight : Fin n → ZMod 2) (offset : ZMod 2), ∀ x : Fin n → ZMod 2, x - p ∈ U →
      g.op.eval (g.inputs.map fun i => (w x).getD i false) =
        decide (dotProduct weight x + offset = 1) := by
  obtain ⟨wb, ob, hb⟩ := hA b
  rcases hop with hop | hop
  · cases c
    · refine ⟨0, 0, fun x hx => ?_⟩
      rw [hop, hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [hc x hx]; simp
    · refine ⟨wb, ob, fun x hx => ?_⟩
      rw [hop, hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [hc x hx, hb x hx]; simp
  · cases c
    · refine ⟨wb, ob, fun x hx => ?_⟩
      rw [hop, hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [hc x hx, hb x hx]; simp
    · refine ⟨0, 1, fun x hx => ?_⟩
      rw [hop, hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [hc x hx]; simp

def dotL {n : ℕ} (a : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := dotProduct a x
  map_add' := dotProduct_add a
  map_smul' := by intro c x; simp [dotProduct_smul]

lemma finrank_inf_ker {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) ↥(U ⊓ LinearMap.ker f) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have h4 := Submodule.finrank_le (U ⊔ LinearMap.ker f)
  omega

lemma main {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) →
    ∀ (w : (Fin n → ZMod 2) → List Bool) (L : ℕ) (U : Submodule (ZMod 2) (Fin n → ZMod 2))
      (p : Fin n → ZMod 2),
      (∀ x, (w x).length = L) → Aff w U p →
      ∃ (ι : Type) (_ : Fintype ι) (base : ι → (Fin n → ZMod 2))
        (dir : ι → Submodule (ZMod 2) (Fin n → ZMod 2)),
        Fintype.card ι ≤ 2 ^ cst gs ∧
        (∀ j, base j - p ∈ U ∧ dir j ≤ U ∧
          Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (dir j) + cst gs) ∧
        (∀ x, x - p ∈ U → ∃! j, x - base j ∈ dir j) ∧
        ∀ j, Aff (fun x => gs.foldl stepF (w x)) (dir j) (base j) := by
  induction gs with
  | nil =>
    intro _ w L U p hL hA
    exact ⟨Unit, inferInstance, fun _ => p, fun _ => U,
      by first | (simp [cst]; done) | (rw [Fintype.card_unit]; exact Nat.one_le_two_pow),
      fun _ => ⟨by simp, le_refl _, by simp⟩, fun x hx => ⟨(), hx, fun _ _ => rfl⟩, fun _ => hA⟩
  | cons g gs ih =>
    intro hsh w L U p hL hA
    have ih' := ih (fun g' hg' => hsh g' (List.mem_cons_of_mem _ hg'))
    have hL' : ∀ x, (stepF (w x) g).length = L + 1 := by intro x; simp [stepF, hL x]
    rcases hsh g (List.mem_cons_self ..) with ⟨hop, hlen⟩ | hlin
    · obtain ⟨a, b, hin⟩ : ∃ a b, g.inputs = [a, b] := by
        match hi : g.inputs, hlen with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      obtain ⟨wa, oa, ha⟩ := hA a
      rw [cst_pos g gs hop]
      by_cases hex : ∃ u ∈ U, dotProduct wa u = 1
      · obtain ⟨u0, hu0, hu01⟩ := hex
        set U' : Submodule (ZMod 2) (Fin n → ZMod 2) := U ⊓ LinearMap.ker (dotL wa) with hU'
        have hU'le : U' ≤ U := inf_le_left
        have hker : ∀ u, u ∈ U' ↔ u ∈ U ∧ dotProduct wa u = 0 := by
          intro u; simp [hU', dotL]
        have hrank : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) U' + 1 := by
          first
            | exact finrank_inf_ker U (dotL wa)
            | (rw [hU']; exact finrank_inf_ker U (dotL wa))
        have hA1 : Aff w U' p := hA.mono (fun x hx => hU'le hx)
        have hshift : ∀ x, x - (p + u0) ∈ U' → x - p ∈ U := by
          intro x hx
          have : x - p = (x - (p + u0)) + u0 := by abel
          rw [this]; exact U.add_mem (hU'le hx) hu0
        have hA2 : Aff w U' (p + u0) := hA.mono hshift
        have hc1 : ∀ x, x - p ∈ U' →
            (w x).getD a false = decide (dotProduct wa p + oa = 1) := by
          intro x hx
          rw [ha x (hU'le hx)]
          have h0 := ((hker _).1 hx).2
          rw [dotProduct_sub, sub_eq_zero] at h0
          rw [h0]
        have hc2 : ∀ x, x - (p + u0) ∈ U' →
            (w x).getD a false = decide (dotProduct wa (p + u0) + oa = 1) := by
          intro x hx
          rw [ha x (hshift x hx)]
          have h0 := ((hker _).1 hx).2
          rw [dotProduct_sub, sub_eq_zero] at h0
          rw [h0]
        have hS1 := step_aff g w U' p L hL hA1 (gate_andor g hop a b hin w U' p hA1 _ hc1)
        have hS2 := step_aff g w U' (p + u0) L hL hA2
          (gate_andor g hop a b hin w U' (p + u0) hA2 _ hc2)
        obtain ⟨ι1, f1, base1, dir1, hcard1, hprop1, huniq1, haff1⟩ :=
          ih' (fun x => stepF (w x) g) (L+1) U' p hL' hS1
        obtain ⟨ι2, f2, base2, dir2, hcard2, hprop2, huniq2, haff2⟩ :=
          ih' (fun x => stepF (w x) g) (L+1) U' (p + u0) hL' hS2
        refine ⟨ι1 ⊕ ι2, inferInstance, Sum.elim base1 base2, Sum.elim dir1 dir2, ?_, ?_, ?_, ?_⟩
        · rw [Fintype.card_sum, pow_succ]; omega
        · rintro (j | j)
          · obtain ⟨h1, h2, h3⟩ := hprop1 j
            exact ⟨hU'le h1, h2.trans hU'le, by
              show Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (dir1 j) + (cst gs + 1)
              omega⟩
          · obtain ⟨h1, h2, h3⟩ := hprop2 j
            exact ⟨hshift _ h1, h2.trans hU'le, by
              show Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (dir2 j) + (cst gs + 1)
              omega⟩
        · intro x hx
          rcases z2_cases (dotProduct wa (x - p)) with h0 | h1
          · have hxU' : x - p ∈ U' := (hker _).2 ⟨hx, h0⟩
            obtain ⟨j, hj, hju⟩ := huniq1 x hxU'
            refine ⟨Sum.inl j, hj, ?_⟩
            rintro (j' | j') hj'
            · rw [hju j' hj']
            · exfalso
              simp only [Sum.elim_inr] at hj'
              have e1 : x - (p + u0) ∈ U' := by
                have : x - (p + u0) = (x - base2 j') + (base2 j' - (p + u0)) := by abel
                rw [this]; exact U'.add_mem ((hprop2 j').2.1 hj') (hprop2 j').1
              have e2 : u0 ∈ U' := by
                have : u0 = (x - p) - (x - (p + u0)) := by abel
                rw [this]; exact U'.sub_mem hxU' e1
              have := ((hker _).1 e2).2
              rw [this] at hu01; exact zero_ne_one hu01
          · have hxU' : x - (p + u0) ∈ U' := by
              have e : x - (p + u0) = (x - p) - u0 := by abel
              refine (hker _).2 ⟨?_, ?_⟩
              · rw [e]; exact U.sub_mem hx hu0
              · rw [e, dotProduct_sub, h1, hu01, sub_self]
            obtain ⟨j, hj, hju⟩ := huniq2 x hxU'
            refine ⟨Sum.inr j, hj, ?_⟩
            rintro (j' | j') hj'
            · exfalso
              simp only [Sum.elim_inl] at hj'
              have e1 : x - p ∈ U' := by
                have : x - p = (x - base1 j') + (base1 j' - p) := by abel
                rw [this]; exact U'.add_mem ((hprop1 j').2.1 hj') (hprop1 j').1
              have := ((hker _).1 e1).2
              rw [this] at h1; exact zero_ne_one h1
            · rw [hju j' hj']
        · rintro (j | j)
          · exact haff1 j
          · exact haff2 j
      · have hex' : ∀ u ∈ U, dotProduct wa u ≠ 1 := fun u hu h => hex ⟨u, hu, h⟩
        have hc : ∀ x, x - p ∈ U →
            (w x).getD a false = decide (dotProduct wa p + oa = 1) := by
          intro x hx
          rw [ha x hx]
          have h0 : dotProduct wa (x - p) = 0 := by
            rcases z2_cases (dotProduct wa (x - p)) with h | h
            · exact h
            · exact absurd h (hex' _ hx)
          rw [dotProduct_sub, sub_eq_zero] at h0
          rw [h0]
        have hS := step_aff g w U p L hL hA (gate_andor g hop a b hin w U p hA _ hc)
        obtain ⟨ι1, f1, base1, dir1, hcard1, hprop1, huniq1, haff1⟩ :=
          ih' (fun x => stepF (w x) g) (L+1) U p hL' hS
        refine ⟨ι1, f1, base1, dir1, ?_, ?_, huniq1, haff1⟩
        · rw [pow_succ]; omega
        · intro j
          obtain ⟨h1, h2, h3⟩ := hprop1 j
          exact ⟨h1, h2, by omega⟩
    · have hneg : ¬ (g.op = .and ∨ g.op = .or) := by
        rcases hlin with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
      rw [cst_neg g gs hneg]
      have hS := step_aff g w U p L hL hA (gate_lin g hlin w U p hA)
      exact ih' (fun x => stepF (w x) g) (L+1) U p hL' hS

end PEqualNP.Outside.L_lib_573_aux

theorem PEqualNP.Outside.L_lib_573 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let K := ZMod 2
  let X := Fin n → K
  let input := fun x : X => List.ofFn (fun i : Fin n => decide (x i = 1))
  let cost := C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) →
  ∀ (U : Submodule K X) (p : X), ∃ (m : ℕ) (base : Fin m → X) (dir : Fin m → Submodule K X),
    m ≤ 2^cost ∧ (∀ j, base j - p ∈ U ∧ dir j ≤ U ∧
      Module.finrank K U ≤ Module.finrank K (dir j) + cost) ∧
    (∀ x : X, x-p ∈ U → ∃! j : Fin m, x-base j ∈ dir j) ∧
    ∀ (part : Fin m) (wire : ℕ), ∃ (weight : X) (offset : K),
      ∀ point : X, point-base part ∈ dir part →
        (C.wires (input point)).getD wire false = decide (dotProduct weight point + offset = 1)) := by
  intro n C K X input cost hRB hsh U p
  have hA : PEqualNP.Outside.L_lib_573_aux.Aff input U p := by
    intro wire
    by_cases h : wire < n
    · refine ⟨Pi.single ⟨wire, h⟩ 1, 0, fun x _ => ?_⟩
      simp [input, h]
    · refine ⟨0, 0, fun x _ => ?_⟩
      rw [List.getD_eq_default _ _ (by simp [input]; omega)]
      simp
  obtain ⟨ι, fι, base, dir, hcard, hprop, huniq, haff⟩ :=
    PEqualNP.Outside.L_lib_573_aux.main C.gates hsh input n U p (by intro x; simp [input]) hA
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => base (e.symm j), fun j => dir (e.symm j), hcard,
    fun j => hprop _, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hu⟩ := huniq x hx
    refine ⟨e i, by simpa using hi, fun j hj => ?_⟩
    have := hu (e.symm j) hj
    rw [← this]; simp
  · intro part wire
    exact haff (e.symm part) wire
