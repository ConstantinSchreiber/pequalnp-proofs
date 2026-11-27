import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_249_aux

noncomputable def cell {n c : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : (Fin n → ZMod 2) → (Fin c → ZMod 2)) (x : Fin n → ZMod 2) : Finset (Fin n → ZMod 2) :=
  @Finset.filter (Fin n → ZMod 2) (fun z => z - x ∈ W ∧ h z = h x) (Classical.decPred _) Finset.univ

theorem mem_cell {n c : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : (Fin n → ZMod 2) → (Fin c → ZMod 2)) (x z : Fin n → ZMod 2) :
    z ∈ cell W h x ↔ (z - x ∈ W ∧ h z = h x) := by
  unfold cell
  simp

open Classical in
theorem card_coset {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (x : Fin n → ZMod 2) :
    (Finset.univ.filter (fun z : Fin n → ZMod 2 => z - x ∈ S)).card
      = 2 ^ Module.finrank (ZMod 2) S := by
  have h1 : (Finset.univ.filter (fun z : Fin n → ZMod 2 => z - x ∈ S)).card
      = (Finset.univ.filter (fun z : Fin n → ZMod 2 => z ∈ S)).card := by
    refine Finset.card_nbij' (fun z => z - x) (fun w => w + x) ?_ ?_ ?_ ?_
    · intro z hz; simpa using hz
    · intro w hw; simpa using hw
    · intro z _; simp
    · intro w _; simp
  rw [h1, ← Fintype.card_subtype]
  have h2 := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [ZMod.card] at h2
  convert h2

open Classical in
theorem mid_count {n : ℕ} (U V : Submodule (ZMod 2) (Fin n → ZMod 2)) (x z : Fin n → ZMod 2) :
    (Finset.univ.filter (fun y : Fin n → ZMod 2 => x - y ∈ U ∧ y - z ∈ V)).card
      = if z - x ∈ U ⊔ V then
          2 ^ Module.finrank (ZMod 2) (U ⊓ V : Submodule (ZMod 2) (Fin n → ZMod 2)) else 0 := by
  split_ifs with hw
  · have hw' : x - z ∈ U ⊔ V := by
      have := (U ⊔ V).neg_mem hw
      simpa using this
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw'
    have hv' : v = x - z - u := eq_sub_of_add_eq' huv
    rw [← card_coset (U ⊓ V) (x - u)]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_inf]
    have e1 : y - (x - u) = u - (x - y) := by abel
    have e2 : y - (x - u) = (y - z) - v := by rw [hv']; abel
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [e1]; exact U.sub_mem hu h1
      · rw [e2]; exact V.sub_mem h2 hv
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : x - y = u - (y - (x - u)) := by abel
        rw [this]; exact U.sub_mem hu h1
      · have : y - z = (y - (x - u)) + v := by rw [hv']; abel
        rw [this]; exact V.add_mem h2 hv
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro y - ⟨hy1, hy2⟩
    apply hw
    have : z - x = -((x - y) + (y - z)) := by abel
    rw [this]
    exact (U ⊔ V).neg_mem
      ((U ⊔ V).add_mem (Submodule.mem_sup_left hy1) (Submodule.mem_sup_right hy2))

open Classical in
theorem count_eq {n a b c : ℕ} (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
    (B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2)) (p : Fin a → ZMod 2) (q : Fin b → ZMod 2)
    (h : (Fin n → ZMod 2) → (Fin c → ZMod 2)) :
    (Finset.univ.filter (fun v : Fin 3 → (Fin n → ZMod 2) =>
      A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0))).card
    = 2 ^ Module.finrank (ZMod 2)
        (LinearMap.ker A ⊓ LinearMap.ker B : Submodule (ZMod 2) (Fin n → ZMod 2))
      * ∑ x : Fin n → ZMod 2, (cell (LinearMap.ker A ⊔ LinearMap.ker B) h x).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin 3 → (Fin n → ZMod 2) => (v 0, v 2))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcell : (cell (LinearMap.ker A ⊔ LinearMap.ker B) h x).card
      = ∑ z : Fin n → ZMod 2,
          if (z - x ∈ LinearMap.ker A ⊔ LinearMap.ker B ∧ h z = h x) then 1 else 0 := by
    unfold cell
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hc : (z - x ∈ LinearMap.ker A ⊔ LinearMap.ker B ∧ h z = h x)
    · simp only [if_pos hc]
    · simp only [if_neg hc]
  rw [hcell, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hfib : (Finset.filter (fun v : Fin 3 → (Fin n → ZMod 2) => (v 0, v 2) = (x, z))
      (Finset.univ.filter (fun v : Fin 3 → (Fin n → ZMod 2) =>
      A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0)))).card
      = if h z = h x then (Finset.univ.filter (fun y : Fin n → ZMod 2 =>
          x - y ∈ LinearMap.ker A ∧ y - z ∈ LinearMap.ker B)).card else 0 := by
    split_ifs with hh
    · refine Finset.card_nbij' (fun v => v 1) (fun y => ![x, y, z]) ?_ ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          Finset.coe_filter, Set.mem_setOf_eq] at hv ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hv
        subst h4 h5
        simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact ⟨add_right_cancel h1, add_right_cancel h2⟩
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
          Set.mem_setOf_eq, LinearMap.mem_ker, map_sub, sub_eq_zero] at hy ⊢
        simp [hy.1, hy.2, hh]
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          Finset.coe_filter, Set.mem_setOf_eq] at hv
        obtain ⟨-, h4, h5⟩ := hv
        funext j
        fin_cases j <;> simp [h4, h5]
      · intro y _
        simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hxz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hv hxz
      apply hh
      rw [← hxz.1, ← hxz.2]
      exact hv.2.2
  rw [hfib, mid_count]
  by_cases h1 : h z = h x <;>
    by_cases h2 : z - x ∈ LinearMap.ker A ⊔ LinearMap.ker B <;> simp [h1, h2]

open Classical in
theorem cells_bound {n c : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : (Fin n → ZMod 2) → (Fin c → ZMod 2)) :
    2 ^ (n + (Module.finrank (ZMod 2) W - c)) ≤
      ∑ x : Fin n → ZMod 2, (cell W h x).card ∧
    (∑ x : Fin n → ZMod 2, (cell W h x).card = 2 ^ (n + (Module.finrank (ZMod 2) W - c)) ↔
      ∀ x : Fin n → ZMod 2, (cell W h x).card = 2 ^ (Module.finrank (ZMod 2) W - c)) := by
  have hcardX : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by simp
  have hback : (∀ x, (cell W h x).card = 2 ^ (Module.finrank (ZMod 2) W - c)) →
      ∑ x, (cell W h x).card = 2 ^ (n + (Module.finrank (ZMod 2) W - c)) := by
    intro hx
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ, hcardX,
      smul_eq_mul, pow_add]
  rcases le_total (Module.finrank (ZMod 2) W) c with hsc | hcs
  · have h0 : Module.finrank (ZMod 2) W - c = 0 := Nat.sub_eq_zero_of_le hsc
    rw [h0] at hback ⊢
    have hpos : ∀ x, 1 ≤ (cell W h x).card := by
      intro x
      apply Finset.card_pos.mpr
      exact ⟨x, by rw [mem_cell]; simp⟩
    have hsum1 : ∑ _x : Fin n → ZMod 2, 1 = 2 ^ (n + 0) := by simp
    refine ⟨?_, ?_, hback⟩
    · rw [← hsum1]; exact Finset.sum_le_sum fun x _ => hpos x
    · intro heq
      rw [← hsum1] at heq
      have := (Finset.sum_eq_sum_iff_of_le (fun x _ => hpos x)).mp heq.symm
      intro x
      simpa using (this x (Finset.mem_univ x)).symm
  · haveI : Fintype ((Fin n → ZMod 2) ⧸ W) := Fintype.ofFinite _
    let g : (Fin n → ZMod 2) → ((Fin n → ZMod 2) ⧸ W) × (Fin c → ZMod 2) :=
      fun x => (Submodule.Quotient.mk x, h x)
    let f : ((Fin n → ZMod 2) ⧸ W) × (Fin c → ZMod 2) → ℕ :=
      fun t => (Finset.univ.filter (fun x => g x = t)).card
    have hmf : ∀ x, (cell W h x).card = f (g x) := by
      intro x
      simp only [f, g]
      congr 1
      ext z
      rw [mem_cell]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      rw [Submodule.Quotient.eq]
    have hsum1 : ∑ t, f t = 2 ^ n := by
      rw [← hcardX, ← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)).symm
    have hsum2 : ∑ x, (cell W h x).card = ∑ t, f t * f t := by
      rw [← Finset.sum_fiberwise (s := Finset.univ) (g := g)
        (f := fun x => (cell W h x).card)]
      refine Finset.sum_congr rfl fun t _ => ?_
      have : ∀ x ∈ Finset.univ.filter (fun x => g x = t), (cell W h x).card = f t := by
        intro x hx
        rw [hmf x, (Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    have hT : Fintype.card (((Fin n → ZMod 2) ⧸ W) × (Fin c → ZMod 2))
        * (2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2
        = 2 ^ n * 2 ^ (Module.finrank (ZMod 2) W - c) := by
      have hq := Submodule.card_eq_card_quotient_mul_card W
      have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
        have h2 := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
        rw [ZMod.card] at h2
        rw [Nat.card_eq_fintype_card]
        exact h2
      rw [hW, Nat.card_eq_fintype_card, hcardX, Nat.card_eq_fintype_card] at hq
      have h2s : 2 ^ Module.finrank (ZMod 2) W
          = 2 ^ c * 2 ^ (Module.finrank (ZMod 2) W - c) := by
        rw [← pow_add, Nat.add_sub_cancel' hcs]
      have hcY : Fintype.card (Fin c → ZMod 2) = 2 ^ c := by simp
      rw [Fintype.card_prod, hcY, hq, h2s]
      ring
    have key : (∑ t, ((f t : ℤ) - 2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2)
        = (∑ x, ((cell W h x).card : ℤ)) - 2 ^ n * 2 ^ (Module.finrank (ZMod 2) W - c) := by
      have e1 : ∀ t, ((f t : ℤ) - 2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2
          = (f t : ℤ) * f t - 2 * 2 ^ (Module.finrank (ZMod 2) W - c) * f t
            + (2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2 := by
        intro t; ring
      rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      have a1 : (∑ t, (f t : ℤ) * f t) = ∑ x, ((cell W h x).card : ℤ) := by
        rw [← Nat.cast_sum, hsum2]; push_cast; rfl
      have a2 : (∑ t, (f t : ℤ)) = 2 ^ n := by
        rw [← Nat.cast_sum, hsum1]; push_cast; rfl
      have a3 : (Fintype.card (((Fin n → ZMod 2) ⧸ W) × (Fin c → ZMod 2)) : ℤ)
          * (2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2
          = 2 ^ n * 2 ^ (Module.finrank (ZMod 2) W - c) := by exact_mod_cast hT
      rw [a1, a2, a3]; ring
    have hnn : 0 ≤ ∑ t, ((f t : ℤ) - 2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2 :=
      Finset.sum_nonneg fun t _ => sq_nonneg _
    refine ⟨?_, ?_, hback⟩
    · have : (2 ^ n * 2 ^ (Module.finrank (ZMod 2) W - c) : ℤ)
          ≤ ∑ x, ((cell W h x).card : ℤ) := by linarith
      rw [pow_add]; exact_mod_cast this
    · intro heq
      have hz : ∑ t, ((f t : ℤ) - 2 ^ (Module.finrank (ZMod 2) W - c)) ^ 2 = 0 := by
        rw [key]
        have : (∑ x, ((cell W h x).card : ℤ))
            = 2 ^ n * 2 ^ (Module.finrank (ZMod 2) W - c) := by
          rw [← pow_add]; exact_mod_cast heq
        rw [this]; ring
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg _)).mp hz
      intro x
      have h3 := hall (g x) (Finset.mem_univ _)
      have h4 : (f (g x) : ℤ) = 2 ^ (Module.finrank (ZMod 2) W - c) := by
        have h5 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
        linarith
      rw [hmf x]; exact_mod_cast h4

theorem exists_L {n c : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    ∃ L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin c → ZMod 2),
      Module.finrank (ZMod 2) (W ⊓ LinearMap.ker L : Submodule (ZMod 2) (Fin n → ZMod 2))
        = Module.finrank (ZMod 2) W - c := by
  have key : ∃ φ : W →ₗ[ZMod 2] (Fin c → ZMod 2),
      Module.finrank (ZMod 2) (LinearMap.ker φ) = Module.finrank (ZMod 2) W - c := by
    let e : W ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
      LinearEquiv.ofFinrankEq _ _ (by simp)
    rcases le_total (Module.finrank (ZMod 2) W) c with hsc | hcs
    · have hsurj : Function.Surjective
          (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hsc)) :=
        LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hsc)
      obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _
        (LinearMap.range_eq_top.mpr hsurj)
      have hginj : Function.Injective g := by
        intro u v huv
        have h0 := congrArg (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hsc)) huv
        have h1 := LinearMap.congr_fun hg u
        have h2 := LinearMap.congr_fun hg v
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
        rw [h1, h2] at h0
        exact h0
      refine ⟨g.comp e.toLinearMap, ?_⟩
      have hk : LinearMap.ker (g.comp e.toLinearMap) = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact hginj.comp e.injective
      rw [hk, finrank_bot, Nat.sub_eq_zero_of_le hsc]
    · have hsurj : Function.Surjective
          (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hcs)) :=
        LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective hcs)
      refine ⟨(LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hcs)).comp e.toLinearMap, ?_⟩
      have hs2 : Function.Surjective
          ((LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hcs)).comp e.toLinearMap) :=
        hsurj.comp e.surjective
      have hr := LinearMap.finrank_range_add_finrank_ker
        ((LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE hcs)).comp e.toLinearMap)
      rw [LinearMap.range_eq_top.mpr hs2, finrank_top, Module.finrank_fin_fun] at hr
      omega
  obtain ⟨φ, hφ⟩ := key
  obtain ⟨L, hL⟩ := LinearMap.exists_extend φ
  refine ⟨L, ?_⟩
  rw [← hφ, ← hL, LinearMap.ker_comp, ← Submodule.map_comap_subtype,
    Submodule.finrank_map_subtype_eq]

open Classical in
theorem cell_linear {n c : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin c → ZMod 2)) (x : Fin n → ZMod 2) :
    (cell W (fun y => L y) x).card
      = 2 ^ Module.finrank (ZMod 2)
          (W ⊓ LinearMap.ker L : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
  rw [← card_coset (W ⊓ LinearMap.ker L) x]
  congr 1
  ext z
  rw [mem_cell]
  simp [Submodule.mem_inf, LinearMap.mem_ker, map_sub, sub_eq_zero]

end PEqualNP.Outside.L_pcx_249_aux

theorem PEqualNP.Outside.L_pcx_249 : (∀ (n a b c : ℕ),
  let K := ZMod 2
  let X := Fin n → K
  let Y := Fin c → K
  ∀ (A : X →ₗ[K] (Fin a → K)) (B : X →ₗ[K] (Fin b → K))
    (p : Fin a → K) (q : Fin b → K),
    let U := LinearMap.ker A
    let V := LinearMap.ker B
    let i := Module.finrank K (U ⊓ V : Submodule K X)
    let s := Module.finrank K (U ⊔ V : Submodule K X)
    let cells := fun (color : X → Y) (x : X) => @Finset.filter X
      (fun z : X => z - x ∈ U ⊔ V ∧ color z = color x) (Classical.decPred _) Finset.univ
    let count := fun h : X → Y => (Finset.univ.filter (fun v : Fin 3 → X =>
      A (v 0) + p = A (v 1) + p ∧ B (v 1) + q = B (v 2) + q ∧ h (v 2) = h (v 0))).card
    let optimum := 2^(n+i+(s-c))
    (∀ h : X → Y,
      count h = 2^i * ∑ x : X, (cells h x).card ∧ optimum ≤ count h ∧
      (count h = optimum ↔ ∀ x : X, (cells h x).card = 2^(s-c))) ∧
    ∃ L : X →ₗ[K] Y, count L = optimum) := by
  intro n a b c K X Y A B p q U V i s cells count optimum
  have hcount : ∀ h : X → Y, count h = 2 ^ i * ∑ x : X, (cells h x).card := by
    intro h
    have h1 := PEqualNP.Outside.L_pcx_249_aux.count_eq A B p q h
    convert h1 using 2
    exact Finset.sum_congr rfl (fun x _ => rfl)
  have hopt : optimum = 2 ^ i * 2 ^ (n + (s - c)) := by
    simp only [optimum]
    rw [← pow_add]
    congr 1
    omega
  have hi : (2 : ℕ) ^ i ≠ 0 := by positivity
  refine ⟨fun h => ?_, ?_⟩
  · have hb := PEqualNP.Outside.L_pcx_249_aux.cells_bound (U ⊔ V) h
    refine ⟨hcount h, ?_, ?_⟩
    · rw [hcount h, hopt]
      exact Nat.mul_le_mul_left _ hb.1
    · rw [hcount h, hopt, Nat.mul_right_inj hi]
      exact hb.2
  · obtain ⟨L, hL⟩ := PEqualNP.Outside.L_pcx_249_aux.exists_L (c := c) (U ⊔ V)
    refine ⟨L, ?_⟩
    have hb := PEqualNP.Outside.L_pcx_249_aux.cells_bound (U ⊔ V) (fun x => L x)
    rw [hcount, hopt, Nat.mul_right_inj hi]
    apply hb.2.mpr
    intro x
    rw [PEqualNP.Outside.L_pcx_249_aux.cell_linear, hL]
