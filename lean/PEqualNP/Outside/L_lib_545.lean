import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_545_aux

theorem main (K : Type) [Field K] (q : ℕ) (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (z : U) (C : Fin q → U →ₗ[K] U) (h : U →ₗ[K] K)
    (hv : ∀ w : List (Fin q), w.length < Module.finrank K U →
      h (w.foldl (fun x a => C a x) z) = 0) :
    ∀ w : List (Fin q), h (w.foldl (fun x a => C a x) z) = 0 := by
  obtain ⟨Z, hZ⟩ : ∃ Z : List (Fin q) → U, Z = fun w => w.foldl (fun x a => C a x) z := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Submodule K U,
      T = fun k => Submodule.span K (Z '' {w | w.length < k}) := ⟨_, rfl⟩
  have hZc : ∀ w a, Z (w ++ [a]) = C a (Z w) := by
    intro w a
    subst hZ
    simp [List.foldl_append]
  have hmem : ∀ w k, w.length < k → Z w ∈ T k := by
    intro w k hw
    subst hT
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  have hle : ∀ k (S : Submodule K U), (∀ w, w.length < k → Z w ∈ S) → T k ≤ S := by
    intro k S hS
    subst hT
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact hS w hw
  have hmono : ∀ i j, i ≤ j → T i ≤ T j := by
    intro i j hij
    apply hle
    intro w hw
    exact hmem w j (by omega)
  have hstep : ∀ k, T (k+1) = T k → T (k+2) = T (k+1) := by
    intro k hk
    apply le_antisymm _ (hmono _ _ (by omega))
    apply hle
    intro w hw
    rcases List.eq_nil_or_concat w with rfl | ⟨w', a, rfl⟩
    · exact hmem _ _ (by simp)
    · have hw' : w'.length < k + 1 := by
        simp at hw
        omega
      have h1 : Z w' ∈ T k := hk ▸ hmem w' (k+1) hw'
      rw [List.concat_eq_append, hZc]
      have h3 : T k ≤ (T (k+1)).comap (C a) := by
        apply hle
        intro w'' hw''
        rw [Submodule.mem_comap, ← hZc]
        exact hmem _ _ (by simp; omega)
      exact h3 h1
  have hstab : ∀ k, T (k+1) = T k → ∀ j, T (k + j) = T k := by
    intro k hk j
    induction j with
    | zero => rfl
    | succ j ih =>
      have : ∀ i, T (k + i + 1) = T (k + i) := by
        intro i
        induction i with
        | zero => exact hk
        | succ i ihi => exact hstep _ ihi
      rw [← add_assoc, this j, ih]
  have hex : ∃ k, k ≤ Module.finrank K U ∧ T (k+1) = T k := by
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ k, k ≤ Module.finrank K U + 1 → k ≤ Module.finrank K (T k) := by
      intro k
      induction k with
      | zero => intro _; omega
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 : T k < T (k+1) :=
          lt_of_le_of_ne (hmono _ _ (by omega)) (fun h => hcon k (by omega) h.symm)
        have h3 := Submodule.finrank_lt_finrank_of_lt h2
        omega
    have h1 := hgrow (Module.finrank K U + 1) le_rfl
    have h2 := Submodule.finrank_le (T (Module.finrank K U + 1))
    omega
  obtain ⟨k, hkn, hk⟩ := hex
  have hker : T (Module.finrank K U) ≤ LinearMap.ker h := by
    apply hle
    intro w hw
    rw [LinearMap.mem_ker]
    subst hZ
    exact hv w hw
  intro w
  have h1 : Z w ∈ T (k + (w.length + 1)) := hmem _ _ (by omega)
  rw [hstab k hk] at h1
  have h2 := hker (hmono _ _ hkn h1)
  rw [LinearMap.mem_ker] at h2
  subst hZ
  exact h2

theorem foldProd (K : Type) [Field K] (q : ℕ) (V W : Type) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W) :
    ∀ (w : List (Fin q)) (s : V) (t : W),
      w.foldl (fun x a => ((A a).prodMap (B a)) x) (s, t) =
        (w.foldl (fun x a => A a x) s, w.foldl (fun y a => B a y) t) := by
  intro w
  induction w with
  | nil => intro s t; rfl
  | cons a w ih =>
    intro s t
    simp only [List.foldl_cons, LinearMap.prodMap_apply]
    exact ih _ _

end PEqualNP.Outside.L_lib_545_aux

theorem PEqualNP.Outside.L_lib_545 : (∀ (K : Type) [Field K] (q d e : ℕ),
  let V := Fin d → K
  let W := Fin e → K
  ∀ (s : V) (t : W) (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K),
    let X := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    let Y := fun (w : List (Fin q)) => w.foldl (fun y a => B a y) t
    (∃ w, f (X w) ≠ g (Y w)) →
      ∃ w, w.length < d + e ∧ f (X w) ≠ g (Y w)) := by
  intro K _ q d e V W s t A B f g X Y hex
  obtain ⟨w, hw⟩ := hex
  by_contra hcon
  push Not at hcon
  apply hw
  have hfr : Module.finrank K ((Fin d → K) × (Fin e → K)) = d + e := by
    simp
  have key := PEqualNP.Outside.L_lib_545_aux.main K q ((Fin d → K) × (Fin e → K)) (s, t)
    (fun a => (A a).prodMap (B a)) (f.coprod (-g)) (by
      intro w' hw'
      rw [hfr] at hw'
      rw [PEqualNP.Outside.L_lib_545_aux.foldProd]
      have := hcon w' hw'
      simp only [LinearMap.coprod_apply, LinearMap.neg_apply]
      exact add_neg_eq_zero.mpr this) w
  rw [PEqualNP.Outside.L_lib_545_aux.foldProd] at key
  simp only [LinearMap.coprod_apply, LinearMap.neg_apply] at key
  exact add_neg_eq_zero.mp key
