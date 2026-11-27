import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_548_aux

theorem bwd (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K) (d : ℕ)
    (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
    (g : (Fin d → K) →ₗ[K] K)
    (h : ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w) :
    Module.Finite K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))) ∧
    Module.finrank K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))) ≤ d := by
  have hadd : ∀ (v : List (Fin q)) (x y : Fin d → K),
      v.foldl (fun x a => A a x) (x + y)
        = v.foldl (fun x a => A a x) x + v.foldl (fun x a => A a x) y := by
    intro v
    induction v with
    | nil => intro x y; rfl
    | cons a v ih => intro x y; simp only [List.foldl_cons, map_add, ih]
  have hsmul : ∀ (v : List (Fin q)) (c : K) (x : Fin d → K),
      v.foldl (fun x a => A a x) (c • x) = c • v.foldl (fun x a => A a x) x := by
    intro v
    induction v with
    | nil => intro c x; rfl
    | cons a v ih => intro c x; simp only [List.foldl_cons, map_smul, ih]
  let Φ : (Fin d → K) →ₗ[K] (List (Fin q) → K) :=
    { toFun := fun x v => g (v.foldl (fun x a => A a x) x)
      map_add' := by
        intro x y; funext v; simp only [hadd, map_add, Pi.add_apply]
      map_smul' := by
        intro c x; funext v; simp only [hsmul, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hle : Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v))) ≤ LinearMap.range Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    refine ⟨u.foldl (fun x a => A a x) s, ?_⟩
    funext v
    show g (v.foldl (fun x a => A a x) (u.foldl (fun x a => A a x) s)) = f (u ++ v)
    rw [← h (u ++ v), List.foldl_append]
  have hfin : Module.Finite K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))) :=
    Submodule.finiteDimensional_of_le hle
  refine ⟨hfin, ?_⟩
  calc _ ≤ Module.finrank K (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K (Fin d → K) := LinearMap.finrank_range_le Φ
    _ = d := Module.finrank_fin_fun K

theorem fwd (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K) (d : ℕ)
    (hfin : Module.Finite K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))))
    (hd : Module.finrank K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))) ≤ d) :
    ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
      (g : (Fin d → K) →ₗ[K] K),
      ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w := by
  set R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v))) with hR
  obtain ⟨ι, π, hπι⟩ : ∃ (ι : R →ₗ[K] (Fin d → K)) (π : (Fin d → K) →ₗ[K] R), ∀ r, π (ι r) = r := by
    let e := (Module.finBasis K R).equivFun
    let ι' : (Fin (Module.finrank K R) → K) →ₗ[K] (Fin d → K) :=
      { toFun := fun x j => if h : j.val < Module.finrank K R then x ⟨j.val, h⟩ else 0
        map_add' := by
          intro x y; funext j
          by_cases h : j.val < Module.finrank K R <;> simp [h]
        map_smul' := by
          intro c x; funext j
          by_cases h : j.val < Module.finrank K R <;> simp [h] }
    refine ⟨ι' ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ LinearMap.funLeft K K (Fin.castLE hd), ?_⟩
    intro r
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    funext i
    simp [LinearMap.funLeft_apply, ι']
  let T : Fin q → (List (Fin q) → K) →ₗ[K] (List (Fin q) → K) :=
    fun a => LinearMap.funLeft K K (fun v => a :: v)
  have hT : ∀ a, ∀ x ∈ R, T a x ∈ R := by
    intro a
    have hc : R ≤ R.comap (T a) := by
      rw [hR, Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      refine Submodule.subset_span ⟨u ++ [a], ?_⟩
      funext v
      simp [T, LinearMap.funLeft_apply]
    exact hc
  let TR : Fin q → R →ₗ[K] R := fun a => (T a).restrict (hT a)
  let rowR : List (Fin q) → R :=
    fun u => ⟨fun v => f (u ++ v), Submodule.subset_span ⟨u, rfl⟩⟩
  have hTR : ∀ a u, TR a (rowR u) = rowR (u ++ [a]) := by
    intro a u
    apply Subtype.ext
    funext v
    simp [TR, T, rowR, LinearMap.funLeft_apply]
  have key : ∀ (w u : List (Fin q)),
      w.foldl (fun x a => ι (TR a (π x))) (ι (rowR u)) = ι (rowR (u ++ w)) := by
    intro w
    induction w with
    | nil => intro u; simp
    | cons a w ih =>
      intro u
      simp only [List.foldl_cons, hπι, hTR]
      have h2 := ih (u ++ [a])
      simp only [List.append_assoc, List.singleton_append] at h2
      exact h2
  refine ⟨ι (rowR []), fun a => ι ∘ₗ TR a ∘ₗ π, (LinearMap.proj []) ∘ₗ R.subtype ∘ₗ π, ?_⟩
  intro w
  have h3 := key w []
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [h3]
  simp [hπι, rowR]

end PEqualNP.Outside.L_lib_548_aux

theorem PEqualNP.Outside.L_lib_548 : (∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  ∀ d : ℕ, (Module.Finite K R ∧ Module.finrank K R ≤ d) ↔
    ∃ (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
      (g : (Fin d → K) →ₗ[K] K),
      ∀ w : List (Fin q), g (w.foldl (fun x a => A a x) s) = f w) := by
  intro K _ q f R d
  constructor
  · rintro ⟨hfin, hd⟩
    exact PEqualNP.Outside.L_lib_548_aux.fwd K q f d hfin hd
  · rintro ⟨s, A, g, h⟩
    exact PEqualNP.Outside.L_lib_548_aux.bwd K q f d s A g h
