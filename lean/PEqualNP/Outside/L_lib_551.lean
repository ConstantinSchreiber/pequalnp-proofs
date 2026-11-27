import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_551_aux

theorem key (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K) (r : ℕ)
    (U V : Fin r → List (Fin q))
    (hfin : Module.Finite K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))))
    (hrank : Module.finrank K (Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))) = r)
    (hdet : (Matrix.of (fun i j : Fin r => f (U i ++ V j))).det ≠ 0)
    (u w : List (Fin q)) :
    f (u ++ w) = dotProduct (Matrix.vecMul (fun j => f (u ++ V j)) (Matrix.of (fun i j : Fin r => f (U i ++ V j)))⁻¹) (fun i => f (U i ++ w)) := by
  set ρ : List (Fin q) → List (Fin q) → K := fun u v => f (u ++ v) with hρ
  set H : Matrix (Fin r) (Fin r) K := Matrix.of (fun i j : Fin r => f (U i ++ V j)) with hH
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hli : LinearIndependent K (fun i : Fin r => ρ (U i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : Matrix.vecMul c H = 0 := by
      funext j
      have := congrFun hc (V j)
      simpa [Matrix.vecMul, dotProduct, ρ, H] using this
    have h2 : c = Matrix.vecMul (Matrix.vecMul c H) H⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
    intro i
    rw [h2, h1]; simp
  have hle : Submodule.span K (Set.range (fun i : Fin r => ρ (U i))) ≤ Submodule.span K (Set.range ρ) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨U i, rfl⟩
  have heq : Submodule.span K (Set.range (fun i : Fin r => ρ (U i))) = Submodule.span K (Set.range ρ) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_eq_card hli, hrank]; simp
  have hmem : ρ u ∈ Submodule.span K (Set.range (fun i : Fin r => ρ (U i))) := by
    rw [heq]; exact Submodule.subset_span ⟨u, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  have hcw : ∀ w, ∑ i, c i * f (U i ++ w) = f (u ++ w) := by
    intro w
    have := congrFun hc w
    simpa [ρ] using this
  have h1 : Matrix.vecMul c H = fun j => f (u ++ V j) := by
    funext j
    simpa [Matrix.vecMul, dotProduct, H] using hcw (V j)
  have h2 : c = Matrix.vecMul (fun j => f (u ++ V j)) H⁻¹ := by
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one]
  rw [← h2, ← hcw w]
  simp [dotProduct]

end PEqualNP.Outside.L_lib_551_aux

theorem PEqualNP.Outside.L_lib_551 : (∀ (K : Type) [Field K] (q : ℕ) (f : List (Fin q) → K),
  let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => f (u ++ v)))
  ∀ (r : ℕ) (U V : Fin r → List (Fin q)),
    Module.Finite K R → Module.finrank K R = r →
    let H := Matrix.of (fun i j : Fin r => f (U i ++ V j))
    H.det ≠ 0 →
    let B := fun a : Fin q =>
      Matrix.of (fun i j : Fin r => f (U i ++ [a] ++ V j)) * H⁻¹
    ∀ w : List (Fin q), f w =
      dotProduct (Matrix.vecMul (fun j => f (V j)) H⁻¹)
        (Matrix.mulVec ((w.map B).prod) (fun i => f (U i)))) := by
  intro K _ q f R r U V hfin hrank H hdet B w
  have key := fun u w => PEqualNP.Outside.L_lib_551_aux.key K q f r U V hfin hrank hdet u w
  have hg : ∀ w : List (Fin q), Matrix.mulVec ((w.map B).prod) (fun i => f (U i)) = fun i => f (U i ++ w) := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih]
      funext i
      have h := key (U i ++ [a]) w
      rw [show U i ++ a :: w = U i ++ [a] ++ w by simp, h]
      rfl
  rw [hg w]
  exact key [] w
