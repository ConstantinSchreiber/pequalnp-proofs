import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_560_aux

theorem key {n : ℕ} (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S)
    (h x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
    (inner ℝ h x)^2 ≤
      (∑ k, (inner ℝ (b k : EuclideanSpace ℝ (Fin n)) h)^2) * inner ℝ x x := by
  have e1 : (∑ k, inner ℝ (b k) (⟨x, hx⟩ : S) • (b k : EuclideanSpace ℝ (Fin n))) = x := by
    have := congrArg (Subtype.val) (b.sum_repr' ⟨x, hx⟩)
    simpa using this
  have e2 : inner ℝ h x =
      ∑ k, inner ℝ (b k) (⟨x, hx⟩ : S) * inner ℝ (b k : EuclideanSpace ℝ (Fin n)) h := by
    conv_lhs => rw [← e1]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right]
    congr 1
    exact real_inner_comm _ _
  have e3 : ∑ k, (inner ℝ (b k) (⟨x, hx⟩ : S))^2 = inner ℝ x x := by
    rw [b.sum_sq_inner_right, real_inner_self_eq_norm_sq]
    rfl
  rw [e2, ← e3, mul_comm]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem parseval {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (u : Fin n → ℝ) :
    ∑ i, (∑ j, H i j * u j)^2 = n * ∑ j, (u j)^2 := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  have h1 : H * H.transpose = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, hH]
  have h2 : H.transpose * H = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have h3 : H * ((n:ℝ)⁻¹ • H.transpose) = 1 := by
      rw [Matrix.mul_smul, h1, smul_smul, inv_mul_cancel₀ hn', one_smul]
    have h4 := mul_eq_one_comm.mp h3
    rw [Matrix.smul_mul] at h4
    calc H.transpose * H = (n:ℝ) • ((n:ℝ)⁻¹ • (H.transpose * H)) := by
          rw [smul_smul, mul_inv_cancel₀ hn', one_smul]
      _ = _ := by rw [h4]
  have h5 : ∑ i, (∑ j, H i j * u j)^2 = dotProduct (H.mulVec u) (H.mulVec u) := by
    simp [dotProduct, Matrix.mulVec, sq]
  have h6 : dotProduct (H.mulVec u) (H.mulVec u) = dotProduct u ((H.transpose * H).mulVec u) := by
    rw [← Matrix.mulVec_mulVec]
    conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h5, h6, h2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, sq]

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (∑ j, H i j * A i j)^2 / (∑ j, (A i j)^2)) ≤ (n : ℝ) * (A.rank : ℝ) := by
  classical
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (Submodule.span ℝ (Set.range A.row)).map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
  have hS : Module.finrank ℝ S = A.rank := by
    rw [A.rank_eq_finrank_span_row]
    exact LinearEquiv.finrank_map_eq _ _
  have hmem : ∀ i, (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)) ∈ S := by
    intro i
    exact ⟨A i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  let b := stdOrthonormalBasis ℝ S
  have hin : ∀ f g : Fin n → ℝ,
      inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 g)
        = ∑ j, f j * g j := by
    intro f g
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hb : ∀ (v : EuclideanSpace ℝ (Fin n)) (f : Fin n → ℝ),
      inner ℝ v (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n)) = ∑ j, f j * v j := by
    intro v f
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct]
  have hterm : ∀ i, (∑ j, H i j * A i j)^2 / (∑ j, (A i j)^2)
      ≤ ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2 := by
    intro i
    have hk := key S b (WithLp.toLp 2 (H i)) (WithLp.toLp 2 (A i)) (hmem i)
    rw [hin, hin] at hk
    simp only [hb] at hk
    have hsq : ∑ j, A i j * A i j = ∑ j, (A i j)^2 := by simp [sq]
    rw [hsq] at hk
    by_cases h0 : (∑ j, (A i j)^2) = 0
    · rw [h0, div_zero]; positivity
    · have hpos : 0 < ∑ j, (A i j)^2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rw [div_le_iff₀ hpos]
      exact hk
  calc (∑ i, (∑ j, H i j * A i j)^2 / (∑ j, (A i j)^2))
      ≤ ∑ i, ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2 :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ∑ k, ∑ i, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2 := Finset.sum_comm
    _ = ∑ k : Fin (Module.finrank ℝ S), (n : ℝ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [parseval H hn hH]
        have h1 : ‖(b k : EuclideanSpace ℝ (Fin n))‖ = 1 := by
          exact b.orthonormal.1 k
        have h2 : ∑ j, ((b k : EuclideanSpace ℝ (Fin n)) j)^2 = 1 := by
          have h3 := EuclideanSpace.norm_sq_eq (b k : EuclideanSpace ℝ (Fin n))
          rw [h1] at h3
          simpa using h3.symm
        rw [h2, mul_one]
    _ = n * A.rank := by simp [hS, mul_comm]

end PEqualNP.Outside.L_lib_560_aux

theorem PEqualNP.Outside.L_lib_560 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, (∑ j, H i j * A i j)^2 / (∑ j, (A i j)^2)) ≤ (n : ℝ) * (A.rank : ℝ)) := by
  intro n H hn _ hH A
  exact PEqualNP.Outside.L_lib_560_aux.main n H hn hH A
