import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_557_aux

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

theorem lower (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (n:ℝ) * n - n * A.rank ≤ ∑ i, ∑ j, (H i j - A i j)^2 := by
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
  have hterm : ∀ i, (n:ℝ) - ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2
      ≤ ∑ j, (H i j - A i j)^2 := by
    intro i
    have hk := key S b (WithLp.toLp 2 (H i)) (WithLp.toLp 2 (A i)) (hmem i)
    rw [hin, hin] at hk
    simp only [hb] at hk
    have hsq : ∑ j, A i j * A i j = ∑ j, (A i j)^2 := by simp [sq]
    rw [hsq] at hk
    have hexp : ∑ j, (H i j - A i j)^2
        = n - 2 * (∑ j, H i j * A i j) + ∑ j, (A i j)^2 := by
      have h0 := hH i i
      rw [if_pos rfl] at h0
      rw [← h0, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hc : 0 ≤ ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2 := by positivity
    have hs : 0 ≤ ∑ j, (A i j)^2 := by positivity
    rw [hexp]
    generalize (∑ j, H i j * A i j) = t at *
    generalize (∑ j, (A i j)^2) = s at *
    generalize (∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2) = c at *
    by_contra hcon
    push_neg at hcon
    nlinarith [sq_nonneg (s - c), mul_pos (show 0 < 2*t - (s+c) by linarith)
      (show 0 < 2*t + (s+c) by linarith)]
  have hsum : ∑ i, ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2
      = n * A.rank := by
    rw [Finset.sum_comm]
    calc ∑ k, ∑ i, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2
        = ∑ k : Fin (Module.finrank ℝ S), (n : ℝ) := by
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
  calc (n:ℝ) * n - n * A.rank
      = ∑ i, ((n:ℝ) - ∑ k, (∑ j, H i j * (b k : EuclideanSpace ℝ (Fin n)) j)^2) := by
        rw [Finset.sum_sub_distrib, hsum]; simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hterm i

theorem cnt (n r : ℕ) (hr : r ≤ n) :
    ∑ i : Fin n, (if (i:ℕ) < r then (0:ℝ) else 1) = ((n - r : ℕ) : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Fin.sum_univ_add]
  simp

theorem upper (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1) (r : ℕ) (hr : r ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.rank ≤ r ∧
      ∑ i, ∑ j, (H i j - A i j)^2 = (n:ℝ) * ((n - r : ℕ) : ℝ) := by
  classical
  refine ⟨Matrix.diagonal (fun i : Fin n => if (i:ℕ) < r then (1:ℝ) else 0) * H, ?_, ?_⟩
  · refine le_trans (Matrix.rank_mul_le_left _ _) ?_
    rw [Matrix.rank_diagonal]
    have : Fintype.card {i : Fin n // (if (i:ℕ) < r then (1:ℝ) else 0) ≠ 0}
        ≤ Fintype.card (Fin r) :=
      Fintype.card_le_of_injective
        (fun x => (⟨x.1, by have := x.2; by_contra h; simp [h] at this⟩ : Fin r)) (by
        intro x y hxy
        simp only [Fin.mk.injEq] at hxy
        exact Subtype.ext (Fin.ext hxy))
    simpa using this
  · rw [← cnt n r hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diagonal_mul]
    have h1 : ∀ j, H i j ^ 2 = 1 := by
      intro j; rcases hpm i j with h | h <;> simp [h]
    by_cases h : (i:ℕ) < r
    · simp [h]
    · simp [h, h1]

end PEqualNP.Outside.L_lib_557_aux

theorem PEqualNP.Outside.L_lib_557 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ r : ℕ, r ≤ n →
    let err := fun (A : Matrix (Fin n) (Fin n) ℝ) => ∑ i, ∑ j, (H i j - A i j)^2
    let best : ℝ := n * (n-r : ℕ)
    (∀ A, A.rank ≤ r → best ≤ err A) ∧ (∃ A, A.rank ≤ r ∧ err A = best)) := by
  intro n H hn hpm hH r hr err best
  refine ⟨fun A hA => ?_, ?_⟩
  · have h1 := PEqualNP.Outside.L_lib_557_aux.lower n H hn hH A
    have h2 : (A.rank : ℝ) ≤ r := by exact_mod_cast hA
    have h3 : (best : ℝ) = n * (n - r) := by
      simp only [best]; rw [Nat.cast_sub hr]
    have h4 : (0:ℝ) ≤ n := by positivity
    show best ≤ ∑ i, ∑ j, (H i j - A i j)^2
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  · exact PEqualNP.Outside.L_lib_557_aux.upper n H hpm r hr
