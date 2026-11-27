import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_563_aux

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hO : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    n ≤ (Finset.univ.filter (fun i => x i ≠ 0)).card *
      (Finset.univ.filter (fun i => H.mulVec x i ≠ 0)).card := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h1 : H * H.transpose = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hO, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have h2 : H.transpose * H = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have h : H * ((n:ℝ)⁻¹ • H.transpose) = 1 := by
      rw [Matrix.mul_smul, h1, smul_smul, inv_mul_cancel₀ hn', one_smul]
    have h' := mul_eq_one_comm.mp h
    rw [Matrix.smul_mul] at h'
    have h3 : (n:ℝ) • ((n:ℝ)⁻¹ • (H.transpose * H)) = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      rw [h']
    rwa [smul_smul, mul_inv_cancel₀ hn', one_smul] at h3
  have e : H.transpose.mulVec (H.mulVec x) = (n:ℝ) • x := by
    rw [Matrix.mulVec_mulVec, h2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hd : (H.mulVec x) ⬝ᵥ (H.mulVec x) = n * (x ⬝ᵥ x) := by
    calc (H.mulVec x) ⬝ᵥ (H.mulVec x) = (Matrix.vecMul x H.transpose) ⬝ᵥ (H.mulVec x) := by
          rw [Matrix.vecMul_transpose]
      _ = x ⬝ᵥ (H.transpose.mulVec (H.mulVec x)) :=
          (Matrix.dotProduct_mulVec x H.transpose (H.mulVec x)).symm
      _ = n * (x ⬝ᵥ x) := by rw [e, dotProduct_smul, smul_eq_mul]
  set S := Finset.univ.filter (fun i => x i ≠ 0) with hS
  set T := Finset.univ.filter (fun i => H.mulVec x i ≠ 0) with hT
  set Q : ℝ := ∑ j, x j ^ 2 with hQ
  have hQpos : 0 < Q := by
    obtain ⟨j, hj0⟩ := Function.ne_iff.mp hx
    have hj : x j ≠ 0 := hj0
    have h0 : 0 < x j ^ 2 := by positivity
    calc 0 < x j ^ 2 := h0
      _ ≤ Q := Finset.single_le_sum (f := fun j => x j ^ 2) (fun k _ => sq_nonneg (x k))
          (Finset.mem_univ j)
  have hpt : ∀ i, (H.mulVec x i) ^ 2 ≤ S.card * Q := by
    intro i
    have e1 : H.mulVec x i = ∑ j ∈ S, H i j * x j := by
      rw [hS, Finset.sum_filter_of_ne]
      · rfl
      · intro j _ hj
        exact right_ne_zero_of_mul hj
    rw [e1]
    calc (∑ j ∈ S, H i j * x j) ^ 2 ≤ (∑ j ∈ S, H i j ^ 2) * ∑ j ∈ S, x j ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq S _ _
      _ = S.card * ∑ j ∈ S, x j ^ 2 := by
          congr 1
          rw [Finset.sum_congr rfl (fun j _ => show H i j ^ 2 = 1 by
            rcases hH i j with h | h <;> rw [h] <;> norm_num)]
          simp
      _ ≤ S.card * Q := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => sq_nonneg (x k))
  have hsum : (n : ℝ) * Q = ∑ i ∈ T, (H.mulVec x i) ^ 2 := by
    rw [hT, Finset.sum_filter_of_ne]
    · have h4 : (H.mulVec x) ⬝ᵥ (H.mulVec x) = ∑ i, (H.mulVec x i) ^ 2 := by
        simp [dotProduct, sq]
      rw [← h4, hd]
      simp [dotProduct, sq, hQ]
    · intro i _ hi
      simpa using hi
  have hle : (n : ℝ) * Q ≤ ((S.card * T.card : ℕ) : ℝ) * Q := by
    rw [hsum]
    calc ∑ i ∈ T, (H.mulVec x i) ^ 2 ≤ ∑ i ∈ T, (S.card * Q : ℝ) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = ((S.card * T.card : ℕ) : ℝ) * Q := by
          rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
  have hfin := le_of_mul_le_mul_right hle hQpos
  exact_mod_cast hfin

end PEqualNP.Outside.L_lib_563_aux

theorem PEqualNP.Outside.L_lib_563 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ x : Fin n → ℝ, x ≠ 0 →
    let y := H.mulVec x
    n ≤ (Finset.univ.filter (fun i => x i ≠ 0)).card *
      (Finset.univ.filter (fun i => y i ≠ 0)).card) := by
  intro n H hn hH hO x hx y
  exact PEqualNP.Outside.L_lib_563_aux.main n H hn hH hO x hx
