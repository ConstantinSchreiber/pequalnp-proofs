import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_558_aux

theorem key (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n) (u : Fin a → ℝ) :
    ∑ j, (∑ i, u i * H (rows i) (cols j)) ^ 2 ≤ n * ∑ i, u i ^ 2 := by
  have h1 : ∑ j, (∑ i, u i * H (rows i) (cols j)) ^ 2 ≤ ∑ c, (∑ i, u i * H (rows i) c) ^ 2 := by
    rw [← Finset.sum_map Finset.univ cols (fun c => (∑ i, u i * H (rows i) c) ^ 2)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intros; positivity
  have h2 : ∑ c, (∑ i, u i * H (rows i) c) ^ 2 = n * ∑ i, u i ^ 2 := by
    calc ∑ c, (∑ i, u i * H (rows i) c) ^ 2
        = ∑ c, ∑ i, ∑ k, (u i * u k) * (H (rows i) c * H (rows k) c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ i, ∑ k, (u i * u k) * ∑ c, (H (rows i) c * H (rows k) c) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ k, (u i * u k) * (if i = k then (n : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hH]; simp [rows.injective.eq_iff]
      _ = n * ∑ i, u i ^ 2 := by
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
  linarith

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n) :
    a * b ≤ n * (H.submatrix rows cols).rank := by
  set M := H.submatrix rows cols with hM
  have hrank : (M * M.transpose).rank = M.rank := Matrix.rank_self_mul_transpose M
  have hG : (M * M.transpose).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self M
    simpa using this
  have htr : (M * M.transpose).trace = (a : ℝ) * b := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    have : ∀ i j, M i j * M i j = 1 := by
      intro i j
      rcases hpm (rows i) (cols j) with h | h <;> simp [hM, h]
    simp [this]
  have heig : ∀ i, hG.eigenvalues i ≤ n := by
    intro i
    have hv : ∑ k, (hG.eigenvectorBasis i) k ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hG.eigenvectorBasis.orthonormal.1 i]; simp
    have hk := key n H hH a b rows cols (fun k => (hG.eigenvectorBasis i) k)
    rw [hv] at hk
    rw [hG.eigenvalues_eq i]
    have e : ∀ v : Fin a → ℝ, RCLike.re (dotProduct (star v) (Matrix.mulVec (M * M.transpose) v))
        = ∑ j, (∑ k, v k * H (rows k) (cols j)) ^ 2 := by
      intro v
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      simp [dotProduct, Matrix.vecMul, sq, hM]
    rw [e]
    exact le_trans hk (le_of_eq (mul_one _))
  rw [← hrank, hG.rank_eq_card_non_zero_eigs]
  have h3 : ((a * b : ℕ) : ℝ) ≤ ((n * Fintype.card {i // hG.eigenvalues i ≠ 0} : ℕ) : ℝ) := by
    push_cast
    rw [← htr, hG.trace_eq_sum_eigenvalues]
    rw [Fintype.card_subtype]
    calc ∑ i, ((hG.eigenvalues i : ℝ) : ℝ) = ∑ i ∈ Finset.univ.filter (fun i => hG.eigenvalues i ≠ 0), hG.eigenvalues i := by
          rw [Finset.sum_filter_ne_zero]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => hG.eigenvalues i ≠ 0), (n : ℝ) :=
          Finset.sum_le_sum fun i _ => heig i
      _ = _ := by simp [mul_comm]
  exact_mod_cast h3

end PEqualNP.Outside.L_lib_558_aux

theorem PEqualNP.Outside.L_lib_558 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n),
    a * b ≤ n * (H.submatrix rows cols).rank) := by
  intro n H hn hpm hH a b rows cols
  exact PEqualNP.Outside.L_lib_558_aux.main n H hpm hH a b rows cols
