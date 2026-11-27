import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_556_aux

theorem core (n r : ℕ) (H A : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (u : Fin r → Fin n → ℝ) (c : Fin r → Fin n → ℝ)
    (F1 : ∀ i j, A i j = ∑ k, c k j * u k i)
    (F2 : ∀ j, ∑ k, (c k j)^2 = ∑ i, (A i j)^2)
    (F3 : ∀ k, ∑ i, (u k i)^2 = 1) :
    (∑ i, ∑ j, H i j * A i j)^2 ≤ (n : ℝ) * (r : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  have F5 : ∀ k, ∑ j, (∑ i, H i j * u k i)^2 = n := by
    intro k
    calc ∑ j, (∑ i, H i j * u k i)^2
        = ∑ j, ∑ i, ∑ i', (u k i * u k i') * (H i j * H i' j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
      _ = ∑ i, ∑ i', (u k i * u k i') * ∑ j, H i j * H i' j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, (u k i)^2 * n := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp_rw [hH]
          simp [sq]
      _ = n := by rw [← Finset.sum_mul, F3, one_mul]
  have e1 : ∑ i, ∑ j, H i j * A i j = ∑ j, ∑ k, c k j * (∑ i, H i j * u k i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ∑ i, H i j * A i j = ∑ i, ∑ k, c k j * (H i j * u k i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [F1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k, c k j * (∑ i, H i j * u k i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin r))
    (fun p => c p.2 p.1) (fun p => ∑ i, H i p.1 * u p.2 i)
  simp only [Fintype.sum_prod_type] at cs
  have e2 : ∑ j, ∑ k, (c k j)^2 = ∑ i, ∑ j, (A i j)^2 := by
    rw [Finset.sum_comm (f := fun i j => (A i j)^2)]
    exact Finset.sum_congr rfl fun j _ => F2 j
  have e3 : ∑ j : Fin n, ∑ k : Fin r, (∑ i, H i j * u k i)^2 = (r : ℝ) * n := by
    rw [Finset.sum_comm]
    simp [F5]
  rw [e1]
  rw [e2, e3] at cs
  linarith

theorem main (n : ℕ) (H A : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) :
    (∑ i, ∑ j, H i j * A i j)^2 ≤ (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  let L : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let S : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (Submodule.span ℝ (Set.range A.col)).map L.toLinearMap
  have hS : Module.finrank ℝ S = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]; exact LinearEquiv.finrank_map_eq L _
  have hmem : ∀ j, L (A.col j) ∈ S := fun j =>
    Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, rfl⟩)
  let b := stdOrthonormalBasis ℝ S
  have key := core n (Module.finrank ℝ S) H A hH
    (fun k i => (b k : EuclideanSpace ℝ (Fin n)) i)
    (fun k j => inner ℝ (b k) (⟨L (A.col j), hmem j⟩ : S)) ?_ ?_ ?_
  · rw [hS] at key; exact key
  · intro i j
    have h := congrArg (fun y : S => (y : EuclideanSpace ℝ (Fin n)) i)
      (b.sum_repr' (⟨L (A.col j), hmem j⟩ : S))
    simp at h
    exact h.symm
  · intro j
    have h := b.sum_sq_norm_inner_right (⟨L (A.col j), hmem j⟩ : S)
    rw [← Submodule.norm_coe, EuclideanSpace.norm_sq_eq] at h
    simp at h
    exact h
  · intro k
    have h := b.orthonormal.1 k
    rw [← Submodule.norm_coe] at h
    have h2 := EuclideanSpace.norm_sq_eq (b k : EuclideanSpace ℝ (Fin n))
    rw [h] at h2
    simp at h2
    exact h2.symm

end PEqualNP.Outside.L_lib_556_aux

theorem PEqualNP.Outside.L_lib_556 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, ∑ j, H i j * A i j)^2 ≤
      (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2)) := by
  intro n H _ _ hH A
  exact PEqualNP.Outside.L_lib_556_aux.main n H A hH
