import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_565_aux

theorem main (n k : ℕ) (v : Fin k → Fin n → ℝ) (h : ∀ j, ∑ i, v j i * v j i = 1) :
    (k:ℝ)^2 ≤ (n:ℝ) * ∑ a, ∑ b, (∑ i, v a i * v b i)^2 := by
  have key : ∑ i : Fin n, ∑ j : Fin n, (∑ a, v a i * v a j)^2
      = ∑ a, ∑ b, (∑ i, v a i * v b i)^2 := by
    simp only [sq, Finset.sum_mul_sum]
    calc ∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin k, ∑ b : Fin k, v a i * v a j * (v b i * v b j)
        = ∑ i : Fin n, ∑ a : Fin k, ∑ j : Fin n, ∑ b : Fin k, v a i * v a j * (v b i * v b j) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ a : Fin k, ∑ i : Fin n, ∑ j : Fin n, ∑ b : Fin k, v a i * v a j * (v b i * v b j) :=
          Finset.sum_comm
      _ = ∑ a : Fin k, ∑ i : Fin n, ∑ b : Fin k, ∑ j : Fin n, v a i * v a j * (v b i * v b j) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
      _ = ∑ a : Fin k, ∑ b : Fin k, ∑ i : Fin n, ∑ j : Fin n, v a i * v a j * (v b i * v b j) :=
          Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ a : Fin k, ∑ b : Fin k, ∑ i : Fin n, ∑ j : Fin n, v a i * v b i * (v a j * v b j) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))))
          ring
  have tr : ∑ i : Fin n, ∑ a, v a i * v a i = (k:ℝ) := by
    rw [Finset.sum_comm]
    simp [h]
  have cs : (∑ i : Fin n, ∑ a, v a i * v a i)^2
      ≤ (n:ℝ) * ∑ i : Fin n, (∑ a, v a i * v a i)^2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => ∑ a, v a i * v a i)
    simpa using this
  have diag : ∑ i : Fin n, (∑ a, v a i * v a i)^2
      ≤ ∑ i : Fin n, ∑ j : Fin n, (∑ a, v a i * v a j)^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (f := fun j => (∑ a, v a i * v a j)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← key, ← tr]
  exact le_trans cs (mul_le_mul_of_nonneg_left diag (Nat.cast_nonneg n))

end PEqualNP.Outside.L_lib_565_aux

theorem PEqualNP.Outside.L_lib_565 : (∀ (n k : ℕ) (v : Fin k → Fin n → ℝ),
  let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
  (∀ j, dot (v j) (v j) = 1) →
    (k : ℝ)^2 ≤ (n : ℝ) * ∑ a, ∑ b, (dot (v a) (v b))^2) := by
  intro n k v dot h
  exact PEqualNP.Outside.L_lib_565_aux.main n k v h
