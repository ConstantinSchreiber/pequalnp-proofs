import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25499_aux

lemma main (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b) :
    ((Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
        (fun word => if f word then (-1 : ℤ) else 1) +
      (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s ^^^ d.setWidth b)).sum
        (fun word => if f word then (-1 : ℤ) else 1)).natAbs ≤
      2 * ((Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).filter
        (fun x => f x = f (x ^^^ d))).card := by
  have hsw : ∀ x : BitVec k, (x ^^^ d).setWidth b = x.setWidth b ^^^ d.setWidth b := by
    intro x
    ext i hi
    simp [BitVec.getElem_setWidth]
  have hinv : ∀ x : BitVec k, (x ^^^ d) ^^^ d = x := by
    intro x
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  have hbij : (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s ^^^ d.setWidth b)).sum
        (fun word => if f word then (-1 : ℤ) else 1) =
      (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
        (fun x => if f (x ^^^ d) then (-1 : ℤ) else 1) := by
    symm
    apply Finset.sum_bij (fun x _ => x ^^^ d)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hsw, hx]
    · intro x1 _ x2 _ h
      have h2 := congrArg (fun y => y ^^^ d) h
      simp only [hinv] at h2
      exact h2
    · intro y hy
      refine ⟨y ^^^ d, ?_, hinv y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hsw, hy, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    · intro x _
      rfl
  rw [hbij, ← Finset.sum_add_distrib]
  have hterm : ∀ x ∈ Finset.univ.filter (fun key : BitVec k => key.setWidth b = s),
      |(if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)| =
        if f x = f (x ^^^ d) then (2 : ℤ) else 0 := by
    intro x _
    cases f x <;> cases f (x ^^^ d) <;> simp
  have habs : |(Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
        (fun x => (if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1))| ≤
      2 * (((Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).filter
        (fun x => f x = f (x ^^^ d))).card : ℤ) := by
    calc |(Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
            (fun x => (if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1))|
        ≤ (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
            (fun x => |(if f x then (-1 : ℤ) else 1) + (if f (x ^^^ d) then (-1 : ℤ) else 1)|) :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
            (fun x => if f x = f (x ^^^ d) then (2 : ℤ) else 0) := Finset.sum_congr rfl hterm
      _ = 2 * (((Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).filter
            (fun x => f x = f (x ^^^ d))).card : ℤ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 := abs_le.mp habs
  omega

end PEqualNP.Outside.L_meta_25499_aux

theorem PEqualNP.Outside.L_meta_25499 : (∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card) := by
  intro k b f d s
  exact PEqualNP.Outside.L_meta_25499_aux.main k b f d s
