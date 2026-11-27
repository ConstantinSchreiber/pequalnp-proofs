import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_593 : (∀ k : ℕ,
  let pairOK := fun p : Fin 8 × Fin 8 =>
    (p.1.val == 7) = (p.1.val.testBit 0 && p.2.val.testBit 0) ∧ p.2.val ≠ 7
  let inputs := (Fin 8 × Fin 8) × (Fin k → Fin 8)
  ((Finset.univ : Finset inputs).filter (fun x =>
    pairOK x.1 ∧ ∀ i, (x.2 i).val ≠ 7)).card = 43 * 7^k) := by
  intro k pairOK inputs
  have h1 : ((Finset.univ : Finset inputs).filter (fun x =>
      pairOK x.1 ∧ ∀ i, (x.2 i).val ≠ 7)) =
      ((Finset.univ : Finset (Fin 8 × Fin 8)).filter (fun p => pairOK p)) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset (Fin 8)).filter (fun a => a.val ≠ 7))) := by
    ext x
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Fintype.mem_piFinset]
    simp
  rw [h1, Finset.card_product, Fintype.card_piFinset]
  have h2 : ((Finset.univ : Finset (Fin 8 × Fin 8)).filter (fun p => pairOK p)).card = 43 := by
    decide
  have h3 : ((Finset.univ : Finset (Fin 8)).filter (fun a => a.val ≠ 7)).card = 7 := by
    decide
  rw [h2]
  simp [h3]
