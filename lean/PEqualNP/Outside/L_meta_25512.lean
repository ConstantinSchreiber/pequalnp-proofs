import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25489
import PEqualNP.Outside.L_meta_25500

namespace PEqualNP.Outside.L_meta_25512_aux

lemma half_lt {h : ℕ} (c : Fin (2 * h)) : c.val / 2 < h := by
  have := c.isLt
  omega

lemma ones_card {r h : ℕ} (b : Fin r → Fin h → Bool) (x : Fin r) :
    (Finset.univ.filter (fun c : Fin (2 * h) =>
      (b x ⟨c.val / 2, half_lt c⟩ == c.val.testBit 0) = true)).card = h := by
  have key : (Finset.univ.filter (fun c : Fin (2 * h) =>
      (b x ⟨c.val / 2, half_lt c⟩ == c.val.testBit 0) = true)).card =
      (Finset.univ : Finset (Fin h)).card := by
    apply Finset.card_nbij' (fun c => (⟨c.val / 2, half_lt c⟩ : Fin h))
      (fun j => (⟨2 * j.val + (b x j).toNat, by
        have := j.isLt
        cases b x j <;> simp <;> omega⟩ : Fin (2 * h)))
    · intro c _
      simp
    · intro j _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      have hj : (2 * j.val + (b x j).toNat) / 2 = j.val := by
        cases b x j <;> simp <;> omega
      have e : ∀ (p : (2 * j.val + (b x j).toNat) / 2 < h),
          (⟨(2 * j.val + (b x j).toNat) / 2, p⟩ : Fin h) = j := fun p => Fin.ext hj
      rw [e]
      cases hb : b x j <;> simp [Nat.testBit_zero] <;> omega
    · intro c hc
      have hc' : (b x ⟨c.val / 2, half_lt c⟩ == c.val.testBit 0) = true := by simpa using hc
      apply Fin.ext
      simp only
      have h2 : b x ⟨c.val / 2, half_lt c⟩ = c.val.testBit 0 := by simpa using hc'
      rw [h2, Nat.testBit_zero]
      by_cases hodd : c.val % 2 = 1
      · simp [hodd]
        omega
      · simp [hodd]
        omega
    · intro j _
      apply Fin.ext
      simp only
      cases b x j <;> simp <;> omega
  rw [key]
  simp

end PEqualNP.Outside.L_meta_25512_aux

theorem PEqualNP.Outside.L_meta_25512 : (∀ (k m s : ℕ) (name : Fin m → Fin (2 ^ k)),
  2 ≤ k → 2 ≤ m → Function.Injective name →
  PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin m) (c : Fin (2 * k)) =>
      (name u).val.testBit (c.val / 2) == c.val.testBit 0) s →
  2 * m ≤ s) := by
  intro k m s name hk hm hinj hrep
  by_contra hlt
  have hs : s < 2 * m := by omega
  have h0 := PEqualNP.Outside.L_meta_25500 k m s name
  simp only [] at h0
  obtain ⟨r, h, row, coord, D, hrow, hcoord, hb, hh, hhr, hboth, hM, hRB, hRepD, hsz, hlt2, hread⟩ :=
    h0 hk hm hinj hrep hs
  have key := PEqualNP.Outside.L_meta_25489 r h
    (fun (x : Fin r) (c : Fin (2 * h)) =>
      (name (row x)).val.testBit (coord ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩).val ==
        c.val.testBit 0) D hh
    (by
      intro x y hxy
      apply hb
      funext j
      have hj : 2 * j.val < 2 * h := by have := j.isLt; omega
      have e := congrFun hxy ⟨2 * j.val, hj⟩
      have hdiv : (⟨(2 * j.val) / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt ⟨2 * j.val, hj⟩⟩ : Fin h) = j :=
        Fin.ext (by simp)
      simp only [hdiv] at e
      have ht : (2 * j.val).testBit 0 = false := by simp [Nat.testBit_zero]
      rw [ht] at e
      simpa using e)
    (by
      intro u
      exact PEqualNP.Outside.L_meta_25512_aux.ones_card
        (fun a' j' => (name (row a')).val.testBit (coord j').val) u)
    (by
      intro c
      obtain ⟨u, v, hu, hv⟩ := hboth ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩
      by_cases hc : c.val.testBit 0 = true
      · have hu' : (name (row u)).val.testBit
            (coord ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩).val = false := hu
        refine ⟨u, ?_⟩
        show ((name (row u)).val.testBit
            (coord ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩).val == c.val.testBit 0) = false
        rw [hu', hc]
        rfl
      · have hc' : c.val.testBit 0 = false := by simpa using hc
        have hv' : (name (row v)).val.testBit
            (coord ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩).val = true := hv
        refine ⟨v, ?_⟩
        show ((name (row v)).val.testBit
            (coord ⟨c.val / 2, PEqualNP.Outside.L_meta_25512_aux.half_lt c⟩).val == c.val.testBit 0) = false
        rw [hv', hc']
        rfl)
    hM hRB hRepD hread
  omega
