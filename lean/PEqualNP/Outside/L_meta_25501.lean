import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25501_aux

lemma core (n m a gap : ℕ) (G : Fin n → Fin n → Bool) (r0 r1 : Fin m → Fin n)
    (h00 : ∀ i j, r0 i = r0 j → i = j) (h11 : ∀ i j, r1 i = r1 j → i = j)
    (h01 : ∀ i j, r0 i ≠ r1 j)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter (fun col : Fin n => G (r0 i) col ≠ G (r1 i) col)).card ≤ a)
    (hcol : ∀ b c, b ≠ c → a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) :
    gap * m ≤ gap * (n - kept.card) + ∑ u ∈ Finset.univ \ kept, min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
  classical

  have hm : (Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)).card +
      (Finset.univ.filter (fun i : Fin m => ¬ (r0 i ∈ kept ∧ r1 i ∈ kept))).card = m := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)
    simpa using h

  have h1 : (Finset.univ.filter (fun i : Fin m => ¬ (r0 i ∈ kept ∧ r1 i ∈ kept))).card ≤
      n - kept.card := by
    have hc : (Finset.univ \ kept).card = n - kept.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ kept)]
      simp
    rw [← hc]
    apply Finset.card_le_card_of_injOn (fun i => if r0 i ∈ kept then r1 i else r0 i)
    · intro i hi
      have hi' : ¬ (r0 i ∈ kept ∧ r1 i ∈ kept) := by simpa using hi
      by_cases h : r0 i ∈ kept
      · have h2 : r1 i ∉ kept := fun h3 => hi' ⟨h, h3⟩
        simp [h, h2]
      · simp [h]
    · intro i _ j _ hij
      simp only at hij
      by_cases hi : r0 i ∈ kept <;> by_cases hj : r0 j ∈ kept <;> simp only [hi, hj, ↓reduceIte] at hij
      · exact h11 i j hij
      · exact absurd hij.symm (h01 j i)
      · exact absurd hij (h01 i j)
      · exact h00 i j hij

  have h2 : ∀ i ∈ Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept),
      gap ≤ ((Finset.univ \ kept).filter (fun t => G t (π (r0 i)) ≠ G t (π (r1 i)))).card := by
    intro i hi
    obtain ⟨k0, k1⟩ := (Finset.mem_filter.mp hi).2
    have hne : π (r0 i) ≠ π (r1 i) := fun h => h01 i i (π.injective h)
    have hc := hcol _ _ hne
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun row : Fin n => G row (π (r0 i)) ≠ G row (π (r1 i))))
      (fun t : Fin n => t ∈ kept)
    have hk : ((Finset.univ.filter (fun row : Fin n => G row (π (r0 i)) ≠ G row (π (r1 i)))).filter
        (fun t : Fin n => t ∈ kept)).card ≤ a := by
      refine le_trans ?_ (hrow i)
      apply Finset.card_le_card_of_injOn (fun t => π t)
      · intro t ht
        have ht' : G t (π (r0 i)) ≠ G t (π (r1 i)) ∧ t ∈ kept := by simpa using ht
        have e0 := hsym t ht'.2 (r0 i) k0
        have e1 := hsym t ht'.2 (r1 i) k1
        have : G (r0 i) (π t) ≠ G (r1 i) (π t) := by
          rw [← e0, ← e1]
          exact ht'.1
        simpa using this
      · intro t _ t' _ htt
        exact π.injective htt
    have hsub : ((Finset.univ.filter (fun row : Fin n => G row (π (r0 i)) ≠ G row (π (r1 i)))).filter
        (fun t : Fin n => ¬ t ∈ kept)).card ≤
        ((Finset.univ \ kept).filter (fun t => G t (π (r0 i)) ≠ G t (π (r1 i)))).card := by
      apply Finset.card_le_card
      intro t ht
      have ht' : G t (π (r0 i)) ≠ G t (π (r1 i)) ∧ ¬ t ∈ kept := by simpa using ht
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact ⟨ht'.2, ht'.1⟩
    omega

  have h3 : ∀ u ∈ Finset.univ \ kept,
      ((Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)).filter
        (fun i => G u (π (r0 i)) ≠ G u (π (r1 i)))).card ≤ min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
    intro u _
    apply le_min
    · apply Finset.card_le_card_of_injOn (fun i => if G u (π (r0 i)) = true then π (r0 i) else π (r1 i))
      · intro i hi
        have hi' : (r0 i ∈ kept ∧ r1 i ∈ kept) ∧ G u (π (r0 i)) ≠ G u (π (r1 i)) := by simpa using hi
        have hP := hi'.2
        by_cases h : G u (π (r0 i)) = true
        · simp [h]
        · have h' : G u (π (r1 i)) = true := by
            revert hP h
            cases G u (π (r0 i)) <;> cases G u (π (r1 i)) <;> simp
          simp [h, h']
      · intro i _ j _ hij
        simp only at hij
        by_cases hi : G u (π (r0 i)) = true <;> by_cases hj : G u (π (r0 j)) = true <;>
          simp only [hi, hj, ↓reduceIte] at hij
        · exact h00 i j (π.injective hij)
        · exact absurd (π.injective hij) (h01 i j)
        · exact absurd (π.injective hij).symm (h01 j i)
        · exact h11 i j (π.injective hij)
    · apply Finset.card_le_card_of_injOn (fun i => if G u (π (r0 i)) = false then π (r0 i) else π (r1 i))
      · intro i hi
        have hi' : (r0 i ∈ kept ∧ r1 i ∈ kept) ∧ G u (π (r0 i)) ≠ G u (π (r1 i)) := by simpa using hi
        have hP := hi'.2
        by_cases h : G u (π (r0 i)) = false
        · simp [h]
        · have h' : G u (π (r1 i)) = false := by
            revert hP h
            cases G u (π (r0 i)) <;> cases G u (π (r1 i)) <;> simp
          simp [h, h']
      · intro i _ j _ hij
        simp only at hij
        by_cases hi : G u (π (r0 i)) = false <;> by_cases hj : G u (π (r0 j)) = false <;>
          simp only [hi, hj, ↓reduceIte] at hij
        · exact h00 i j (π.injective hij)
        · exact absurd (π.injective hij) (h01 i j)
        · exact absurd (π.injective hij).symm (h01 j i)
        · exact h11 i j (π.injective hij)

  have hdouble : ∑ i ∈ Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept),
        ((Finset.univ \ kept).filter (fun t => G t (π (r0 i)) ≠ G t (π (r1 i)))).card =
      ∑ u ∈ Finset.univ \ kept,
        ((Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)).filter
          (fun i => G u (π (r0 i)) ≠ G u (π (r1 i)))).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hlow : gap * (Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)).card ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept),
        ((Finset.univ \ kept).filter (fun t => G t (π (r0 i)) ≠ G t (π (r1 i)))).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum h2
  have hup := Finset.sum_le_sum h3
  rw [← hdouble] at hup
  have hmul : gap * m = gap * (Finset.univ.filter (fun i : Fin m => r0 i ∈ kept ∧ r1 i ∈ kept)).card +
      gap * (Finset.univ.filter (fun i : Fin m => ¬ (r0 i ∈ kept ∧ r1 i ∈ kept))).card := by
    rw [← Nat.mul_add, hm]
  have hmono : gap * (Finset.univ.filter (fun i : Fin m => ¬ (r0 i ∈ kept ∧ r1 i ∈ kept))).card ≤
      gap * (n - kept.card) := Nat.mul_le_mul_left _ h1
  omega

lemma main (n m a gap : ℕ) (G : Fin n → Fin n → Bool) (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter
      (fun col : Fin n => G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card ≤ a)
    (hcol : ∀ b c, b ≠ c → a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) :
    gap * m ≤ gap * (n - kept.card) + ∑ u ∈ Finset.univ \ kept, min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
  apply core n m a gap G (fun i => rowPair (i, false)) (fun i => rowPair (i, true)) _ _ _ π kept hrow hcol hsym
  · intro i j h
    exact (Prod.mk.inj (rowPair.injective h)).1
  · intro i j h
    exact (Prod.mk.inj (rowPair.injective h)).1
  · intro i j h
    have h2 := (Prod.mk.inj (rowPair.injective h)).2
    exact absurd h2 (by simp)

end PEqualNP.Outside.L_meta_25501_aux

theorem PEqualNP.Outside.L_meta_25501 : (∀ (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n)),
  let rowDistance := fun (firstRow secondRow : Fin n) =>
    (Finset.univ.filter (fun col : Fin n => G firstRow col ≠ G secondRow col)).card
  let colDistance := fun (firstCol secondCol : Fin n) =>
    (Finset.univ.filter (fun row : Fin n => G row firstCol ≠ G row secondCol)).card
  let minority := fun (line : Fin n) =>
    min (Finset.univ.filter (fun onCol : Fin n => G line onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G line offCol = false)).card
  (∀ i, rowDistance (rowPair (i, false)) (rowPair (i, true)) ≤ a) →
  (∀ b c, b ≠ c → a + gap ≤ colDistance b c) →
  (∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) →
  gap * m ≤ gap * (n - kept.card) +
    ∑ u ∈ Finset.univ \ kept, minority u) := by
  intro n m a gap G rowPair π kept rowDistance colDistance minority hrow hcol hsym
  exact PEqualNP.Outside.L_meta_25501_aux.main n m a gap G rowPair π kept hrow hcol hsym
