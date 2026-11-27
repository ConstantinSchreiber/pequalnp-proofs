import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_569_aux

def loc (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

lemma loc_loc (n : ℕ) (hn : 0 < n) (k j : ℕ) :
    loc n hn ((loc n hn k).val + j) = loc n hn (k + j) := by
  apply Fin.ext
  simp only [loc]
  exact Nat.mod_add_mod k n j

lemma loc_add_n (n : ℕ) (hn : 0 < n) (k : ℕ) : loc n hn (k + n) = loc n hn k := by
  apply Fin.ext
  simp only [loc]
  exact Nat.add_mod_right k n

lemma loc_val (n : ℕ) (hn : 0 < n) (s : Fin n) : loc n hn s.val = s := by
  apply Fin.ext
  simp only [loc]
  exact Nat.mod_eq_of_lt s.2

lemma exists_rel (n : ℕ) (hn : 0 < n) (s s' : Fin n) :
    ∃ e, e < n ∧ loc n hn (s.val + e) = s' := by
  have hs := s.isLt
  have hs' := s'.isLt
  by_cases h : s.val ≤ s'.val
  · refine ⟨s'.val - s.val, by omega, ?_⟩
    rw [Nat.add_sub_cancel' h]; exact loc_val n hn s'
  · refine ⟨s'.val + n - s.val, by omega, ?_⟩
    have : s.val + (s'.val + n - s.val) = s'.val + n := by omega
    rw [this, loc_add_n]; exact loc_val n hn s'

def Z (n t : ℕ) (hn : 0 < n) (w : Fin n → Bool) (s : Fin n) : Prop :=
  ∀ j, n - t ≤ j → j < n → w (loc n hn (s.val + j)) = false

lemma sep (n h t : ℕ) (hn : 0 < n) (hht : h ≤ t) (htn : t + 3 ≤ n)
    (a b : Fin n → Bool) (s s' : Fin n)
    (ha : Z n t hn a s) (hau : ∀ x, Z n t hn a x → x = s)
    (hb : Z n t hn b s')
    (hab : ∀ j, j < n - h → a (loc n hn (s.val + j)) = b (loc n hn (s.val + j))) : a = b := by
  have hsl := s.isLt
  obtain ⟨e, he, hes⟩ := exists_rel n hn s s'
  have hss : s' = s := by
    by_cases het : e ≤ t
    · by_cases he0 : e = 0
      · subst he0; rw [← hes, Nat.add_zero]; exact loc_val n hn s
      · exfalso
        have hbs : b (loc n hn (s.val + 0)) = false := by
          have := hb (n - e) (by omega) (by omega)
          rw [← hes, loc_loc] at this
          have h2 : s.val + e + (n - e) = s.val + 0 + n := by omega
          rw [h2, loc_add_n] at this
          exact this
        have has : a (loc n hn (s.val + 0)) = false := by
          rw [hab 0 (by omega)]; exact hbs
        have hZ : Z n t hn a (loc n hn (s.val + 1)) := by
          intro j hj1 hj2
          rw [loc_loc]
          by_cases hjn : j = n - 1
          · have : s.val + 1 + j = s.val + 0 + n := by omega
            rw [this, loc_add_n]; exact has
          · have : s.val + 1 + j = s.val + (j + 1) := by omega
            rw [this]; exact ha (j+1) (by omega) (by omega)
        have := hau _ hZ
        have hv := congrArg Fin.val this
        simp only [loc] at hv
        by_cases hsn : s.val + 1 < n
        · rw [Nat.mod_eq_of_lt hsn] at hv; omega
        · have : s.val + 1 = n := by omega
          rw [this, Nat.mod_self] at hv; omega
    · have hZ : Z n t hn a s' := by
        intro j hj1 hj2
        have hbj := hb j hj1 hj2
        rw [← hes, loc_loc] at hbj ⊢
        have h2 : s.val + e + j = s.val + (e + j - n) + n := by omega
        rw [h2, loc_add_n] at hbj ⊢
        by_cases hw : e + j - n < n - h
        · rw [hab _ hw]; exact hbj
        · exact ha _ (by omega) (by omega)
      exact hau _ hZ
  rw [hss] at hb
  funext x
  obtain ⟨j, hj, hjx⟩ := exists_rel n hn s x
  rw [← hjx]
  by_cases hw : j < n - h
  · exact hab j hw
  · rw [ha j (by omega) hj, hb j (by omega) hj]

def F (n t : ℕ) (c : Fin (n - t - 2) → Bool) (j : ℕ) : Bool :=
  if j = 0 ∨ j = n - t - 1 then true
  else if h : j - 1 < n - t - 2 then c ⟨j - 1, h⟩ else false

def E (n t : ℕ) (i : Fin n) (c : Fin (n - t - 2) → Bool) : Fin n → Bool :=
  fun x => F n t c ((x.val + n - i.val) % n)

lemma rel_loc (n i j : ℕ) (hi : i < n) (hj : j < n) : ((i + j) % n + n - i) % n = j := by
  by_cases h : i + j < n
  · rw [Nat.mod_eq_of_lt h]
    have : i + j + n - i = j + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · have h1 : (i + j) % n = i + j - n := by
      rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have : i + j - n + n - i = j := by omega
    rw [this, Nat.mod_eq_of_lt hj]

lemma E_loc (n t : ℕ) (hn : 0 < n) (i : Fin n) (c : Fin (n - t - 2) → Bool) (j : ℕ)
    (hj : j < n) : E n t i c (loc n hn (i.val + j)) = F n t c j := by
  simp only [E, loc]
  rw [rel_loc n i.val j i.2 hj]

lemma F_zero (n t : ℕ) (c : Fin (n - t - 2) → Bool) : F n t c 0 = true := by
  simp [F]

lemma F_mid (n t : ℕ) (c : Fin (n - t - 2) → Bool) : F n t c (n - t - 1) = true := by
  simp [F]

lemma F_succ (n t : ℕ) (c : Fin (n - t - 2) → Bool) (k : Fin (n - t - 2)) :
    F n t c (k.val + 1) = c k := by
  have hk := k.isLt
  unfold F
  have h1 : ¬ (k.val + 1 = 0 ∨ k.val + 1 = n - t - 1) := by omega
  have h2 : k.val + 1 - 1 < n - t - 2 := by omega
  rw [if_neg h1, dif_pos h2]
  exact congrArg c (Fin.ext (by show k.val + 1 - 1 = k.val; omega))

lemma F_high (n t : ℕ) (htn : t + 3 ≤ n) (c : Fin (n - t - 2) → Bool) (j : ℕ)
    (hj : n - t ≤ j) : F n t c j = false := by
  unfold F
  have h1 : ¬ (j = 0 ∨ j = n - t - 1) := by omega
  have h2 : ¬ (j - 1 < n - t - 2) := by omega
  rw [if_neg h1, dif_neg h2]

def Run (m t : ℕ) (c : Fin m → Bool) (p : ℕ) : Prop :=
  ∀ k : Fin m, p ≤ k.val → k.val < p + t → c k = false

lemma Z_E (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n)
    (c : Fin (n - t - 2) → Bool) : Z n t hn (E n t i c) i := by
  intro j hj1 hj2
  rw [E_loc n t hn i c j hj2]
  exact F_high n t htn c j hj1

lemma uniq_E (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i s' : Fin n)
    (c : Fin (n - t - 2) → Bool)
    (hc : ∀ p, p + t ≤ n - t - 2 → ¬ Run (n - t - 2) t c p)
    (hZ : Z n t hn (E n t i c) s') : s' = i := by
  obtain ⟨e, he, hes⟩ := exists_rel n hn i s'
  by_cases he0 : e = 0
  · subst he0; rw [← hes, Nat.add_zero]; exact loc_val n hn i
  exfalso
  by_cases het : e ≤ t
  · have := hZ (n - e) (by omega) (by omega)
    rw [← hes, loc_loc] at this
    have h2 : i.val + e + (n - e) = i.val + 0 + n := by omega
    rw [h2, loc_add_n, E_loc n t hn i c 0 hn, F_zero] at this
    exact Bool.noConfusion this
  by_cases het2 : n - t ≤ e
  · have := hZ (2 * n - t - 1 - e) (by omega) (by omega)
    rw [← hes, loc_loc] at this
    have h2 : i.val + e + (2 * n - t - 1 - e) = i.val + (n - t - 1) + n := by omega
    rw [h2, loc_add_n, E_loc n t hn i c (n - t - 1) (by omega), F_mid] at this
    exact Bool.noConfusion this
  · apply hc (e - t - 1) (by omega)
    intro k hk1 hk2
    have hk3 := k.isLt
    have := hZ (k.val + 1 + n - e) (by omega) (by omega)
    rw [← hes, loc_loc] at this
    have h2 : i.val + e + (k.val + 1 + n - e) = i.val + (k.val + 1) + n := by omega
    rw [h2, loc_add_n, E_loc n t hn i c (k.val + 1) (by omega), F_succ] at this
    exact this

lemma E_inj (n t : ℕ) (hn : 0 < n) (htn : t + 3 ≤ n) (i : Fin n) :
    Function.Injective (E n t i) := by
  intro c c' h
  funext k
  have hk := k.isLt
  have := congrFun h (loc n hn (i.val + (k.val + 1)))
  rw [E_loc n t hn i c (k.val + 1) (by omega), E_loc n t hn i c' (k.val + 1) (by omega),
    F_succ, F_succ] at this
  exact this

lemma bad_card (m t p : ℕ) (hp : p + t ≤ m) (B : Finset (Fin m → Bool))
    (hB : ∀ c ∈ B, Run m t c p) : B.card * 2 ^ t ≤ 2 ^ m := by
  classical
  have key : (B ×ˢ (Finset.univ : Finset (Fin t → Bool))).card ≤
      (Finset.univ : Finset (Fin m → Bool)).card := by
    apply Finset.card_le_card_of_injOn
      (fun cd : (Fin m → Bool) × (Fin t → Bool) => fun x : Fin m =>
        if hx : p ≤ x.val ∧ x.val < p + t then cd.2 ⟨x.val - p, by omega⟩ else cd.1 x)
    · intro _ _; exact Finset.mem_univ _
    · rintro ⟨c, d⟩ hcd ⟨c', d'⟩ hcd' heq
      have hc := hB c (Finset.mem_product.mp (Finset.mem_coe.mp hcd)).1
      have hc' := hB c' (Finset.mem_product.mp (Finset.mem_coe.mp hcd')).1
      have h1 : c = c' := by
        funext x
        by_cases hx : p ≤ x.val ∧ x.val < p + t
        · rw [hc x hx.1 hx.2, hc' x hx.1 hx.2]
        · have := congrFun heq x
          simp only [dif_neg hx] at this
          exact this
      have h2 : d = d' := by
        funext k
        have hk3 := k.isLt
        have hk : p ≤ p + k.val ∧ p + k.val < p + t := ⟨by omega, by omega⟩
        have := congrFun heq ⟨p + k.val, by omega⟩
        simp only [dif_pos hk] at this
        simpa using this
      rw [h1, h2]
  simpa [Finset.card_product] using key

lemma count (m t n : ℕ) (hn : 0 < n) (hmn : m + 1 ≤ n) (h2 : 2 * n ≤ 2 ^ t) :
    ∃ NR : Finset (Fin m → Bool), 2 ^ m ≤ 2 * NR.card ∧
      ∀ c ∈ NR, ∀ p, p + t ≤ m → ¬ Run m t c p := by
  classical
  refine ⟨Finset.univ.filter (fun c => ∀ p, p + t ≤ m → ¬ Run m t c p), ?_, ?_⟩
  · generalize hNR : Finset.univ.filter
      (fun c : Fin m → Bool => ∀ p, p + t ≤ m → ¬ Run m t c p) = NR
    have hcov : (Finset.univ : Finset (Fin m → Bool)) ⊆
        NR ∪ (Finset.range (m + 1 - t)).biUnion
          (fun p => Finset.univ.filter (fun c => Run m t c p)) := by
      intro c _
      by_cases hc : ∀ p, p + t ≤ m → ¬ Run m t c p
      · exact Finset.mem_union_left _ (hNR ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
      · push_neg at hc
        obtain ⟨p, hp, hr⟩ := hc
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨p, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩)
    have h1 : 2 ^ m ≤ NR.card + ∑ p ∈ Finset.range (m + 1 - t),
        (Finset.univ.filter (fun c : Fin m → Bool => Run m t c p)).card := by
      calc 2 ^ m = (Finset.univ : Finset (Fin m → Bool)).card := by simp
        _ ≤ (NR ∪ (Finset.range (m + 1 - t)).biUnion
          (fun p => Finset.univ.filter (fun c => Run m t c p))).card := Finset.card_le_card hcov
        _ ≤ NR.card + ((Finset.range (m + 1 - t)).biUnion
          (fun p => Finset.univ.filter (fun c => Run m t c p))).card := Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _
    have h3 : (∑ p ∈ Finset.range (m + 1 - t),
        (Finset.univ.filter (fun c : Fin m → Bool => Run m t c p)).card) * 2 ^ t ≤ n * 2 ^ m := by
      rw [Finset.sum_mul]
      calc ∑ p ∈ Finset.range (m + 1 - t),
            (Finset.univ.filter (fun c : Fin m → Bool => Run m t c p)).card * 2 ^ t
          ≤ ∑ p ∈ Finset.range (m + 1 - t), 2 ^ m :=
            Finset.sum_le_sum (fun p hp => bad_card m t p
              (by have := Finset.mem_range.mp hp; omega) _
              (fun c hc => (Finset.mem_filter.mp hc).2))
        _ = (m + 1 - t) * 2 ^ m := by simp
        _ ≤ n * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
    generalize (∑ p ∈ Finset.range (m + 1 - t),
        (Finset.univ.filter (fun c : Fin m → Bool => Run m t c p)).card) = S at h1 h3
    have h4 : S * (2 * n) ≤ n * 2 ^ m := le_trans (Nat.mul_le_mul_left _ h2) h3
    have h5 : 2 * S ≤ 2 ^ m := by
      have : n * (2 * S) ≤ n * 2 ^ m := by
        calc n * (2 * S) = S * (2 * n) := by ring
          _ ≤ _ := h4
      exact Nat.le_of_mul_le_mul_left this hn
    omega
  · intro c hc
    exact (Finset.mem_filter.mp hc).2

theorem main (n h t : ℕ) (hn : 0 < n) (hht : h ≤ t) (htn : t + 3 ≤ n) (h2 : 2 * n ≤ 2 ^ t)
    (sites : Finset (Fin n)) :
    ∃ (pool : Finset (Fin n → Bool)) (owner : ↥pool → ↥sites),
    (∀ i : ↥sites, 2^(n-t-3) ≤
      ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card) ∧
    ∀ a b : ↥pool,
      (∀ j : Fin (n-h), a.val (loc n hn ((owner a).val.val+j.val)) =
          b.val (loc n hn ((owner a).val.val+j.val))) → a = b := by
  classical
  obtain ⟨pool, hpool⟩ : ∃ pool : Finset (Fin n → Bool), ∀ w, w ∈ pool ↔
      ∃ s, s ∈ sites ∧ Z n t hn w s ∧ ∀ x, Z n t hn w x → x = s :=
    ⟨Finset.univ.filter (fun w => ∃ s, s ∈ sites ∧ Z n t hn w s ∧ ∀ x, Z n t hn w x → x = s),
      fun w => by
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  choose own hown using (fun z : ↥pool => (hpool z.val).mp z.2)
  refine ⟨pool, fun z => ⟨own z, (hown z).1⟩, ?_, ?_⟩
  · intro i
    obtain ⟨NR, hNRcard, hNR⟩ := count (n - t - 2) t n hn (by omega) h2
    have hpow : 2 ^ (n - t - 2) = 2 * 2 ^ (n - t - 3) := by
      have : n - t - 2 = (n - t - 3) + 1 := by omega
      rw [this, pow_succ]; ring
    refine le_trans (b := NR.card) (by omega) ?_
    rw [← Finset.card_image_of_injective NR (E_inj n t hn htn i.val)]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := Subtype.val))
    intro w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
    have hmem : E n t i.val c ∈ pool := (hpool _).mpr ⟨i.val, i.2,
      Z_E n t hn htn i.val c, fun x hx => uniq_E n t hn htn i.val x c (hNR c hc) hx⟩
    refine Finset.mem_image.mpr ⟨⟨_, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply Subtype.ext
    exact ((hown ⟨_, hmem⟩).2.2 i.val (Z_E n t hn htn i.val c)).symm
  · intro a b hab
    apply Subtype.ext
    exact sep n h t hn hht htn a.val b.val (own a) (own b) (hown a).2.1 (hown a).2.2
      (hown b).2.1 (fun j hj => hab ⟨j, hj⟩)

def glue (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) (p : Fin (a + b)) : Bool :=
  if hp : p.val < a then u ⟨p.val, hp⟩ else v ⟨p.val - a, by have := p.isLt; omega⟩

lemma glue_lt (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) (p : Fin (a + b))
    (hp : p.val < a) : glue a b u v p = u ⟨p.val, hp⟩ := by
  unfold glue; rw [dif_pos hp]

lemma glue_ge (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) (p : Fin (a + b))
    (hp : ¬ p.val < a) : glue a b u v p = v ⟨p.val - a, by have := p.isLt; omega⟩ := by
  unfold glue; rw [dif_neg hp]

lemma glue_left (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) (p : ℕ) (hp : p < a)
    (hp' : p < a + b) : glue a b u v ⟨p, hp'⟩ = u ⟨p, hp⟩ :=
  glue_lt a b u v ⟨p, hp'⟩ hp

lemma glue_right (a b : ℕ) (u : Fin a → Bool) (v : Fin b → Bool) (q : ℕ) (hq : q < b)
    (hp' : a + q < a + b) : glue a b u v ⟨a + q, hp'⟩ = v ⟨q, hq⟩ := by
  rw [glue_ge a b u v ⟨a + q, hp'⟩ (by show ¬ (a + q < a); omega)]
  exact congrArg v (Fin.ext (by show a + q - a = q; omega))

lemma modc (x a : ℕ) (hx : x < 2 * a) : (x < a ∧ x % a = x) ∨ (a ≤ x ∧ x % a = x - a) := by
  by_cases h : x < a
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)

lemma vis (n w h : ℕ) (l p : ℕ) (hl : l < n) (hp : p < n) (hw : n ≤ w + 1 + h)
    (hhl : h ≤ l) (hv : p < l → p + h < l) : ∃ j, j < w + 1 ∧ (l + j) % n = p := by
  by_cases hc : l ≤ p
  · refine ⟨p - l, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hc]; exact Nat.mod_eq_of_lt hp
  · refine ⟨p + n - l, by have := hv (by omega); omega, ?_⟩
    have : l + (p + n - l) = p + n := by omega
    rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hp

lemma pool_card (n k : ℕ) (sites : Finset (Fin n)) (pool : Finset (Fin n → Bool))
    (owner : ↥pool → ↥sites)
    (hc : ∀ i : ↥sites, k ≤
      ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card) :
    sites.card * k ≤ pool.card := by
  calc sites.card * k = ∑ _i : ↥sites, k := by simp
    _ ≤ ∑ i : ↥sites, ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card :=
        Finset.sum_le_sum (fun i _ => hc i)
    _ = (Finset.univ : Finset ↥pool).card :=
        (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)).symm
    _ = pool.card := by simp

lemma arc (a h t : ℕ) (ha : 0 < a) (hht : h ≤ t) (hta : t + 3 ≤ a) (h2 : 2 * a ≤ 2 ^ t) :
    ∃ (pool : Finset (Fin a → Bool)) (own : ↥pool → Fin a),
      (a - h - 1) * 2 ^ (a - t - 3) ≤ pool.card ∧
      (∀ u, h + 1 ≤ (own u).val) ∧
      ∀ u u' : ↥pool, (∀ j, j < a - h → u.val (loc a ha ((own u).val + j)) =
        u'.val (loc a ha ((own u).val + j))) → u = u' := by
  classical
  obtain ⟨sites, hs, hmem⟩ : ∃ sites : Finset (Fin a), sites.card = a - h - 1 ∧
      ∀ s ∈ sites, h + 1 ≤ s.val := by
    refine ⟨Finset.univ.image (fun i : Fin (a - h - 1) =>
      (⟨i.val + h + 1, by have := i.isLt; omega⟩ : Fin a)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective]
      · simp
      · intro i i' hii
        have h3 : i.val + h + 1 = i'.val + h + 1 := congrArg Fin.val hii
        exact Fin.ext (by omega)
    · intro s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      show h + 1 ≤ i.val + h + 1
      omega
  obtain ⟨pool, owner, hcard, hsep⟩ := main a h t ha hht hta h2 sites
  refine ⟨pool, fun u => (owner u).val, ?_, ?_, ?_⟩
  · rw [← hs]
    exact pool_card a _ sites pool owner hcard
  · intro u
    exact hmem _ (owner u).2
  · intro u u' hj
    exact hsep u u' (fun j => hj j.val j.isLt)

theorem core {n w M : ℕ} (a : ℕ) (lc : ℕ → Fin n) (code : Fin M → (Fin n → Bool))
    (L R : Fin M → Fin n) (r0 ra : Fin n)
    (hL : ∀ m, (L m).val < a ∧ L m ≠ r0 ∧ L m ≠ ra)
    (hR : ∀ m, a ≤ (R m).val ∧ R m ≠ r0 ∧ R m ≠ ra)
    (P1L : ∀ m m', (∀ j, j < w + 1 → code m (lc ((L m).val + j)) =
        code m' (lc ((L m).val + j))) → m = m')
    (P1R : ∀ m m', (∀ j, j < w + 1 → code m (lc ((R m).val + j)) =
        code m' (lc ((R m).val + j))) → m = m')
    (T : ∀ x m1 m2, (∀ j, j < w + 1 → x (lc (r0.val + j)) = code m1 (lc (r0.val + j))) →
        (∀ j, j < w + 1 → x (lc (ra.val + j)) = code m2 (lc (ra.val + j))) →
        ∃ m, code m = x) :
    ∃ (base : Fin n × (Fin (w+1) → Bool) → Bool)
      (left right : Fin M → Fin n × (Fin (w+1) → Bool)),
      Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
      (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
        base (left i) = false ∧ base (right i) = false) ∧
      ∀ (A B : Finset (Fin M)) (x : Fin n → Bool),
        (∀ i : Fin n, (base (i, fun j => x (lc (i.val + j.val))) = true ∨
          ∃ m ∈ A, left m = (i, fun j => x (lc (i.val + j.val)))) ∨
          ∃ m ∈ B, right m = (i, fun j => x (lc (i.val + j.val)))) ↔
        ∃ m, (m ∈ A ∧ m ∈ B) ∧ code m = x := by
  classical
  have QL : ∀ m m', (fun j : Fin (w+1) => code m (lc ((L m).val + j.val))) =
      (fun j : Fin (w+1) => code m' (lc ((L m).val + j.val))) → m = m' :=
    fun m m' h => P1L m m' (fun j hj => congrFun h ⟨j, hj⟩)
  have QR : ∀ m m', (fun j : Fin (w+1) => code m (lc ((R m).val + j.val))) =
      (fun j : Fin (w+1) => code m' (lc ((R m).val + j.val))) → m = m' :=
    fun m m' h => P1R m m' (fun j hj => congrFun h ⟨j, hj⟩)
  obtain ⟨left, hleft⟩ : ∃ left : Fin M → Fin n × (Fin (w+1) → Bool),
      ∀ m, left m = (L m, fun j => code m (lc ((L m).val + j.val))) := ⟨_, fun _ => rfl⟩
  obtain ⟨right, hright⟩ : ∃ right : Fin M → Fin n × (Fin (w+1) → Bool),
      ∀ m, right m = (R m, fun j => code m (lc ((R m).val + j.val))) := ⟨_, fun _ => rfl⟩
  obtain ⟨base, hbase⟩ : ∃ base : Fin n × (Fin (w+1) → Bool) → Bool, ∀ i p, base (i, p) =
      if i = r0 ∨ i = ra then
        decide (∃ m, p = fun j : Fin (w+1) => code m (lc (i.val + j.val)))
      else decide (¬ ∃ m, left m = (i, p) ∨ right m = (i, p)) :=
    ⟨fun slot => if slot.1 = r0 ∨ slot.1 = ra then
        decide (∃ m, slot.2 = fun j : Fin (w+1) => code m (lc (slot.1.val + j.val)))
      else decide (¬ ∃ m, left m = slot ∨ right m = slot), fun _ _ => rfl⟩
  have linj : Function.Injective left := by
    intro m m' h
    rw [hleft, hleft] at h
    have h1 := (Prod.mk.inj h).1
    have h2 := (Prod.mk.inj h).2
    rw [← h1] at h2
    exact QL m m' h2
  have rinj : Function.Injective right := by
    intro m m' h
    rw [hright, hright] at h
    have h1 := (Prod.mk.inj h).1
    have h2 := (Prod.mk.inj h).2
    rw [← h1] at h2
    exact QR m m' h2
  have bl : ∀ m, base (left m) = false := by
    intro m
    have h0 : ¬ (L m = r0 ∨ L m = ra) := fun h => h.elim (hL m).2.1 (hL m).2.2
    rw [hleft, hbase, if_neg h0, decide_eq_false_iff_not, not_not]
    exact ⟨m, Or.inl (hleft m)⟩
  have br : ∀ m, base (right m) = false := by
    intro m
    have h0 : ¬ (R m = r0 ∨ R m = ra) := fun h => h.elim (hR m).2.1 (hR m).2.2
    rw [hright, hbase, if_neg h0, decide_eq_false_iff_not, not_not]
    exact ⟨m, Or.inr (hright m)⟩
  refine ⟨base, left, right, ?_, linj, rinj, ?_, ?_⟩
  · intro m m' h
    exact P1L m m' (fun j _ => by rw [h])
  · intro i
    refine ⟨?_, ?_, bl i, br i⟩
    · rw [hleft]; exact (hL i).1
    · rw [hright]; exact (hR i).1
  · intro A B x
    constructor
    · intro H
      have key : ∀ r : Fin n, (r = r0 ∨ r = ra) →
          ∃ m, (fun j : Fin (w+1) => x (lc (r.val + j.val))) =
            fun j : Fin (w+1) => code m (lc (r.val + j.val)) := by
        intro r hr
        rcases H r with (hb | ⟨m, -, hm⟩) | ⟨m, -, hm⟩
        · rw [hbase, if_pos hr, decide_eq_true_eq] at hb
          exact hb
        · exfalso
          rw [hleft] at hm
          have h1 : L m = r := (Prod.mk.inj hm).1
          rcases hr with hr | hr
          · exact (hL m).2.1 (h1.trans hr)
          · exact (hL m).2.2 (h1.trans hr)
        · exfalso
          rw [hright] at hm
          have h1 : R m = r := (Prod.mk.inj hm).1
          rcases hr with hr | hr
          · exact (hR m).2.1 (h1.trans hr)
          · exact (hR m).2.2 (h1.trans hr)
      obtain ⟨m1, hm1⟩ := key r0 (Or.inl rfl)
      obtain ⟨m2, hm2⟩ := key ra (Or.inr rfl)
      obtain ⟨m, rfl⟩ := T x m1 m2 (fun j hj => congrFun hm1 ⟨j, hj⟩)
        (fun j hj => congrFun hm2 ⟨j, hj⟩)
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases H (L m) with (hb | ⟨m', hA, hm⟩) | ⟨m', -, hm⟩
        · have h0 := bl m
          rw [hleft] at h0
          exact Bool.noConfusion (h0.symm.trans hb)
        · rw [← hleft m] at hm
          rw [← linj hm]; exact hA
        · exfalso
          rw [hright] at hm
          have h1 : R m' = L m := (Prod.mk.inj hm).1
          have h2 := (hR m').1
          have h3 := (hL m).1
          rw [h1] at h2
          omega
      · rcases H (R m) with (hb | ⟨m', -, hm⟩) | ⟨m', hB, hm⟩
        · have h0 := br m
          rw [hright] at h0
          exact Bool.noConfusion (h0.symm.trans hb)
        · exfalso
          rw [hleft] at hm
          have h1 : L m' = R m := (Prod.mk.inj hm).1
          have h2 := (hL m').1
          have h3 := (hR m).1
          rw [h1] at h2
          omega
        · rw [← hright m] at hm
          rw [← rinj hm]; exact hB
    · rintro ⟨m, ⟨hA, hB⟩, rfl⟩ i
      by_cases hi : i = r0 ∨ i = ra
      · left; left
        rw [hbase, if_pos hi, decide_eq_true_eq]
        exact ⟨m, rfl⟩
      · by_cases hex : ∃ m', left m' = (i, fun j : Fin (w+1) => code m (lc (i.val + j.val))) ∨
            right m' = (i, fun j : Fin (w+1) => code m (lc (i.val + j.val)))
        · obtain ⟨m', hm' | hm'⟩ := hex
          · left; right
            have hm2 := hm'
            rw [hleft] at hm2
            have h1 : L m' = i := (Prod.mk.inj hm2).1
            have h2 := (Prod.mk.inj hm2).2
            subst h1
            have h3 := QL m' m h2
            subst h3
            exact ⟨_, hA, hm'⟩
          · right
            have hm2 := hm'
            rw [hright] at hm2
            have h1 : R m' = i := (Prod.mk.inj hm2).1
            have h2 := (Prod.mk.inj hm2).2
            subst h1
            have h3 := QR m' m h2
            subst h3
            exact ⟨_, hB, hm'⟩
        · left; left
          rw [hbase, if_neg hi, decide_eq_true_eq]
          exact hex

theorem main569 (a b w t : ℕ) (hn : 0 < a + b) (hht : a + b - (w + 1) ≤ t)
    (hmin : t + 3 ≤ min a b) (hmax : 2 * max a b ≤ 2 ^ t) :
    ∃ (M : ℕ) (code : Fin M → (Fin (a+b) → Bool))
      (base : Fin (a+b) × (Fin (w+1) → Bool) → Bool)
      (left right : Fin M → Fin (a+b) × (Fin (w+1) → Bool)),
      (a-(a + b - (w + 1))-1)*2^(a-t-3)*((b-(a + b - (w + 1))-1)*2^(b-t-3)) ≤ M ∧
      Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
      (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
        base (left i) = false ∧ base (right i) = false) ∧
      ∀ A B : Finset (Fin M),
        ((Finset.univ : Finset (Fin (a+b) → Bool)).filter (fun x =>
          ∀ i : Fin (a+b), (base (i, fun j => x (loc (a+b) hn (i.val + j.val))) ||
            decide ((i, fun j => x (loc (a+b) hn (i.val + j.val))) ∈ A.image left) ||
            decide ((i, fun j => x (loc (a+b) hn (i.val + j.val))) ∈ B.image right)) = true)) =
          (A ∩ B).image code := by
  classical
  have ha : 0 < a := by omega
  have hb : 0 < b := by omega
  obtain ⟨h, hh⟩ : ∃ h, h = a + b - (w + 1) := ⟨_, rfl⟩
  rw [← hh] at hht ⊢
  have hw : a + b ≤ w + 1 + h := by omega
  obtain ⟨pL, oL, cL, sL, eL⟩ := arc a h t ha hht (by omega) (by omega)
  obtain ⟨pR, oR, cR, sR, eR⟩ := arc b h t hb hht (by omega) (by omega)
  obtain ⟨M, hM, ⟨e⟩⟩ : ∃ M, M = pL.card * pR.card ∧ Nonempty (Fin M ≃ ↥pL × ↥pR) :=
    ⟨Fintype.card (↥pL × ↥pR), by simp, ⟨(Fintype.equivFin _).symm⟩⟩
  obtain ⟨code, hcode⟩ : ∃ code : Fin M → (Fin (a+b) → Bool),
      ∀ m, code m = glue a b (e m).1.val (e m).2.val := ⟨_, fun _ => rfl⟩
  obtain ⟨L, hLv⟩ : ∃ L : Fin M → Fin (a+b), ∀ m, (L m).val = (oL (e m).1).val :=
    ⟨fun m => ⟨(oL (e m).1).val, by have := (oL (e m).1).isLt; omega⟩, fun _ => rfl⟩
  obtain ⟨R, hRv⟩ : ∃ R : Fin M → Fin (a+b), ∀ m, (R m).val = a + (oR (e m).2).val :=
    ⟨fun m => ⟨a + (oR (e m).2).val, by have := (oR (e m).2).isLt; omega⟩, fun _ => rfl⟩
  obtain ⟨r0, hr0⟩ : ∃ r0 : Fin (a+b), r0.val = 0 := ⟨⟨0, hn⟩, rfl⟩
  obtain ⟨ra, hra⟩ : ∃ ra : Fin (a+b), ra.val = a := ⟨⟨a, by omega⟩, rfl⟩
  have hL' : ∀ m, (L m).val < a ∧ L m ≠ r0 ∧ L m ≠ ra := by
    intro m
    have h1 := hLv m
    have h2 := sL (e m).1
    have h3 := (oL (e m).1).isLt
    refine ⟨by omega, ?_, ?_⟩
    · intro hc; rw [hc] at h1; omega
    · intro hc; rw [hc] at h1; omega
  have hR' : ∀ m, a ≤ (R m).val ∧ R m ≠ r0 ∧ R m ≠ ra := by
    intro m
    have h1 := hRv m
    have h2 := sR (e m).2
    refine ⟨by omega, ?_, ?_⟩
    · intro hc; rw [hc] at h1; omega
    · intro hc; rw [hc] at h1; omega
  have P1L : ∀ m m', (∀ j, j < w + 1 → code m (loc (a+b) hn ((L m).val + j)) =
      code m' (loc (a+b) hn ((L m).val + j))) → m = m' := by
    intro m m' H
    have h1 := hLv m
    have h2 := sL (e m).1
    have h3 := (oL (e m).1).isLt
    have V : ∀ (p : ℕ) (hp : p < a + b), (p < (L m).val → p + h < (L m).val) →
        code m ⟨p, hp⟩ = code m' ⟨p, hp⟩ := by
      intro p hp hv
      obtain ⟨j, hj, hjp⟩ := vis (a+b) w h (L m).val p (L m).isLt hp hw (by omega) hv
      have hH := H j hj
      have hloc : loc (a+b) hn ((L m).val + j) = ⟨p, hp⟩ := Fin.ext hjp
      rw [hloc] at hH
      exact hH
    apply e.injective
    apply Prod.ext
    · apply eL
      intro j hj
      obtain ⟨q, hq⟩ : ∃ q : Fin a, q = loc a ha ((oL (e m).1).val + j) := ⟨_, rfl⟩
      rw [← hq]
      have hqv : q.val = ((oL (e m).1).val + j) % a := by rw [hq]; rfl
      have hql := q.isLt
      have hv : q.val < (L m).val → q.val + h < (L m).val := by
        rcases modc ((oL (e m).1).val + j) a (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> omega
      have := V q.val (by omega) hv
      rw [hcode, hcode, glue_left a b _ _ q.val q.isLt, glue_left a b _ _ q.val q.isLt] at this
      exact this
    · apply Subtype.ext
      funext q
      have hql := q.isLt
      have := V (a + q.val) (by omega) (fun _ => by omega)
      rw [hcode, hcode, glue_right a b _ _ q.val q.isLt, glue_right a b _ _ q.val q.isLt] at this
      exact this
  have P1R : ∀ m m', (∀ j, j < w + 1 → code m (loc (a+b) hn ((R m).val + j)) =
      code m' (loc (a+b) hn ((R m).val + j))) → m = m' := by
    intro m m' H
    have h1 := hRv m
    have h2 := sR (e m).2
    have h3 := (oR (e m).2).isLt
    have V : ∀ (p : ℕ) (hp : p < a + b), (p < (R m).val → p + h < (R m).val) →
        code m ⟨p, hp⟩ = code m' ⟨p, hp⟩ := by
      intro p hp hv
      obtain ⟨j, hj, hjp⟩ := vis (a+b) w h (R m).val p (R m).isLt hp hw (by omega) hv
      have hH := H j hj
      have hloc : loc (a+b) hn ((R m).val + j) = ⟨p, hp⟩ := Fin.ext hjp
      rw [hloc] at hH
      exact hH
    apply e.injective
    apply Prod.ext
    · apply Subtype.ext
      funext q
      have hql := q.isLt
      have := V q.val (by omega) (fun _ => by omega)
      rw [hcode, hcode, glue_left a b _ _ q.val q.isLt, glue_left a b _ _ q.val q.isLt] at this
      exact this
    · apply eR
      intro j hj
      obtain ⟨q, hq⟩ : ∃ q : Fin b, q = loc b hb ((oR (e m).2).val + j) := ⟨_, rfl⟩
      rw [← hq]
      have hqv : q.val = ((oR (e m).2).val + j) % b := by rw [hq]; rfl
      have hql := q.isLt
      have hv : a + q.val < (R m).val → a + q.val + h < (R m).val := by
        rcases modc ((oR (e m).2).val + j) b (by omega) with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> omega
      have := V (a + q.val) (by omega) hv
      rw [hcode, hcode, glue_right a b _ _ q.val q.isLt, glue_right a b _ _ q.val q.isLt] at this
      exact this
  have T : ∀ x m1 m2,
      (∀ j, j < w + 1 → x (loc (a+b) hn (r0.val + j)) = code m1 (loc (a+b) hn (r0.val + j))) →
      (∀ j, j < w + 1 → x (loc (a+b) hn (ra.val + j)) = code m2 (loc (a+b) hn (ra.val + j))) →
      ∃ m, code m = x := by
    intro x m1 m2 H1 H2
    obtain ⟨m, hm⟩ : ∃ m, e m = ((e m1).1, (e m2).2) := ⟨e.symm _, e.apply_symm_apply _⟩
    have hm1 : (e m).1 = (e m1).1 := by
      have h9 : (e m).1 = ((e m1).1, (e m2).2).1 := by rw [hm]
      exact h9
    have hm2 : (e m).2 = (e m2).2 := by
      have h9 : (e m).2 = ((e m1).1, (e m2).2).2 := by rw [hm]
      exact h9
    refine ⟨m, ?_⟩
    funext p
    have hpl := p.isLt
    rw [hcode, hm1, hm2]
    by_cases hp : p.val < a
    · have hH := H1 p.val (by omega)
      have hloc : loc (a+b) hn (r0.val + p.val) = p := by
        apply Fin.ext
        show (r0.val + p.val) % (a + b) = p.val
        rw [hr0, Nat.zero_add]; exact Nat.mod_eq_of_lt p.isLt
      rw [hloc, hcode] at hH
      rw [hH, glue_lt a b _ _ p hp, glue_lt a b _ _ p hp]
    · have hH := H2 (p.val - a) (by omega)
      have hloc : loc (a+b) hn (ra.val + (p.val - a)) = p := by
        apply Fin.ext
        show (ra.val + (p.val - a)) % (a + b) = p.val
        rw [hra, Nat.add_sub_cancel' (by omega)]; exact Nat.mod_eq_of_lt p.isLt
      rw [hloc, hcode] at hH
      rw [hH, glue_ge a b _ _ p hp, glue_ge a b _ _ p hp]
  obtain ⟨base, left, right, c1, c2, c3, c4, c5⟩ :=
    core (w := w) a (loc (a+b) hn) code L R r0 ra hL' hR' P1L P1R T
  refine ⟨M, code, base, left, right, ?_, c1, c2, c3, c4, ?_⟩
  · rw [hM]; exact Nat.mul_le_mul cL cR
  · intro A B
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_inter, Bool.or_eq_true, decide_eq_true_eq]
    exact c5 A B x


end PEqualNP.Outside.L_lib_569_aux

theorem PEqualNP.Outside.L_lib_569 : (∀ (a b w t : Nat) (hn : 0 < a+b),
  let n := a+b
  let h := n-(w+1)
  h ≤ t → t+3 ≤ min a b → 2*max a b ≤ 2^t →
  let Word := Fin n → Bool
  let Pat := Fin (w+1) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (M : Nat) (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    (a-h-1)*2^(a-t-3)*((b-h-1)*2^(b-t-3)) ≤ M ∧
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code) := by
  intro a b w t hn n h hht hmin hmax Word Pat Slot loc solutions
  exact PEqualNP.Outside.L_lib_569_aux.main569 a b w t hn hht hmin hmax
