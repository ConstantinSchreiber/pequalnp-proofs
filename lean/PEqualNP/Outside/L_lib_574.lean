import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_574_aux

def win {n : ℕ} (hn : 0 < n) (h : ℕ) (x : Fin n → Bool) (i : Fin n) : Fin (n-h) → Bool :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def Goal (n h M a : ℕ) (hn : 0 < n) : Prop :=
  ∃ (code : Fin M → (Fin n → Bool)) (base : Fin n × (Fin (n-h) → Bool) → Bool)
    (left right : Fin M → Fin n × (Fin (n-h) → Bool)),
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M),
      (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, (base (i, win hn h x i) || decide ((i, win hn h x i) ∈ A.image left) ||
          decide ((i, win hn h x i) ∈ B.image right)) = true) = (A ∩ B).image code

theorem win_agree {n h : ℕ} (hn : 0 < n) (x y : Fin n → Bool) (i : Fin n)
    (H : win hn h x i = win hn h y i) (k : Fin n) (j : ℕ) (hj : j < n - h)
    (hk : (i.val + j) % n = k.val) : x k = y k := by
  have := congrFun H ⟨j, hj⟩
  have e : (⟨(i.val + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hk
  change x ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩ = y ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩ at this
  rwa [e] at this

theorem off_tile {n h : ℕ} (hn : 0 < n) (x y : Fin n → Bool) (i : Fin n) (T : ℕ)
    (hT : i.val = T + h) (H : win hn h x i = win hn h y i) :
    ∀ k : Fin n, (k.val < T ∨ T + h ≤ k.val) → x k = y k := by
  intro k hk
  have hi := i.isLt
  have hk' := k.isLt
  rcases hk with hk | hk
  · apply win_agree hn x y i H k (k.val + n - (T+h)) (by omega)
    have : i.val + (k.val + n - (T + h)) = k.val + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
  · apply win_agree hn x y i H k (k.val - (T+h)) (by omega)
    have : i.val + (k.val - (T+h)) = k.val := by omega
    rw [this, Nat.mod_eq_of_lt k.isLt]

theorem assemble {n h M : ℕ} (hn : 0 < n) {S : Type} [Fintype S] (hM : M ≤ Fintype.card S)
    (E : S → (Fin n → Bool)) (l r : S → Fin n) (a : ℕ) (ha : 0 < a)
    (hl0 : ∀ t, 0 < (l t).val) (hla : ∀ t, (l t).val < a) (hra : ∀ t, a ≤ (r t).val)
    (hclose : ∀ (x : Fin n → Bool) (t : S),
      win hn h x ⟨0, hn⟩ = win hn h (E t) ⟨0, hn⟩ → ∃ t', x = E t')
    (hkeyL : ∀ t t', win hn h (E t') (l t) = win hn h (E t) (l t) → t' = t)
    (hkeyR : ∀ t t', win hn h (E t') (r t) = win hn h (E t) (r t) → t' = t) :
    Goal n h M a hn := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin M) (β := S) (by simpa using hM)
  unfold Goal
  refine ⟨fun m => E (e m),
    fun slot => decide ((slot.1 = ⟨0, hn⟩ → ∃ t, slot.2 = win hn h (E t) ⟨0, hn⟩) ∧
      ¬ ∃ t, slot = (l t, win hn h (E t) (l t)) ∨ slot = (r t, win hn h (E t) (r t))),
    fun m => (l (e m), win hn h (E (e m)) (l (e m))),
    fun m => (r (e m), win hn h (E (e m)) (r (e m))), ?_, ?_, ?_, ?_, ?_⟩
  · intro m m' hmm
    have hmm' : E (e m) = E (e m') := hmm
    exact e.injective (hkeyL (e m') (e m) (by rw [hmm']))
  · intro m m' hmm
    have h1 : l (e m) = l (e m') := congrArg Prod.fst hmm
    have h2 : win hn h (E (e m)) (l (e m)) = win hn h (E (e m')) (l (e m')) :=
      congrArg Prod.snd hmm
    rw [h1] at h2
    exact e.injective (hkeyL (e m') (e m) h2)
  · intro m m' hmm
    have h1 : r (e m) = r (e m') := congrArg Prod.fst hmm
    have h2 : win hn h (E (e m)) (r (e m)) = win hn h (E (e m')) (r (e m')) :=
      congrArg Prod.snd hmm
    rw [h1] at h2
    exact e.injective (hkeyR (e m') (e m) h2)
  · intro i
    refine ⟨hla _, hra _, ?_, ?_⟩
    · simp only [decide_eq_false_iff_not]
      rintro ⟨-, hc⟩
      exact hc ⟨e i, Or.inl rfl⟩
    · simp only [decide_eq_false_iff_not]
      rintro ⟨-, hc⟩
      exact hc ⟨e i, Or.inr rfl⟩
  · intro A B
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_inter,
      Bool.or_eq_true, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · intro H
      obtain ⟨t', rfl⟩ : ∃ t', x = E t' := by
        rcases H ⟨0, hn⟩ with (⟨hP, -⟩ | ⟨m, -, hm, -⟩) | ⟨m, -, hm, -⟩
        · obtain ⟨t, ht⟩ := hP rfl
          exact hclose x t ht
        · have h1 := hl0 (e m)
          rw [hm] at h1
          exact absurd h1 (lt_irrefl 0)
        · have h1 := hra (e m)
          rw [hm] at h1
          have h2 : a ≤ 0 := h1
          omega
      obtain ⟨m, hmA, hm⟩ : ∃ m, m ∈ A ∧ t' = e m := by
        rcases H (l t') with (⟨-, hQ⟩ | ⟨m, hmA, hm1, hm2⟩) | ⟨m, -, hm1, -⟩
        · exact absurd ⟨t', Or.inl ⟨rfl, rfl⟩⟩ hQ
        · refine ⟨m, hmA, hkeyL (e m) t' ?_⟩
          rw [hm1] at hm2 ⊢
          exact hm2.symm
        · have h1 := hra (e m)
          rw [hm1] at h1
          have h2 := hla t'
          omega
      obtain ⟨m', hmB, hm'⟩ : ∃ m, m ∈ B ∧ t' = e m := by
        rcases H (r t') with (⟨-, hQ⟩ | ⟨m, -, hm1, -⟩) | ⟨m, hmB, hm1, hm2⟩
        · exact absurd ⟨t', Or.inr ⟨rfl, rfl⟩⟩ hQ
        · have h1 := hla (e m)
          rw [hm1] at h1
          have h2 := hra t'
          omega
        · refine ⟨m, hmB, hkeyR (e m) t' ?_⟩
          rw [hm1] at hm2 ⊢
          exact hm2.symm
      have hmm : m = m' := e.injective (hm.symm.trans hm')
      subst hmm
      exact ⟨m, ⟨hmA, hmB⟩, by rw [hm]⟩
    · rintro ⟨m, ⟨hA, hB⟩, rfl⟩ i
      by_cases hQ : ∃ t, (i = l t ∧ win hn h (E (e m)) i = win hn h (E t) (l t)) ∨
          (i = r t ∧ win hn h (E (e m)) i = win hn h (E t) (r t))
      · obtain ⟨t, ⟨hi, hw⟩ | ⟨hi, hw⟩⟩ := hQ
        · subst hi
          have := hkeyL t (e m) hw
          subst this
          exact Or.inl (Or.inr ⟨m, hA, rfl, rfl⟩)
        · subst hi
          have := hkeyR t (e m) hw
          subst this
          exact Or.inr ⟨m, hB, rfl, rfl⟩
      · exact Or.inl (Or.inl ⟨fun hi => ⟨e m, by rw [hi]⟩, hQ⟩)

theorem mul_step {x y h : ℕ} (hxy : x < y) : x*h + h ≤ y*h := by
  have h2 : (x+1)*h ≤ y*h := Nat.mul_le_mul_right h hxy
  have h3 : (x+1)*h = x*h + h := Nat.succ_mul x h
  omega

theorem eq_of_bits {h x y : ℕ} (hx : x < 2^h) (hy : y < 2^h)
    (H : ∀ o, o < h → x.testBit o = y.testBit o) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < h
  · exact H i hi
  · have hi' : h ≤ i := Nat.le_of_not_lt hi
    have : 2^h ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hi'
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx this),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy this)]

def tv {q' : ℕ} (z N : ℕ) (u : Fin (q'+1)) (c : Fin z) (μ : Fin q' → Fin N) : Fin (q'+1) → ℕ :=
  Fin.insertNth (α := fun _ => ℕ) u c.val (fun k => z + (μ k).val)

theorem tv_same {q' z N : ℕ} (u : Fin (q'+1)) (c : Fin z) (μ : Fin q' → Fin N) :
    tv z N u c μ u = c.val := by
  simp [tv]

theorem tv_succAbove {q' z N : ℕ} (u : Fin (q'+1)) (c : Fin z) (μ : Fin q' → Fin N)
    (k : Fin q') : tv z N u c μ (u.succAbove k) = z + (μ k).val := by
  simp [tv]

theorem tv_ge {q' z N : ℕ} (u : Fin (q'+1)) (c : Fin z) (μ : Fin q' → Fin N)
    (j : Fin (q'+1)) (hj : j ≠ u) : z ≤ tv z N u c μ j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  rw [tv_succAbove]; omega

theorem tv_lt {q' z N h : ℕ} (hz : z + N ≤ 2^h) (u : Fin (q'+1)) (c : Fin z)
    (μ : Fin q' → Fin N) (j : Fin (q'+1)) : tv z N u c μ j < 2^h := by
  by_cases hj : j = u
  · subst hj; rw [tv_same]; have := c.isLt; omega
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [tv_succAbove]; have := (μ k).isLt; omega

theorem tv_rigid {q' z N : ℕ} (u u' : Fin (q'+1)) (c c' : Fin z) (μ μ' : Fin q' → Fin N)
    (H : ∀ j, j ≠ u → tv z N u' c' μ' j = tv z N u c μ j) : u' = u ∧ μ' = μ := by
  have hu : u' = u := by
    by_contra hne
    have h1 := H u' hne
    rw [tv_same] at h1
    have h2 := tv_ge u c μ u' hne
    have := c'.isLt
    omega
  subst hu
  refine ⟨rfl, ?_⟩
  funext k
  have h1 := H (u'.succAbove k) (Fin.succAbove_ne u' k)
  rw [tv_succAbove, tv_succAbove] at h1
  exact Fin.ext (by omega)

theorem tv_inj {q' z N : ℕ} (u u' : Fin (q'+1)) (c c' : Fin z) (μ μ' : Fin q' → Fin N)
    (H : ∀ j, tv z N u' c' μ' j = tv z N u c μ j) : u' = u ∧ c' = c ∧ μ' = μ := by
  obtain ⟨hu, hμ⟩ := tv_rigid u u' c c' μ μ' (fun j _ => H j)
  subst hu; subst hμ
  have := H u'
  rw [tv_same, tv_same] at this
  exact ⟨rfl, Fin.ext this, rfl⟩

def tvN {q' : ℕ} (V : Fin (q'+1) → ℕ) (j : ℕ) : ℕ := if hj : j < q'+1 then V ⟨j, hj⟩ else 0

theorem tvN_val {q' : ℕ} (V : Fin (q'+1) → ℕ) (j : Fin (q'+1)) : tvN V j.val = V j := by
  unfold tvN
  first
    | exact dif_pos j.isLt
    | rw [dif_pos j.isLt]
    | simp only [dif_pos j.isLt]

def enc (a b h X : ℕ) {q' : ℕ} (VL VR : Fin (q'+1) → ℕ)
    (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool) : Fin (a+b) → Bool := fun i =>
  if h1 : i.val < X then (tvN VL (i.val / h)).testBit (i.val % h)
  else if h2 : i.val < a then gL ⟨i.val - X, by omega⟩
  else if h3 : i.val < a + X then (tvN VR ((i.val - a) / h)).testBit ((i.val - a) % h)
  else gR ⟨i.val - a - X, by have := i.isLt; omega⟩

theorem divmod {h : ℕ} (hh : 0 < h) (j o : ℕ) (ho : o < h) :
    (j*h + o) / h = j ∧ (j*h + o) % h = o := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt ho, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem enc_L (a b h X : ℕ) {q' : ℕ} (hh : 0 < h) (hX : X = (q'+1)*h)
    (VL VR : Fin (q'+1) → ℕ) (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool)
    (j : Fin (q'+1)) (o : ℕ) (ho : o < h) (hi : j.val*h + o < a+b) :
    enc a b h X VL VR gL gR ⟨j.val*h+o, hi⟩ = (VL j).testBit o := by
  have h0 : j.val*h + h ≤ (q'+1)*h := mul_step j.isLt
  have h1 : j.val*h + o < X := by omega
  obtain ⟨e1, e2⟩ := divmod hh j.val o ho
  simp only [enc, dif_pos h1, e1, e2, tvN_val]

theorem enc_R (a b h X : ℕ) {q' : ℕ} (hh : 0 < h) (hX : X = (q'+1)*h) (hXa : X < a)
    (VL VR : Fin (q'+1) → ℕ) (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool)
    (j : Fin (q'+1)) (o : ℕ) (ho : o < h) (hi : a + (j.val*h + o) < a+b) :
    enc a b h X VL VR gL gR ⟨a + (j.val*h+o), hi⟩ = (VR j).testBit o := by
  have h0 : j.val*h + h ≤ (q'+1)*h := mul_step j.isLt
  have h1 : ¬ (a + (j.val*h + o) < X) := by omega
  have h2 : ¬ (a + (j.val*h + o) < a) := by omega
  have h3 : a + (j.val*h + o) < a + X := by omega
  obtain ⟨e1, e2⟩ := divmod hh j.val o ho
  simp only [enc, dif_neg h1, dif_neg h2, dif_pos h3, Nat.add_sub_cancel_left, e1, e2, tvN_val]

theorem enc_gL (a b h X : ℕ) {q' : ℕ}
    (VL VR : Fin (q'+1) → ℕ) (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool)
    (k : Fin (a - X)) (hi : X + k.val < a+b) :
    enc a b h X VL VR gL gR ⟨X + k.val, hi⟩ = gL k := by
  have h1 : ¬ (X + k.val < X) := by omega
  have h2 : X + k.val < a := by have := k.isLt; omega
  simp only [enc, dif_neg h1, dif_pos h2, Nat.add_sub_cancel_left, Fin.eta]

theorem enc_gR (a b h X : ℕ) {q' : ℕ}
    (VL VR : Fin (q'+1) → ℕ) (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool)
    (k : Fin (b - X)) (hi : a + X + k.val < a+b) :
    enc a b h X VL VR gL gR ⟨a + X + k.val, hi⟩ = gR k := by
  have h1 : ¬ (a + X + k.val < X) := by omega
  have h2 : ¬ (a + X + k.val < a) := by omega
  have h3 : ¬ (a + X + k.val < a + X) := by omega
  have e : a + X + k.val - a - X = k.val := by omega
  simp only [enc, dif_neg h1, dif_neg h2, dif_neg h3, e, Fin.eta]

theorem enc_close (a b h X : ℕ) {q' : ℕ} (hXb : X + h ≤ b) (VL VR : Fin (q'+1) → ℕ)
    (gL : Fin (a - X) → Bool) (gR : Fin (b - X) → Bool) (x : Fin (a+b) → Bool)
    (H : ∀ k : Fin (a+b), k.val < a + b - h → x k = enc a b h X VL VR gL gR k) :
    x = enc a b h X VL VR gL (fun k => x ⟨a + X + k.val, by have := k.isLt; omega⟩) := by
  funext i
  have hi' := i.isLt
  by_cases hi : i.val < a + X
  · rw [H i (by omega)]
    by_cases h1 : i.val < X
    · simp only [enc, dif_pos h1]
    · by_cases h2 : i.val < a
      · simp only [enc, dif_neg h1, dif_pos h2]
      · simp only [enc, dif_neg h1, dif_neg h2, dif_pos hi]
  · have h1 : ¬ i.val < X := by omega
    have h2 : ¬ i.val < a := by omega
    simp only [enc, dif_neg h1, dif_neg h2, dif_neg hi]
    congr 1
    apply Fin.ext
    show i.val = a + X + (i.val - a - X)
    omega

theorem enc_rigid_L (a b h X : ℕ) {q' : ℕ} (hh : 0 < h) (hX : X = (q'+1)*h) (hXa : X < a)
    (hXb : X + h ≤ b) (VL VL' VR VR' : Fin (q'+1) → ℕ)
    (hVL : ∀ j, VL j < 2^h) (hVL' : ∀ j, VL' j < 2^h)
    (hVR : ∀ j, VR j < 2^h) (hVR' : ∀ j, VR' j < 2^h)
    (gL gL' : Fin (a - X) → Bool) (gR gR' : Fin (b - X) → Bool) (u : Fin (q'+1))
    (H : ∀ k : Fin (a+b), (k.val < u.val*h ∨ u.val*h + h ≤ k.val) →
      enc a b h X VL' VR' gL' gR' k = enc a b h X VL VR gL gR k) :
    (∀ j, j ≠ u → VL' j = VL j) ∧ VR' = VR ∧ gL' = gL ∧ gR' = gR := by
  have hmul : ∀ j : Fin (q'+1), j.val*h + h ≤ X := by
    intro j
    have := mul_step (h := h) j.isLt
    omega
  have huX := hmul u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    apply eq_of_bits (hVL' j) (hVL j)
    intro o ho
    have hjX := hmul j
    have hpos : j.val*h + o < a + b := by omega
    have hk : (j.val*h + o < u.val*h ∨ u.val*h + h ≤ j.val*h+o) := by
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
      · left
        have := mul_step (h := h) hlt
        omega
      · right
        have := mul_step (h := h) hgt
        omega
    have := H ⟨j.val*h+o, hpos⟩ hk
    rw [enc_L a b h X hh hX _ _ _ _ j o ho hpos, enc_L a b h X hh hX _ _ _ _ j o ho hpos] at this
    exact this
  · funext j
    apply eq_of_bits (hVR' j) (hVR j)
    intro o ho
    have hjX := hmul j
    have hpos : a + (j.val*h + o) < a + b := by omega
    have := H ⟨a + (j.val*h+o), hpos⟩
      (Or.inr (by show u.val*h + h ≤ a + (j.val*h+o); omega))
    rw [enc_R a b h X hh hX hXa _ _ _ _ j o ho hpos,
      enc_R a b h X hh hX hXa _ _ _ _ j o ho hpos] at this
    exact this
  · funext k
    have hk := k.isLt
    have hpos : X + k.val < a + b := by omega
    have := H ⟨X + k.val, hpos⟩ (Or.inr (by show u.val*h + h ≤ X + k.val; omega))
    rw [enc_gL, enc_gL] at this
    exact this
  · funext k
    have hk := k.isLt
    have hpos : a + X + k.val < a + b := by omega
    have := H ⟨a + X + k.val, hpos⟩ (Or.inr (by show u.val*h + h ≤ a + X + k.val; omega))
    rw [enc_gR, enc_gR] at this
    exact this

theorem enc_rigid_R (a b h X : ℕ) {q' : ℕ} (hh : 0 < h) (hX : X = (q'+1)*h) (hXa : X < a)
    (hXb : X + h ≤ b) (VL VL' VR VR' : Fin (q'+1) → ℕ)
    (hVL : ∀ j, VL j < 2^h) (hVL' : ∀ j, VL' j < 2^h)
    (hVR : ∀ j, VR j < 2^h) (hVR' : ∀ j, VR' j < 2^h)
    (gL gL' : Fin (a - X) → Bool) (gR gR' : Fin (b - X) → Bool) (v : Fin (q'+1))
    (H : ∀ k : Fin (a+b), (k.val < a + v.val*h ∨ a + v.val*h + h ≤ k.val) →
      enc a b h X VL' VR' gL' gR' k = enc a b h X VL VR gL gR k) :
    VL' = VL ∧ (∀ j, j ≠ v → VR' j = VR j) ∧ gL' = gL ∧ gR' = gR := by
  have hmul : ∀ j : Fin (q'+1), j.val*h + h ≤ X := by
    intro j
    have := mul_step (h := h) j.isLt
    omega
  have hvX := hmul v
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext j
    apply eq_of_bits (hVL' j) (hVL j)
    intro o ho
    have hjX := hmul j
    have hpos : j.val*h + o < a + b := by omega
    have := H ⟨j.val*h+o, hpos⟩ (Or.inl (by show j.val*h + o < a + v.val*h; omega))
    rw [enc_L a b h X hh hX _ _ _ _ j o ho hpos, enc_L a b h X hh hX _ _ _ _ j o ho hpos] at this
    exact this
  · intro j hj
    apply eq_of_bits (hVR' j) (hVR j)
    intro o ho
    have hjX := hmul j
    have hpos : a + (j.val*h + o) < a + b := by omega
    have hk : (a + (j.val*h + o) < a + v.val*h ∨ a + v.val*h + h ≤ a + (j.val*h+o)) := by
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
      · left
        have := mul_step (h := h) hlt
        omega
      · right
        have := mul_step (h := h) hgt
        omega
    have := H ⟨a + (j.val*h+o), hpos⟩ hk
    rw [enc_R a b h X hh hX hXa _ _ _ _ j o ho hpos,
      enc_R a b h X hh hX hXa _ _ _ _ j o ho hpos] at this
    exact this
  · funext k
    have hk := k.isLt
    have hpos : X + k.val < a + b := by omega
    have := H ⟨X + k.val, hpos⟩ (Or.inl (by show X + k.val < a + v.val*h; omega))
    rw [enc_gL, enc_gL] at this
    exact this
  · funext k
    have hk := k.isLt
    have hpos : a + X + k.val < a + b := by omega
    have := H ⟨a + X + k.val, hpos⟩
      (Or.inr (by show a + v.val*h + h ≤ a + X + k.val; omega))
    rw [enc_gR, enc_gR] at this
    exact this

theorem main (a b h s q' : ℕ) (hn : 0 < a+b) (hs : 0 < s) (hsh : s ≤ h)
    (hL : (q'+1)*h < a) (hR : (q'+1+1)*h ≤ b) :
    Goal (a+b) h ((q'+1)^2 * (2^s-1)^(2*(q'+1-1)) * 2^(a+b-(2*(q'+1)*s+(h-s)))) a hn := by
  have hh : 0 < h := lt_of_lt_of_le hs hsh
  obtain ⟨X, hX⟩ : ∃ X, X = (q'+1)*h := ⟨_, rfl⟩
  have hXa : X < a := by omega
  have hXb : X + h ≤ b := by
    have h9 : (q'+1+1)*h = (q'+1)*h + h := Nat.succ_mul (q'+1) h
    omega
  obtain ⟨z, hz⟩ : ∃ z, z = 2^(h-s) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 2^h - 2^(h-s) := ⟨_, rfl⟩
  have hzN : z + N ≤ 2^h := by
    have : 2^(h-s) ≤ 2^h := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le h s)
    omega
  have hmul : ∀ j : Fin (q'+1), j.val*h + h ≤ X := by
    intro j
    have := mul_step (h := h) j.isLt
    omega
  refine assemble (S := (Fin (q'+1) × Fin (q'+1)) × ((Fin q' → Fin N) × (Fin q' → Fin N)) ×
      Fin z × ((Fin (a - X) → Bool) × (Fin (b - X) → Bool))) hn ?_
    (fun t => enc a b h X (tv z N t.1.1 t.2.2.1 t.2.1.1) (tv z N t.1.2 t.2.2.1 t.2.1.2)
      t.2.2.2.1 t.2.2.2.2)
    (fun t => ⟨t.1.1.val*h + h, by have := hmul t.1.1; omega⟩)
    (fun t => ⟨a + t.1.2.val*h + h, by have := hmul t.1.2; omega⟩) a (by omega) ?_ ?_ ?_ ?_ ?_ ?_
  · subst hz hN
    have hN2 : 2^h - 2^(h-s) = (2^s-1) * 2^(h-s) := by
      rw [Nat.sub_mul, Nat.one_mul, ← pow_add, Nat.add_sub_of_le hsh]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_bool]
    rw [hN2]
    obtain ⟨d, rfl⟩ : ∃ d, h = s + d := ⟨h - s, by omega⟩
    have e0 : s + d - s = d := by omega
    rw [e0]
    have hexp : a+b-(2*(q'+1)*s+d) = d*q' + d*q' + (d + ((a - X) + (b - X))) := by
      have e1 : 2*(q'+1)*s = 2*(q'*s) + 2*s := by ring
      have e2 : X = q'*s + q'*d + s + d := by rw [hX]; ring
      have e3 : d*q' = q'*d := Nat.mul_comm _ _
      omega
    rw [hexp]
    apply le_of_eq
    simp only [Nat.add_sub_cancel]
    ring
  · intro t
    show 0 < t.1.1.val*h + h
    omega
  · intro t
    have := hmul t.1.1
    show t.1.1.val*h + h < a
    omega
  · intro t
    show a ≤ a + t.1.2.val*h + h
    omega
  · rintro x ⟨⟨u,v⟩,⟨μL,μR⟩,c,gL,gR⟩ Hw
    have H : ∀ k : Fin (a+b), k.val < a + b - h →
        x k = enc a b h X (tv z N u c μL) (tv z N v c μR) gL gR k := by
      intro k hk
      exact win_agree hn x _ ⟨0, hn⟩ Hw k k.val hk (by simp [Nat.mod_eq_of_lt k.isLt])
    exact ⟨((u,v),(μL,μR),c,(gL, _)), enc_close a b h X hXb _ _ gL gR x H⟩
  · rintro ⟨⟨u,v⟩,⟨μL,μR⟩,c,gL,gR⟩ ⟨⟨u',v'⟩,⟨μL',μR'⟩,c',gL',gR'⟩ Hw
    have Hoff := off_tile hn _ _ _ (u.val*h) rfl Hw
    obtain ⟨h1,h2,h3,h4⟩ := enc_rigid_L a b h X hh hX hXa hXb
      (tv z N u c μL) (tv z N u' c' μL') (tv z N v c μR) (tv z N v' c' μR')
      (tv_lt hzN _ _ _) (tv_lt hzN _ _ _) (tv_lt hzN _ _ _) (tv_lt hzN _ _ _)
      gL gL' gR gR' u Hoff
    obtain ⟨rfl, rfl⟩ := tv_rigid _ _ _ _ _ _ h1
    obtain ⟨rfl, rfl, rfl⟩ := tv_inj _ _ _ _ _ _ (congrFun h2)
    subst h3 h4
    rfl
  · rintro ⟨⟨u,v⟩,⟨μL,μR⟩,c,gL,gR⟩ ⟨⟨u',v'⟩,⟨μL',μR'⟩,c',gL',gR'⟩ Hw
    have Hoff := off_tile hn _ _ _ (a + v.val*h) rfl Hw
    obtain ⟨h1,h2,h3,h4⟩ := enc_rigid_R a b h X hh hX hXa hXb
      (tv z N u c μL) (tv z N u' c' μL') (tv z N v c μR) (tv z N v' c' μR')
      (tv_lt hzN _ _ _) (tv_lt hzN _ _ _) (tv_lt hzN _ _ _) (tv_lt hzN _ _ _)
      gL gL' gR gR' v Hoff
    obtain ⟨rfl, rfl, rfl⟩ := tv_inj _ _ _ _ _ _ (congrFun h1)
    obtain ⟨rfl, rfl⟩ := tv_rigid _ _ _ _ _ _ h2
    subst h3 h4
    rfl

end PEqualNP.Outside.L_lib_574_aux

theorem PEqualNP.Outside.L_lib_574 : (∀ (a b h s q : Nat) (hn : 0 < a+b), 0 < q → 0 < s → s ≤ h →
  q*h < a → (q+1)*h ≤ b →
  let n := a+b
  let M := q^2 * (2^s-1)^(2*(q-1)) * 2^(n-(2*q*s+(h-s)))
  let Word := Fin n → Bool
  let Pat := Fin (n-h) → Bool
  let Slot := Fin n × Pat
  let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
  let solutions := fun (tab : Slot → Bool) =>
    (Finset.univ : Finset Word).filter (fun x =>
      ∀ i : Fin n, tab (i,fun j => x (loc (i.val+j.val))) = true)
  ∃ (code : Fin M → Word) (base : Slot → Bool) (left right : Fin M → Slot),
    Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
    (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
      base (left i) = false ∧ base (right i) = false) ∧
    ∀ A B : Finset (Fin M), solutions (fun slot =>
      base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right)) =
        (A ∩ B).image code) := by
  intro a b h s q hn hq hs hsh hL hR
  obtain ⟨q', rfl⟩ : ∃ q', q = q'+1 := ⟨q-1, by omega⟩
  intro n M Word Pat Slot loc solutions
  exact PEqualNP.Outside.L_lib_574_aux.main a b h s q' hn hs hsh hL hR
