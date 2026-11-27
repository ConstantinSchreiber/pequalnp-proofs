import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25566_aux

def idx (k : ℕ) (hk : 0 < k) (a : ℕ) : Fin k := ⟨a % k, Nat.mod_lt _ hk⟩

def mix (k : ℕ) (hk : 0 < k) (d : ℕ) (word : Fin k → Bool) (p : Fin k) : Bool :=
  xor (xor (word p) (word (idx k hk (p.val + d))))
    (word (idx k hk (p.val + k - d % k)))

def outp (k : ℕ) (hk : 0 < k) (d : ℕ) (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (mix k hk d w i)
    (!(mix k hk d w (idx k hk (i.val + 1))) && mix k hk d w (idx k hk (i.val + 2)))

def mixed (k : ℕ) (hk : 0 < k) (d : ℕ) (x v : Fin k → Bool) (i : Fin k) : Bool :=
  xor (xor (outp k hk d x i) (outp k hk d (fun basePos => !(x basePos)) i))
    (xor (outp k hk d (fun j => xor (x j) (v j)) i)
      (outp k hk d (fun shiftedPos => !(xor (x shiftedPos) (v shiftedPos))) i))

def L (k : ℕ) (hk : 0 < k) (d : ℕ) (v : Fin k → Bool) (i : Fin k) : Bool :=
  xor (mix k hk d v (idx k hk (i.val + 1))) (mix k hk d v (idx k hk (i.val + 2)))

lemma bx3 (a b c : Bool) : xor (xor (!a) (!b)) (!c) = !(xor (xor a b) c) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma bx6 (a b c a' b' c' : Bool) :
    xor (xor (xor a a') (xor b b')) (xor c c') = xor (xor (xor a b) c) (xor (xor a' b') c') := by
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> rfl

lemma bx4 (a b c e : Bool) : xor (xor a b) (xor c e) = xor (xor a c) (xor b e) := by
  cases a <;> cases b <;> cases c <;> cases e <;> rfl

lemma bxx (a : Bool) : xor a a = false := by
  cases a <;> rfl

lemma xor_false_eq (a b : Bool) (h : xor a b = false) : a = b := by
  revert h
  cases a <;> cases b <;> decide

lemma b_per (A B X Z c : Bool) (h1 : xor (xor A B) X = c) (h2 : xor (xor B Z) A = c) :
    Z = X := by
  revert h1 h2
  cases A <;> cases B <;> cases X <;> cases Z <;> cases c <;> decide

lemma b_aaa (a c : Bool) (h : xor (xor a a) a = c) : a = c := by
  revert h
  cases a <;> cases c <;> decide

lemma mix_not (k : ℕ) (hk : 0 < k) (d : ℕ) (x : Fin k → Bool) (q : Fin k) :
    mix k hk d (fun b => !(x b)) q = !(mix k hk d x q) := by
  unfold mix
  exact bx3 _ _ _

lemma mix_add (k : ℕ) (hk : 0 < k) (d : ℕ) (x v : Fin k → Bool) (q : Fin k) :
    mix k hk d (fun j => xor (x j) (v j)) q = xor (mix k hk d x q) (mix k hk d v q) := by
  unfold mix
  exact bx6 _ _ _ _ _ _

lemma mixed_eq (k : ℕ) (hk : 0 < k) (d : ℕ) (x v : Fin k → Bool) (i : Fin k) :
    mixed k hk d x v i = L k hk d v i := by
  have e1 : ∀ q, mix k hk d (fun basePos => !(x basePos)) q = !(mix k hk d x q) :=
    fun q => mix_not k hk d x q
  have e2 : ∀ q, mix k hk d (fun j => xor (x j) (v j)) q
      = xor (mix k hk d x q) (mix k hk d v q) := fun q => mix_add k hk d x v q
  have e3 : ∀ q, mix k hk d (fun shiftedPos => !(xor (x shiftedPos) (v shiftedPos))) q
      = !(xor (mix k hk d x q) (mix k hk d v q)) := by
    intro q
    have h := mix_not k hk d (fun j => xor (x j) (v j)) q
    rw [e2] at h
    exact h
  unfold mixed outp L
  rw [e1, e1, e1, e2, e2, e2, e3, e3, e3]
  generalize mix k hk d x i = a0
  generalize mix k hk d x (idx k hk (i.val + 1)) = a1
  generalize mix k hk d x (idx k hk (i.val + 2)) = a2
  generalize mix k hk d v i = m0
  generalize mix k hk d v (idx k hk (i.val + 1)) = m1
  generalize mix k hk d v (idx k hk (i.val + 2)) = m2
  cases a0 <;> cases a1 <;> cases a2 <;> cases m0 <;> cases m1 <;> cases m2 <;> rfl

lemma L_add (k : ℕ) (hk : 0 < k) (d : ℕ) (v w : Fin k → Bool) (i : Fin k) :
    L k hk d (fun j => xor (v j) (w j)) i = xor (L k hk d v i) (L k hk d w i) := by
  unfold L
  rw [mix_add, mix_add]
  exact bx4 _ _ _ _

lemma idx_val (k : ℕ) (hk : 0 < k) (p : Fin k) : idx k hk p.val = p :=
  Fin.ext (Nat.mod_eq_of_lt p.isLt)

lemma idx_add (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    idx k hk ((idx k hk a).val + b) = idx k hk (a + b) :=
  Fin.ext (Nat.mod_add_mod a k b)

lemma idx_sub (k : ℕ) (hk : 0 < k) (n d : ℕ) :
    idx k hk ((idx k hk (n + d)).val + k - d % k) = idx k hk n := by
  apply Fin.ext
  show ((n + d) % k + k - d % k) % k = n % k
  have h1 : d % k < k := Nat.mod_lt _ hk
  have h2 : (n + d) % k + k - d % k = (n + d) % k + (k - d % k) := by omega
  rw [h2, Nat.mod_add_mod]
  have h3 : n + d + (k - d % k) = n + k * (d / k + 1) := by
    have h4 := Nat.div_add_mod d k
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [h3, Nat.add_mul_mod_self_left]

lemma rot_mem (k : ℕ) (hk : 0 < k) (U : Finset (Fin k → Bool))
    (hrot : ∀ a ∈ U, (fun slot : Fin k => a (idx k hk (slot.val + 1))) ∈ U) :
    ∀ (n : ℕ), ∀ a ∈ U, (fun slot : Fin k => a (idx k hk (slot.val + n))) ∈ U := by
  intro n
  induction n with
  | zero =>
    intro a ha
    have e : (fun slot : Fin k => a (idx k hk (slot.val + 0))) = a := by
      funext slot
      rw [Nat.add_zero, idx_val]
    rw [e]
    exact ha
  | succ n ih =>
    intro a ha
    have h1 := hrot _ (ih a ha)
    have e : (fun slot : Fin k => a (idx k hk (slot.val + (n + 1)))) =
        (fun slot : Fin k => a (idx k hk ((idx k hk (slot.val + 1)).val + n))) := by
      funext slot
      rw [idx_add, Nat.add_assoc, Nat.add_comm 1 n]
    rw [e]
    exact h1

lemma mix_mem (k : ℕ) (hk : 0 < k) (U : Finset (Fin k → Bool))
    (hadd : ∀ a ∈ U, ∀ b ∈ U, (fun j : Fin k => xor (a j) (b j)) ∈ U)
    (hrot : ∀ a ∈ U, (fun slot : Fin k => a (idx k hk (slot.val + 1))) ∈ U)
    (d : ℕ) : ∀ v ∈ U, mix k hk d v ∈ U := by
  intro v hv
  have hr := rot_mem k hk U hrot
  have h1 := hr d v hv
  have h2 := hr (k - d % k) v hv
  have h3 := hadd _ (hadd _ hv _ h1) _ h2
  have e : mix k hk d v = (fun j : Fin k =>
      xor (xor (v j) (v (idx k hk (j.val + d)))) (v (idx k hk (j.val + (k - d % k))))) := by
    funext p
    show xor (xor (v p) (v (idx k hk (p.val + d)))) (v (idx k hk (p.val + k - d % k))) =
      xor (xor (v p) (v (idx k hk (p.val + d)))) (v (idx k hk (p.val + (k - d % k))))
    have h4 : p.val + k - d % k = p.val + (k - d % k) := by
      have h5 := Nat.mod_lt d hk
      omega
    rw [h4]
  rw [e]
  exact h3

lemma L_mem (k : ℕ) (hk : 0 < k) (U : Finset (Fin k → Bool))
    (hadd : ∀ a ∈ U, ∀ b ∈ U, (fun j : Fin k => xor (a j) (b j)) ∈ U)
    (hrot : ∀ a ∈ U, (fun slot : Fin k => a (idx k hk (slot.val + 1))) ∈ U)
    (d : ℕ) : ∀ v ∈ U, L k hk d v ∈ U := by
  intro v hv
  have hm := mix_mem k hk U hadd hrot d v hv
  have hr := rot_mem k hk U hrot
  exact hadd _ (hr 1 _ hm) _ (hr 2 _ hm)

lemma ker (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) (d : ℕ) (v : Fin k → Bool)
    (hL : ∀ i, L k hk d v i = false) : ∃ c : Bool, ∀ p, v p = c := by
  have hy : ∀ n : ℕ, mix k hk d v (idx k hk (n + 1)) = mix k hk d v (idx k hk (n + 2)) := by
    intro n
    have h := hL (idx k hk n)
    unfold L at h
    rw [idx_add, idx_add] at h
    exact xor_false_eq _ _ h
  have hy1 : ∀ m : ℕ, mix k hk d v (idx k hk (m + 1)) = mix k hk d v (idx k hk 1) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => exact (hy m).symm.trans ih
  have hyc : ∀ p : Fin k, mix k hk d v p = mix k hk d v (idx k hk 1) := by
    intro p
    have e : idx k hk ((p.val + k - 1) + 1) = p := by
      apply Fin.ext
      show ((p.val + k - 1) + 1) % k = p.val
      have h1 : p.val + k - 1 + 1 = p.val + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
    have h2 := hy1 (p.val + k - 1)
    rw [e] at h2
    exact h2
  obtain ⟨c, hc⟩ : ∃ c, ∀ p : Fin k, mix k hk d v p = c := ⟨_, hyc⟩
  have hR : ∀ n : ℕ, xor (xor (v (idx k hk (n + d))) (v (idx k hk (n + d + d))))
      (v (idx k hk n)) = c := by
    intro n
    have h := hc (idx k hk (n + d))
    unfold mix at h
    rw [idx_add, idx_sub] at h
    exact h
  have hP : ∀ n : ℕ, v (idx k hk (n + d + d + d)) = v (idx k hk n) := by
    intro n
    exact b_per _ _ _ _ _ (hR n) (hR (n + d))
  have hPq : ∀ q n : ℕ, v (idx k hk (n + 3 * d * q)) = v (idx k hk n) := by
    intro q
    induction q with
    | zero =>
      intro n
      rw [Nat.mul_zero, Nat.add_zero]
    | succ q ih =>
      intro n
      have e : n + 3 * d * (q + 1) = n + 3 * d * q + d + d + d := by ring
      rw [e, hP, ih]
  have hK : ∀ n : ℕ, idx k hk (n + k * d) = idx k hk n :=
    fun n => Fin.ext (Nat.add_mul_mod_self_left n k d)
  have hD : ∀ n : ℕ, v (idx k hk (n + d)) = v (idx k hk n) := by
    intro n
    have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h
    · obtain ⟨q, hq⟩ : ∃ q, k = 3 * q + 1 := ⟨k / 3, by omega⟩
      have e : n + d + 3 * d * q = n + k * d := by
        rw [hq]
        ring
      rw [← hPq q (n + d), e, hK]
    · obtain ⟨q, hq⟩ : ∃ q, k = 3 * q + 2 := ⟨k / 3, by omega⟩
      have h2 : ∀ m : ℕ, v (idx k hk (m + d + d)) = v (idx k hk m) := by
        intro m
        have e : m + d + d + 3 * d * q = m + k * d := by
          rw [hq]
          ring
        rw [← hPq q (m + d + d), e, hK]
      exact (h2 (n + d)).symm.trans (hP n)
  refine ⟨c, fun p => ?_⟩
  have h := hR p.val
  rw [hD (p.val + d), hD p.val, idx_val] at h
  exact b_aaa _ _ h

lemma main (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) (U : Finset (Fin k → Bool))
    (hadd : ∀ a ∈ U, ∀ b ∈ U, (fun j : Fin k => xor (a j) (b j)) ∈ U)
    (hrot : ∀ a ∈ U, (fun slot : Fin k => a (idx k hk (slot.val + 1))) ∈ U)
    (htrue : (fun _ : Fin k => true) ∉ U)
    (d : ℕ) (x target : Fin k → Bool) :
    (U.filter (fun direction => mixed k hk d x direction = target)).card =
      if target ∈ U then 1 else 0 := by
  have hm : ∀ v, mixed k hk d x v = L k hk d v := fun v => funext (mixed_eq k hk d x v)
  have hLU := L_mem k hk U hadd hrot d
  have hinj : ∀ a ∈ U, ∀ b ∈ U, L k hk d a = L k hk d b → a = b := by
    intro a ha b hb hab
    have hab' : ∀ i, L k hk d (fun j => xor (a j) (b j)) i = false := by
      intro i
      rw [L_add, hab]
      exact bxx _
    obtain ⟨c, hc⟩ := ker k hk h3 d _ hab'
    cases c with
    | true =>
      exfalso
      apply htrue
      have e : (fun _ : Fin k => true) = (fun j => xor (a j) (b j)) :=
        funext (fun p => (hc p).symm)
      rw [e]
      exact hadd a ha b hb
    | false =>
      funext p
      exact xor_false_eq _ _ (hc p)
  have himg : U.image (L k hk d) = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact hLU a ha
    · have hcard : (U.image (L k hk d)).card = U.card := by
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        exact hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
      exact le_of_eq hcard.symm
  by_cases ht : target ∈ U
  · simp only [ht, ↓reduceIte]
    have ht' : target ∈ U.image (L k hk d) := by
      rw [himg]
      exact ht
    obtain ⟨a, ha, hat⟩ := Finset.mem_image.mp ht'
    rw [Finset.card_eq_one]
    refine ⟨a, ?_⟩
    ext b
    rw [Finset.mem_filter, Finset.mem_singleton, hm]
    constructor
    · rintro ⟨hb, hbt⟩
      exact hinj b hb a ha (hbt.trans hat.symm)
    · rintro rfl
      exact ⟨ha, hat⟩
  · simp only [ht, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b hb hbt
    rw [hm] at hbt
    apply ht
    rw [← hbt]
    exact hLU b hb

end PEqualNP.Outside.L_meta_25566_aux

theorem PEqualNP.Outside.L_meta_25566 : (∀ (k : Nat) (hk : 0 < k), k % 3 ≠ 0 →
  let index := fun (a : Nat) => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : Fin k → Bool) (j : Fin k) => xor (x j) (y j)
  ∀ (U : Finset (Fin k → Bool)),
    (∀ a ∈ U, ∀ b ∈ U, add a b ∈ U) →
    (∀ a ∈ U, (fun slot : Fin k => a (index (slot.val + 1))) ∈ U) →
    (fun _ : Fin k => true) ∉ U →
  ∀ (d : Nat), (d = 1 ∨ d = 2) →
  let mix := fun (word : Fin k → Bool) (p : Fin k) =>
    xor (xor (word p) (word (index (p.val + d))))
      (word (index (p.val + k - d % k)))
  let output := fun (w : Fin k → Bool) (i : Fin k) =>
    let y := mix w
    xor (y i) (!(y (index (i.val + 1))) && y (index (i.val + 2)))
  ∀ (x target : Fin k → Bool),
    let mixed := fun (v : Fin k → Bool) (i : Fin k) =>
      xor (xor (output x i) (output (fun basePos => !(x basePos)) i))
        (xor (output (add x v) i) (output (fun shiftedPos => !((add x v) shiftedPos)) i))
    (U.filter (fun direction => mixed direction = target)).card = if target ∈ U then 1 else 0) := by
  intro k hk h3 index add U hadd hrot htrue d _ mix output x target mixed
  exact PEqualNP.Outside.L_meta_25566_aux.main k hk h3 U hadd hrot htrue d x target
