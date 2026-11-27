import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_572_aux

open PEqualNP.CircuitLowerBounds

abbrev V := ℕ → Bool

def fl (x : V) (c : ℕ) : V := Function.update x c (!x c)

lemma fl_apply (x : V) (c k : ℕ) : fl x c k = if k = c then !x c else x k := by
  unfold fl
  exact Function.update_apply _ _ _ _

lemma bnn (t : Bool) : t ≠ !t := by cases t <;> decide
lemma bnn' (t : Bool) : (!t) ≠ t := by cases t <;> decide
lemma bne_not (a b : Bool) (h : a ≠ b) : a = !b := by
  revert h; cases a <;> cases b <;> decide
lemma bneq3 (a b c : Bool) (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> decide
lemma bneq3' (a b c : Bool) (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  revert h1 h2; cases a <;> cases b <;> cases c <;> decide

def Ign (F : V → Bool) (i : ℕ) : Prop := ∀ (x : V) (v : Bool), F (Function.update x i v) = F x

def Chg (F : V → Bool) (c : ℕ) (β τ : Bool) : Prop :=
  ∃ y : V, y c = β ∧ F y = τ ∧ F (fl y c) = !τ

def Binate (F : V → Bool) (c : ℕ) : Prop := ∃ β τ, Chg F c β τ ∧ Chg F c β (!τ)

def Pat (N : ℕ) (F : V → Bool) : Prop :=
  ∃ (a b c : ℕ) (p : V) (v t : Bool), a < N ∧ b < N ∧ c < N ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    F p = t ∧ F (fl p b) = !t ∧ F (fl p c) = !t ∧
    F (Function.update (fl p c) a v) = !t ∧ F (fl (Function.update (fl p c) a v) b) = t ∧
    Chg F c (p c) (!t)

def Lv (F : V → Bool) (k m : ℕ) : Prop :=
  ∃ T : Finset ℕ, (∀ i, i ∉ T → Ign F i) ∧ T.card + m ≤ k + 1

def Inv (N : ℕ) (F : V → Bool) (k : ℕ) : Prop :=
  Lv F k 0 ∧ (Lv F k 1 ∨ ∀ c, ¬ Binate F c) ∧ (Lv F k 2 ∨ ¬ Pat N F)

def GateOK (N cg : ℕ) (G : V → Bool) : Prop :=
  ∃ D : Finset ℕ, (∀ d ∈ D, d < N) ∧ D.card ≤ 1 + cg ∧
    (∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y) ∧
    (∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p) ∧
    (∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)

lemma ign_ext (F : V → Bool) (D : Finset ℕ) : (∀ d ∈ D, Ign F d) →
    ∀ x y : V, (∀ k, k ∉ D → x k = y k) → F x = F y := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro _ x y hxy
    have : x = y := funext (fun k => hxy k (by simp))
    rw [this]
  | insert d D hd ih =>
    intro h x y hxy
    rw [← h d (Finset.mem_insert_self d D) x (y d)]
    apply ih (fun e he => h e (Finset.mem_insert_of_mem he))
    intro k hk
    by_cases hkd : k = d
    · rw [hkd]; simp
    · rw [Function.update_of_ne hkd]
      exact hxy k (by simp [hk, hkd])

lemma pat_mono {N : ℕ} {F : V → Bool} (h : Pat N F) : Pat (N + 1) F := by
  obtain ⟨a, b, c, p, v, t, haN, hbN, hcN, r⟩ := h
  exact ⟨a, b, c, p, v, t, by omega, by omega, by omega, r⟩

lemma pat_binate {N : ℕ} {F : V → Bool} (h : Pat N F) :
    ∃ b c, b ≠ c ∧ Binate F b ∧ Binate F c := by
  obtain ⟨a, b, c, p, v, t, haN, hbN, hcN, hab, hac, hbc, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨b, c, hbc, ⟨p b, t, ⟨p, rfl, h0, h1⟩,
    ⟨Function.update (fl p c) a v, ?_, h3, ?_⟩⟩, ⟨p c, t, ⟨p, rfl, h0, h2⟩, h5⟩⟩
  · rw [Function.update_of_ne (Ne.symm hab), fl_apply, if_neg hbc]
  · rw [h4, Bool.not_not]

set_option maxHeartbeats 400000 in
lemma pt_bc (N : ℕ) (F' G : V → Bool) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d < N) (hcard : D.card ≤ 2)
    (hI : ∀ d ∈ D, Ign F' d)
    (hG : ∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y)
    (GP1 : ∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p)
    (GP3 : ∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)
    (a b c : ℕ) (p y : V) (v t : Bool) (haN : a < N) (hbN : b < N) (hcN : c < N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : F' (Function.update p N (G p)) = t)
    (h1 : F' (Function.update (fl p b) N (G (fl p b))) = !t)
    (h2 : F' (Function.update (fl p c) N (G (fl p c))) = !t)
    (h3 : F' (Function.update (Function.update (fl p c) a v) N
      (G (Function.update (fl p c) a v))) = !t)
    (h4 : F' (Function.update (fl (Function.update (fl p c) a v) b) N
      (G (fl (Function.update (fl p c) a v) b))) = t)
    (hyc : y c = p c)
    (hy1 : F' (Function.update y N (G y)) = !t)
    (hy2 : F' (Function.update (fl y c) N (G (fl y c))) = !!t)
    (hbD : b ∈ D) (hcD : c ∈ D) : False := by
  have E := ign_ext F' D hI
  have hND : N ∉ D := fun h => absurd (hD N h) (lt_irrefl N)
  have haN' : a ≠ N := by omega
  have hbN' : b ≠ N := by omega
  have hcN' : c ≠ N := by omega
  have haD : a ∉ D := by
    intro haD
    have hs : ({a, b, c} : Finset ℕ) ⊆ D := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have h3c : ({a, b, c} : Finset ℕ).card = 3 := by
      rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩
    have := Finset.card_le_card hs
    omega
  have g1 : G (fl p b) ≠ G p := by
    intro h
    have e := E (Function.update (fl p b) N (G (fl p b))) (Function.update p N (G p))
      (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
    rw [e, h0] at h1
    exact bnn t h1
  have g2n : G (fl p c) ≠ G p := by
    intro h
    have e := E (Function.update (fl p c) N (G (fl p c))) (Function.update p N (G p))
      (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
    rw [e, h0] at h2
    exact bnn t h2
  apply GP1 p b c hbc g1 g2n
  by_contra hne
  have e5 : G (fl (fl p c) b) = G (fl p c) := bneq3 _ _ _ hne g2n
  have e3 : G (Function.update (fl p c) a v) = G (fl p c) :=
    hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
  have e4 : G (fl (Function.update (fl p c) a v) b) = G (fl (fl p c) b) :=
    hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
  have e := E (Function.update (fl (Function.update (fl p c) a v) b) N
      (G (fl (Function.update (fl p c) a v) b)))
    (Function.update (Function.update (fl p c) a v) N (G (Function.update (fl p c) a v)))
    (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
  rw [e, h3] at h4
  exact bnn' t h4

set_option maxHeartbeats 400000 in
lemma pt_b (N : ℕ) (F' G : V → Bool) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d < N) (hcard : D.card ≤ 2)
    (hI : ∀ d ∈ D, Ign F' d)
    (hG : ∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y)
    (GP1 : ∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p)
    (GP3 : ∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)
    (a b c : ℕ) (p y : V) (v t : Bool) (haN : a < N) (hbN : b < N) (hcN : c < N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : F' (Function.update p N (G p)) = t)
    (h1 : F' (Function.update (fl p b) N (G (fl p b))) = !t)
    (h2 : F' (Function.update (fl p c) N (G (fl p c))) = !t)
    (h3 : F' (Function.update (Function.update (fl p c) a v) N
      (G (Function.update (fl p c) a v))) = !t)
    (h4 : F' (Function.update (fl (Function.update (fl p c) a v) b) N
      (G (fl (Function.update (fl p c) a v) b))) = t)
    (hyc : y c = p c)
    (hy1 : F' (Function.update y N (G y)) = !t)
    (hy2 : F' (Function.update (fl y c) N (G (fl y c))) = !!t)
    (hbD : b ∈ D) (hcD : c ∉ D) : Pat (N + 1) F' := by
  have E := ign_ext F' D hI
  have hND : N ∉ D := fun h => absurd (hD N h) (lt_irrefl N)
  have haN' : a ≠ N := by omega
  have hbN' : b ≠ N := by omega
  have hcN' : c ≠ N := by omega
  have gc : G (fl p c) = G p :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have g1 : G (fl p b) = !G p := by
    apply bne_not
    intro h
    have e := E (Function.update (fl p b) N (G (fl p b))) (Function.update p N (G p))
      (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
    rw [e, h0] at h1
    exact bnn t h1
  have gy : G (fl y c) = G y :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have h3' : F' (Function.update (Function.update (fl (Function.update p N (G p)) c) a v) N
      (G (Function.update (fl p c) a v))) = !t :=
    (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h3
  have h4' : F' (Function.update (Function.update (fl (Function.update p N (G p)) c) a v) N
      (G (fl (Function.update (fl p c) a v) b))) = t :=
    (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h4
  have k2 : G (Function.update (fl p c) a v) = G p ∧
      G (fl (Function.update (fl p c) a v) b) = !G p := by
    by_cases haD : a ∈ D
    · have eX : F' (Function.update (fl (Function.update p N (G p)) c) a v) = !t :=
        (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h2
      have kb : G (fl (Function.update (fl p c) a v) b) ≠ G p := by
        intro h
        rw [h] at h4'
        have e := E (Function.update (Function.update (fl (Function.update p N (G p)) c) a v) N
            (G p))
          (Function.update (fl (Function.update p N (G p)) c) a v)
          (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
        rw [e, eX] at h4'
        exact bnn' t h4'
      have kn : G (Function.update (fl p c) a v) ≠ G (fl (Function.update (fl p c) a v) b) := by
        intro h
        rw [h, h4'] at h3'
        exact bnn t h3'
      exact ⟨bneq3' _ _ _ kn kb, bne_not _ _ kb⟩
    · have e1 : G (Function.update (fl p c) a v) = G p :=
        hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
      refine ⟨e1, bne_not _ _ ?_⟩
      intro h
      rw [h] at h4'
      rw [e1, h4'] at h3'
      exact bnn t h3'
  obtain ⟨k2a, k2b⟩ := k2
  refine ⟨a, N, c, Function.update p N (G p), v, t, by omega, by omega, by omega, haN', hac,
    Ne.symm hcN', h0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h1
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h2
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h3'
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h4'
  · refine ⟨Function.update y N (G y), ?_, hy1, ?_⟩
    · simp only [Function.update_apply]; grind
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans hy2

set_option maxHeartbeats 400000 in
lemma pt_c (N : ℕ) (F' G : V → Bool) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d < N) (hcard : D.card ≤ 2)
    (hI : ∀ d ∈ D, Ign F' d)
    (hG : ∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y)
    (GP1 : ∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p)
    (GP3 : ∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)
    (a b c : ℕ) (p y : V) (v t : Bool) (haN : a < N) (hbN : b < N) (hcN : c < N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : F' (Function.update p N (G p)) = t)
    (h1 : F' (Function.update (fl p b) N (G (fl p b))) = !t)
    (h2 : F' (Function.update (fl p c) N (G (fl p c))) = !t)
    (h3 : F' (Function.update (Function.update (fl p c) a v) N
      (G (Function.update (fl p c) a v))) = !t)
    (h4 : F' (Function.update (fl (Function.update (fl p c) a v) b) N
      (G (fl (Function.update (fl p c) a v) b))) = t)
    (hyc : y c = p c)
    (hy1 : F' (Function.update y N (G y)) = !t)
    (hy2 : F' (Function.update (fl y c) N (G (fl y c))) = !!t)
    (hbD : b ∉ D) (hcD : c ∈ D) : Pat (N + 1) F' := by
  have E := ign_ext F' D hI
  have hND : N ∉ D := fun h => absurd (hD N h) (lt_irrefl N)
  have haN' : a ≠ N := by omega
  have hbN' : b ≠ N := by omega
  have hcN' : c ≠ N := by omega
  have gb : G (fl p b) = G p :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have g2n : G (fl p c) ≠ G p := by
    intro h
    have e := E (Function.update (fl p c) N (G (fl p c))) (Function.update p N (G p))
      (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
    rw [e, h0] at h2
    exact bnn t h2
  have g2 : G (fl p c) = !G p := bne_not _ _ g2n
  have gyn : G (fl y c) ≠ G y := by
    intro h
    have e := E (Function.update (fl y c) N (G (fl y c))) (Function.update y N (G y))
      (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
    rw [e, hy1] at hy2
    exact bnn (!t) hy2
  have gy : G (fl y c) = !G y := bne_not _ _ gyn
  have gyp : G y = G p := GP3 c p y hyc g2n gyn
  have k2b : G (fl (Function.update (fl p c) a v) b) = G (Function.update (fl p c) a v) :=
    hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
  have k2 : G (Function.update (fl p c) a v) = !G p := by
    by_cases haD : a ∈ D
    · apply bne_not
      intro h
      have e := E (Function.update (Function.update (fl p c) a v) N
          (G (Function.update (fl p c) a v))) (Function.update p N (G p))
        (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)
      rw [e, h0] at h3
      exact bnn t h3
    · have e1 : G (Function.update (fl p c) a v) = G (fl p c) :=
        hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
      rw [e1, g2]
  refine ⟨a, b, N, Function.update p N (G p), v, t, by omega, by omega, by omega, hab, haN',
    hbN', h0, ?_, ?_, ?_, ?_, ?_⟩
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h1
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h2
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h3
  · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h4
  · refine ⟨Function.update y N (G y), ?_, hy1, ?_⟩
    · simp only [Function.update_apply]; grind
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans hy2

set_option maxHeartbeats 400000 in
lemma pt_n (N : ℕ) (F' G : V → Bool) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d < N) (hcard : D.card ≤ 2)
    (hI : ∀ d ∈ D, Ign F' d)
    (hG : ∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y)
    (GP1 : ∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p)
    (GP3 : ∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)
    (a b c : ℕ) (p y : V) (v t : Bool) (haN : a < N) (hbN : b < N) (hcN : c < N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : F' (Function.update p N (G p)) = t)
    (h1 : F' (Function.update (fl p b) N (G (fl p b))) = !t)
    (h2 : F' (Function.update (fl p c) N (G (fl p c))) = !t)
    (h3 : F' (Function.update (Function.update (fl p c) a v) N
      (G (Function.update (fl p c) a v))) = !t)
    (h4 : F' (Function.update (fl (Function.update (fl p c) a v) b) N
      (G (fl (Function.update (fl p c) a v) b))) = t)
    (hyc : y c = p c)
    (hy1 : F' (Function.update y N (G y)) = !t)
    (hy2 : F' (Function.update (fl y c) N (G (fl y c))) = !!t)
    (hbD : b ∉ D) (hcD : c ∉ D) : Pat (N + 1) F' := by
  have E := ign_ext F' D hI
  have hND : N ∉ D := fun h => absurd (hD N h) (lt_irrefl N)
  have haN' : a ≠ N := by omega
  have hbN' : b ≠ N := by omega
  have hcN' : c ≠ N := by omega
  have gb : G (fl p b) = G p :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have gc : G (fl p c) = G p :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have gy : G (fl y c) = G y :=
    hG _ _ (by intro d hd; simp only [fl_apply]; grind)
  have k2b : G (fl (Function.update (fl p c) a v) b) = G (Function.update (fl p c) a v) :=
    hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
  by_cases haD : a ∈ D
  · refine ⟨N, b, c, Function.update p N (G p), G (Function.update (fl p c) a v), t,
      by omega, by omega, by omega, Ne.symm hbN', Ne.symm hcN', hbc, h0, ?_, ?_, ?_, ?_, ?_⟩
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h1
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h2
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h3
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h4
    · refine ⟨Function.update y N (G y), ?_, hy1, ?_⟩
      · simp only [Function.update_apply]; grind
      · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans hy2
  · have k2 : G (Function.update (fl p c) a v) = G p :=
      hG _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
    refine ⟨a, b, c, Function.update p N (G p), v, t, by omega, by omega, by omega, hab, hac,
      hbc, h0, ?_, ?_, ?_, ?_, ?_⟩
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h1
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h2
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h3
    · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans h4
    · refine ⟨Function.update y N (G y), ?_, hy1, ?_⟩
      · simp only [Function.update_apply]; grind
      · exact (E _ _ (by intro k hk; simp only [fl_apply, Function.update_apply]; grind)).trans hy2

lemma pat_transfer (N : ℕ) (F F' G : V → Bool) (D : Finset ℕ)
    (hF : ∀ x, F x = F' (Function.update x N (G x)))
    (hD : ∀ d ∈ D, d < N) (hcard : D.card ≤ 2)
    (hI : ∀ d ∈ D, Ign F' d)
    (hG : ∀ x y : V, (∀ d ∈ D, x d = y d) → G x = G y)
    (GP1 : ∀ (p : V) (b c : ℕ), b ≠ c → G (fl p b) ≠ G p → G (fl p c) ≠ G p →
      G (fl (fl p c) b) ≠ G p)
    (GP3 : ∀ (c : ℕ) (p y : V), y c = p c → G (fl p c) ≠ G p → G (fl y c) ≠ G y → G y = G p)
    (hP : Pat N F) : Pat (N + 1) F' := by
  obtain ⟨a, b, c, p, v, t, haN, hbN, hcN, hab, hac, hbc, h0, h1, h2, h3, h4, y, hyc, hy1, hy2⟩ := hP
  rw [hF] at h0 h1 h2 h3 h4 hy1 hy2
  by_cases hbD : b ∈ D
  · by_cases hcD : c ∈ D
    · exact (pt_bc N F' G D hD hcard hI hG GP1 GP3 a b c p y v t haN hbN hcN hab hac hbc
        h0 h1 h2 h3 h4 hyc hy1 hy2 hbD hcD).elim
    · exact pt_b N F' G D hD hcard hI hG GP1 GP3 a b c p y v t haN hbN hcN hab hac hbc
        h0 h1 h2 h3 h4 hyc hy1 hy2 hbD hcD
  · by_cases hcD : c ∈ D
    · exact pt_c N F' G D hD hcard hI hG GP1 GP3 a b c p y v t haN hbN hcN hab hac hbc
        h0 h1 h2 h3 h4 hyc hy1 hy2 hbD hcD
    · exact pt_n N F' G D hD hcard hI hG GP1 GP3 a b c p y v t haN hbN hcN hab hac hbc
        h0 h1 h2 h3 h4 hyc hy1 hy2 hbD hcD


lemma step (N cg k' : ℕ) (F F' G : V → Bool)
    (hF : ∀ x, F x = F' (Function.update x N (G x)))
    (hGok : GateOK N cg G) (hcg : cg ≤ 1) (IH : Inv (N + 1) F' k') : Inv N F (k' + cg) := by
  classical
  obtain ⟨D, hD, hcard, hGD, GP1, GP3⟩ := hGok
  obtain ⟨I0, I1, I2⟩ := IH
  by_cases hN : Ign F' N
  · have hFF : F = F' := by
      funext x
      rw [hF]
      exact hN x (G x)
    rw [hFF]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨T, hT, hc⟩ := I0
      exact ⟨T, hT, by omega⟩
    · rcases I1 with ⟨T, hT, hc⟩ | h
      · exact Or.inl ⟨T, hT, by omega⟩
      · exact Or.inr h
    · rcases I2 with ⟨T, hT, hc⟩ | h
      · exact Or.inl ⟨T, hT, by omega⟩
      · exact Or.inr (fun hp => h (pat_mono hp))
  · have hND : N ∉ D := fun h => absurd (hD N h) (lt_irrefl N)
    have hIgnN : Ign F N := by
      intro x v
      rw [hF, hF]
      have e : G (Function.update x N v) = G x :=
        hGD _ _ (fun d hd => Function.update_of_ne (fun h => hND (by rw [← h]; exact hd)) _ _)
      rw [e, Function.update_idem]
    have L : ∀ m, Lv F' k' m →
        Lv F (k' + cg) (m + (D.filter (fun d => ¬ Ign F' d)).card) := by
      rintro m ⟨T, hT, hc⟩
      have hNT : N ∈ T := by
        by_contra h
        exact hN (hT N h)
      refine ⟨T.erase N ∪ D.filter (fun d => Ign F' d), ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_union, not_or, Finset.mem_erase, Finset.mem_filter] at hi
        obtain ⟨hi1, hi2⟩ := hi
        by_cases hiN : i = N
        · rw [hiN]; exact hIgnN
        · have hiT : i ∉ T := fun h => hi1 ⟨hiN, h⟩
          have hiF' : Ign F' i := hT i hiT
          have hiD : i ∉ D := fun h => hi2 ⟨h, hiF'⟩
          intro x v
          rw [hF, hF]
          have e : G (Function.update x i v) = G x :=
            hGD _ _ (fun d hd => Function.update_of_ne (fun h => hiD (by rw [← h]; exact hd)) _ _)
          rw [e, Function.update_comm hiN]
          exact hiF' _ _
      · have h1 : (T.erase N ∪ D.filter (fun d => Ign F' d)).card ≤
            (T.erase N).card + (D.filter (fun d => Ign F' d)).card := Finset.card_union_le _ _
        have h2 : (T.erase N).card = T.card - 1 := Finset.card_erase_of_mem hNT
        have h3 : 0 < T.card := Finset.card_pos.mpr ⟨N, hNT⟩
        have h4 : (D.filter (fun d => Ign F' d)).card + (D.filter (fun d => ¬ Ign F' d)).card
            = D.card := Finset.card_filter_add_card_filter_not _
        omega
    have C1 : ∀ c β τ, c ∉ D → Chg F c β τ → Chg F' c β τ := by
      rintro c β τ hcD ⟨y, hy, h1, h2⟩
      have hcN : c ≠ N := by
        intro e
        rw [e] at h2
        have e2 : F (fl y N) = F y := hIgnN y (!y N)
        rw [e2, h1] at h2
        exact bnn τ h2
      have e : G (fl y c) = G y :=
        hGD _ _ (by intro d hd; simp only [fl_apply, Function.update_apply]; grind)
      rw [hF] at h1 h2
      rw [e] at h2
      refine ⟨Function.update y N (G y), ?_, h1, ?_⟩
      · rw [Function.update_of_ne hcN]; exact hy
      · exact (congrArg F' (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h2
    have C2 : ∀ c β τ, c ∈ D → Ign F' c → Chg F c β τ →
        ∃ y : V, y c = β ∧ G (fl y c) ≠ G y ∧ F' (Function.update y N (G y)) = τ ∧
          F' (fl (Function.update y N (G y)) N) = !τ := by
      rintro c β τ hcD hcI ⟨y, hy, h1, h2⟩
      have hcN : c ≠ N := fun h => hND (by rw [← h]; exact hcD)
      rw [hF] at h1 h2
      have e1 : F' (Function.update (fl y c) N (G (fl y c))) =
          F' (Function.update y N (G (fl y c))) := by
        have e0 : Function.update (fl y c) N (G (fl y c)) =
            Function.update (Function.update y N (G (fl y c))) c (!y c) := by
          funext k; simp only [fl_apply, Function.update_apply]; grind
        rw [e0]
        exact hcI _ _
      rw [e1] at h2
      have hne : G (fl y c) ≠ G y := by
        intro h
        rw [h, h1] at h2
        exact bnn τ h2
      have hne' : G (fl y c) = !G y := bne_not _ _ hne
      refine ⟨y, hy, hne, h1, ?_⟩
      exact (congrArg F' (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h2
    have B : ∀ c, Binate F c → (∀ c', ¬ Binate F' c') → c ∈ D ∧ ¬ Ign F' c := by
      rintro c ⟨β, τ, hc1, hc2⟩ hno
      by_cases hcD : c ∈ D
      · refine ⟨hcD, fun hcI => ?_⟩
        obtain ⟨y1, hy1, hg1, ha1, hb1⟩ := C2 c β τ hcD hcI hc1
        obtain ⟨y2, hy2, hg2, ha2, hb2⟩ := C2 c β (!τ) hcD hcI hc2
        have hGy : G y2 = G y1 := GP3 c y1 y2 (by rw [hy1, hy2]) hg1 hg2
        refine hno N ⟨G y1, τ, ⟨Function.update y1 N (G y1), by simp, ha1, hb1⟩,
          ⟨Function.update y2 N (G y2), by simp [hGy], ha2, hb2⟩⟩
      · exact absurd ⟨β, τ, C1 c β τ hcD hc1, C1 c β (!τ) hcD hc2⟩ (hno c)
    have L0 := L 0 I0
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨T, hT, hc⟩ := L0
      exact ⟨T, hT, by omega⟩
    · by_cases h1 : 1 ≤ (D.filter (fun d => ¬ Ign F' d)).card
      · obtain ⟨T, hT, hc⟩ := L0
        exact Or.inl ⟨T, hT, by omega⟩
      · rcases I1 with h | h
        · obtain ⟨T, hT, hc⟩ := L 1 h
          exact Or.inl ⟨T, hT, by omega⟩
        · refine Or.inr (fun c hc => ?_)
          obtain ⟨hcD, hcI⟩ := B c hc h
          have hm : c ∈ D.filter (fun d => ¬ Ign F' d) := Finset.mem_filter.mpr ⟨hcD, hcI⟩
          have := Finset.card_pos.mpr ⟨c, hm⟩
          omega
    · by_cases h2 : 2 ≤ (D.filter (fun d => ¬ Ign F' d)).card
      · obtain ⟨T, hT, hc⟩ := L0
        exact Or.inl ⟨T, hT, by omega⟩
      · by_cases h1 : 1 ≤ (D.filter (fun d => ¬ Ign F' d)).card
        · rcases I1 with h | h
          · obtain ⟨T, hT, hc⟩ := L 1 h
            exact Or.inl ⟨T, hT, by omega⟩
          · refine Or.inr (fun hp => ?_)
            obtain ⟨b, c, hbc, hb, hc⟩ := pat_binate hp
            obtain ⟨hbD, hbI⟩ := B b hb h
            obtain ⟨hcD, hcI⟩ := B c hc h
            have hbm : b ∈ D.filter (fun d => ¬ Ign F' d) := Finset.mem_filter.mpr ⟨hbD, hbI⟩
            have hcm : c ∈ D.filter (fun d => ¬ Ign F' d) := Finset.mem_filter.mpr ⟨hcD, hcI⟩
            have := Finset.one_lt_card.mpr ⟨b, hbm, c, hcm, hbc⟩
            omega
        · rcases I2 with h | h
          · obtain ⟨T, hT, hc⟩ := L 2 h
            exact Or.inl ⟨T, hT, by omega⟩
          · refine Or.inr (fun hp => h ?_)
            have hI : ∀ d ∈ D, Ign F' d := by
              intro d hd
              by_contra hdI
              have hm : d ∈ D.filter (fun d => ¬ Ign F' d) := Finset.mem_filter.mpr ⟨hd, hdI⟩
              have := Finset.card_pos.mpr ⟨d, hm⟩
              omega
            exact pat_transfer N F F' G D hF hD (by omega) hI hGD GP1 GP3 hp

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ev (gs : List Gate) (out : ℕ) (w : List Bool) : Bool := (gs.foldl stepF w).getD out false

def inp (N : ℕ) (x : V) : List Bool := (List.range N).map x

lemma inp_getD (N : ℕ) (x : V) (i : ℕ) :
    (inp N x).getD i false = if i < N then x i else false := by
  unfold inp
  by_cases h : i < N
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [h]

lemma inp_succ (N : ℕ) (x : V) (v : Bool) :
    inp (N + 1) (Function.update x N v) = inp N x ++ [v] := by
  unfold inp
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have : i ≠ N := by
      have := List.mem_range.mp hi
      omega
    exact Function.update_of_ne this _ _
  · simp

def FN (gs : List Gate) (out N : ℕ) : V → Bool := fun x => ev gs out (inp N x)

def gv (g : Gate) (N : ℕ) : V → Bool := fun x =>
  g.op.eval (g.inputs.map fun i => if i < N then x i else false)

lemma FN_cons (g : Gate) (gs : List Gate) (out N : ℕ) (x : V) :
    FN (g :: gs) out N x = FN gs out (N + 1) (Function.update x N (gv g N x)) := by
  have h : stepF (inp N x) g = inp N x ++ [gv g N x] := by
    simp only [stepF, gv, inp_getD]
  simp only [FN, ev, List.foldl_cons, inp_succ, h]

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def bc : List Gate → ℕ
  | [] => 0
  | g :: gs => bc gs + (if isNot g.op then 0 else 1)

lemma gok_const (N cg : ℕ) (G : V → Bool) (v : Bool) (h : ∀ x, G x = v) : GateOK N cg G := by
  refine ⟨∅, by simp, by simp, ?_, ?_, ?_⟩
  · intro x y _; rw [h, h]
  · intro p b c _ h1; exact absurd (by rw [h, h]) h1
  · intro c p y _ h1; exact absurd (by rw [h, h]) h1

lemma gok_lit (N cg : ℕ) (G : V → Bool) (i : ℕ) (s : Bool) (hi : i < N)
    (h : ∀ x, G x = xor (x i) s) : GateOK N cg G := by
  refine ⟨{i}, by simpa using hi, by simp, ?_, ?_, ?_⟩
  · intro x y hxy; rw [h, h, hxy i (by simp)]
  · intro p b c hbc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind
  · intro c p y hyc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind

lemma gok_and (N cg : ℕ) (G : V → Bool) (i j : ℕ) (hi : i < N) (hj : j < N) (hcg : 1 ≤ cg)
    (h : ∀ x, G x = (x i && x j)) : GateOK N cg G := by
  refine ⟨{i, j}, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> assumption
  · have := Finset.card_le_two (a := i) (b := j)
    omega
  · intro x y hxy; rw [h, h, hxy i (by simp), hxy j (by simp)]
  · intro p b c hbc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind
  · intro c p y hyc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind

lemma gok_or (N cg : ℕ) (G : V → Bool) (i j : ℕ) (hi : i < N) (hj : j < N) (hcg : 1 ≤ cg)
    (h : ∀ x, G x = (x i || x j)) : GateOK N cg G := by
  refine ⟨{i, j}, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> assumption
  · have := Finset.card_le_two (a := i) (b := j)
    omega
  · intro x y hxy; rw [h, h, hxy i (by simp), hxy j (by simp)]
  · intro p b c hbc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind
  · intro c p y hyc h1 h2
    simp only [h, fl_apply] at h1 h2 ⊢
    grind

lemma gate_ok (g : Gate) (N : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) :
    GateOK N (if isNot g.op then 0 else 1) (gv g N) := by
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with h | h | h
    · exact gok_const N _ _ true (fun x => by simp [gv, hin, h, GateOp.eval])
    · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval])
    · exact gok_const N _ _ true (fun x => by simp [gv, hin, h, GateOp.eval])
  · by_cases hi : i < N
    · rcases hop with h | h | h
      · exact gok_lit N _ _ i false hi (fun x => by simp [gv, hin, h, GateOp.eval, hi])
      · exact gok_lit N _ _ i false hi (fun x => by simp [gv, hin, h, GateOp.eval, hi])
      · exact gok_lit N _ _ i true hi (fun x => by simp [gv, hin, h, GateOp.eval, hi])
    · rcases hop with h | h | h
      · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval, hi])
      · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval, hi])
      · exact gok_const N _ _ true (fun x => by simp [gv, hin, h, GateOp.eval, hi])
  · rcases hop with h | h | h
    · by_cases hi : i < N
      · by_cases hj : j < N
        · exact gok_and N _ _ i j hi hj (by simp [h, isNot])
            (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
        · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
      · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval, hi])
    · by_cases hi : i < N
      · by_cases hj : j < N
        · exact gok_or N _ _ i j hi hj (by simp [h, isNot])
            (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
        · exact gok_lit N _ _ i false hi (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
      · by_cases hj : j < N
        · exact gok_lit N _ _ j false hj (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
        · exact gok_const N _ _ false (fun x => by simp [gv, hin, h, GateOp.eval, hi, hj])
    · by_cases hi : i < N
      · exact gok_lit N _ _ i true hi (fun x => by simp [gv, hin, h, GateOp.eval, hi])
      · exact gok_const N _ _ true (fun x => by simp [gv, hin, h, GateOp.eval, hi])
  · exact absurd hlen (by rw [hin]; simp only [List.length_cons]; omega)

lemma base (out N : ℕ) : Inv N (FN [] out N) 0 := by
  have hF : ∀ x, FN [] out N x = if out < N then x out else false := by
    intro x
    simp only [FN, ev, List.foldl_nil, inp_getD]
  have nb : ∀ c, ¬ Binate (FN [] out N) c := by
    rintro c ⟨β, τ, ⟨y1, h1, h2, h3⟩, ⟨y2, k1, k2, k3⟩⟩
    rw [hF] at h2 h3 k2 k3
    simp only [fl_apply] at h3 k3
    grind
  refine ⟨⟨{out}, ?_, by simp⟩, Or.inr nb, Or.inr (fun hp => ?_)⟩
  · intro i hi x v
    rw [hF, hF]
    have : i ≠ out := by simpa using hi
    rw [Function.update_of_ne (Ne.symm this)]
  · obtain ⟨b, c, _, hb, _⟩ := pat_binate hp
    exact nb b hb

lemma main_inv (out : ℕ) : ∀ (gs : List Gate) (N : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    Inv N (FN gs out N) (bc gs) := by
  intro gs
  induction gs with
  | nil => intro N _; exact base out N
  | cons g gs ih =>
    intro N hg
    have IH := ih (N + 1) (fun g' hg' => hg g' (by simp [hg']))
    have hgo := hg g (by simp)
    change Inv N (FN (g :: gs) out N) (bc gs + (if isNot g.op then 0 else 1))
    exact step N (if isNot g.op then 0 else 1) (bc gs) _ _ (gv g N)
      (fun x => FN_cons g gs out N x) (gate_ok g N hgo.1 hgo.2) (by split_ifs <;> omega) IH

def Mono (F : V → Bool) : Prop :=
  ∀ x y : V, (∀ k, x k = true → y k = true) → F x = true → F y = true

lemma gv_mono (g : Gate) (N : ℕ) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Mono (gv g N) := by
  intro x y hxy
  unfold gv
  rcases h with h | h
  · rw [h]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id_eq]
    intro hx i hi
    have := hx i hi
    by_cases hiN : i < N
    · simp only [hiN, if_true] at this ⊢
      exact hxy i this
    · simp [hiN] at this
  · rw [h]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
    rintro ⟨i, hi, hv⟩
    refine ⟨i, hi, ?_⟩
    by_cases hiN : i < N
    · simp only [hiN, if_true] at hv ⊢
      exact hxy i hv
    · simp [hiN] at hv

lemma mono_all (out : ℕ) : ∀ (gs : List Gate) (N : ℕ),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Mono (FN gs out N) := by
  intro gs
  induction gs with
  | nil =>
    intro N _ x y hxy
    simp only [FN, ev, List.foldl_nil, inp_getD]
    by_cases h : out < N
    · simp only [h, if_true]
      exact hxy out
    · simp [h]
  | cons g gs ih =>
    intro N hg x y hxy hx
    rw [FN_cons] at hx ⊢
    refine ih (N + 1) (fun g' hg' => hg g' (by simp [hg'])) _ _ ?_ hx
    intro k hk
    by_cases hkN : k = N
    · rw [hkN] at hk ⊢
      rw [Function.update_self] at hk ⊢
      exact gv_mono g N (hg g (by simp)) x y hxy hk
    · rw [Function.update_of_ne hkN] at hk ⊢
      exact hxy k hk

lemma filt (gs : List Gate) :
    gs.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _)) =
      gs.filter (fun g => isNot g.op) := by
  apply List.filter_congr
  intro g _
  cases h : g.op <;> simp [isNot]

lemma bc_count (gs : List Gate) :
    bc gs + (gs.filter (fun g => isNot g.op)).length = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : isNot g.op <;> simp [bc, List.filter_cons, h] <;> omega

def ext {n : ℕ} (x : Fin n → Bool) : V := fun k => if h : k < n then x ⟨k, h⟩ else false

lemma ofFn_ext {n : ℕ} (x : Fin n → Bool) : List.ofFn x = inp n (ext x) := by
  apply List.ext_getElem
  · simp [inp]
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp [inp, ext, hi]

lemma ext_update {n : ℕ} (x : Fin n → Bool) (j : Fin n) (v : Bool) :
    ext (Function.update x j v) = Function.update (ext x) j.val v := by
  funext k
  by_cases hkj : k = j.val
  · subst hkj
    simp [ext]
  · rw [Function.update_of_ne hkj]
    unfold ext
    by_cases hk : k < n
    · have : (⟨k, hk⟩ : Fin n) ≠ j := fun h => hkj (by rw [← h])
      simp [hk, Function.update_of_ne this]
    · simp [hk]

lemma pat_of_hyp (n : ℕ) (F : V → Bool) (a b c : Fin n) (x : Fin n → Bool) (t : Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : F (ext (Function.update (Function.update (Function.update x a true) b false) c false))
      = t)
    (h2 : F (ext (Function.update (Function.update (Function.update x a false) b true) c true))
      = t)
    (h3 : F (ext (Function.update (Function.update (Function.update x a false) b true) c false))
      = !t)
    (h4 : F (ext (Function.update (Function.update (Function.update x a false) b false) c true))
      = !t)
    (h5 : F (ext (Function.update (Function.update (Function.update x a true) b true) c false))
      = !t)
    (hy : ∃ y : Fin n → Bool, F (ext (Function.update y c false)) = t ∧
      F (ext (Function.update y c true)) = !t) :
    Pat n F ∧ ¬ Mono F := by
  simp only [ext_update] at h1 h2 h3 h4 h5 hy
  have hAB : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hAC : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hBC : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  refine ⟨?_, ?_⟩
  · obtain ⟨y0, hy0a, hy0b⟩ := hy
    refine ⟨a.val, b.val, c.val,
      Function.update (Function.update (Function.update (ext x) a.val false) b.val true) c.val true,
      true, t, a.isLt, b.isLt, c.isLt, hAB, hAC, hBC, h2, ?_, ?_, ?_, ?_, ?_⟩
    · exact (congrArg F (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h4
    · exact (congrArg F (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h3
    · exact (congrArg F (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h5
    · exact (congrArg F (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans h1
    · refine ⟨Function.update (ext y0) c.val true, by simp, hy0b, ?_⟩
      rw [Bool.not_not]
      exact (congrArg F (by funext k; simp only [fl_apply, Function.update_apply]; grind)).trans hy0a
  · intro m
    cases t
    · have := m _
        (Function.update (Function.update (Function.update (ext x) a.val false) b.val true) c.val true)
        (by intro k; simp only [Function.update_apply]; grind) h4
      rw [h2] at this
      exact absurd this (by decide)
    · have := m _
        (Function.update (Function.update (Function.update (ext x) a.val true) b.val true) c.val false)
        (by intro k; simp only [Function.update_apply]; grind) h1
      rw [h5] at this
      exact absurd this (by decide)

theorem main (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (f : (Fin n → Bool) → Bool) (hf : ∀ z, f z = C.eval (List.ofFn z))
    (a b c : Fin n) (x : Fin n → Bool) (t : Bool) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : f (Function.update (Function.update (Function.update x a true) b false) c false) = t)
    (h2 : f (Function.update (Function.update (Function.update x a false) b true) c true) = t)
    (h3 : f (Function.update (Function.update (Function.update x a false) b true) c false) = !t)
    (h4 : f (Function.update (Function.update (Function.update x a false) b false) c true) = !t)
    (h5 : f (Function.update (Function.update (Function.update x a true) b true) c false) = !t)
    (hy : ∃ y : Fin n → Bool, f (Function.update y c false) = t ∧
      f (Function.update y c true) = !t)
    (S : Finset (Fin n))
    (hS : ∀ j ∈ S, ∃ z : Fin n → Bool,
      f (Function.update z j false) ≠ f (Function.update z j true)) :
    1 ≤ (C.gates.filter (fun g =>
        @decide (g.op = GateOp.not) (Classical.propDecidable _))).length ∧
      S.card + 1 ≤ C.size - (C.gates.filter (fun g =>
        @decide (g.op = GateOp.not) (Classical.propDecidable _))).length := by
  rw [filt]
  have hfF : ∀ z, f z = FN C.gates C.output n (ext z) := by
    intro z
    rw [hf, ofFn_ext]
    rfl
  have hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (hC g hg).1, (hC g hg).2⟩
  rw [hfF] at h1 h2 h3 h4 h5
  have hy' : ∃ y : Fin n → Bool, FN C.gates C.output n (ext (Function.update y c false)) = t ∧
      FN C.gates C.output n (ext (Function.update y c true)) = !t := by
    obtain ⟨y, e1, e2⟩ := hy
    exact ⟨y, by rw [← hfF]; exact e1, by rw [← hfF]; exact e2⟩
  obtain ⟨hPat, hNM⟩ := pat_of_hyp n _ a b c x t hab hac hbc h1 h2 h3 h4 h5 hy'
  obtain ⟨_, _, I2⟩ := main_inv C.output C.gates n hfan
  have hcount := bc_count C.gates
  refine ⟨?_, ?_⟩
  · by_contra hlt
    apply hNM
    apply mono_all
    intro g hg
    have hz : (C.gates.filter (fun g => isNot g.op)) = [] :=
      List.length_eq_zero_iff.mp (by omega)
    have hnn := (List.filter_eq_nil_iff.mp hz) g hg
    rcases (hfan g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hnn
      exact absurd rfl hnn
  · rcases I2 with ⟨T, hT, hc⟩ | h
    · have hle : S.card ≤ T.card := by
        apply Finset.card_le_card_of_injOn (fun j => j.val)
        · intro j hj
          by_contra hjT
          have hI : Ign (FN C.gates C.output n) j.val := hT j.val hjT
          obtain ⟨z, hz⟩ := hS j hj
          rw [hfF, hfF, ext_update, ext_update, hI _ _, hI _ _] at hz
          exact hz rfl
        · intro j1 _ j2 _ h
          exact Fin.ext h
      unfold Circuit.size
      omega
    · exact absurd hPat h

end PEqualNP.Outside.L_lib_572_aux

theorem PEqualNP.Outside.L_lib_572 : (∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let W := Fin n → Bool
  let f := fun (x : W) => C.eval (List.ofFn x)
  let essential := (Finset.univ : Finset (Fin n)).filter (fun j =>
    ∃ x : W, f (Function.update x j false) ≠ f (Function.update x j true))
  ∀ (a b c : Fin n) (x : W) (t : Bool), a ≠ b → a ≠ c → b ≠ c →
    let atBits := fun (u v w : Bool) =>
      f (Function.update (Function.update (Function.update x a u) b v) c w)
    atBits true false false = t → atBits false true true = t →
    atBits false true false = !t → atBits false false true = !t →
    atBits true true false = !t →
    (∃ y : W, f (Function.update y c false) = t ∧ f (Function.update y c true) = !t) →
    let inv := (C.gates.filter (fun g =>
      @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
    1 ≤ inv ∧ essential.card + 1 ≤ C.size - inv) := by
  intro n C hC W f essential a b c x t hab hac hbc atBits h1 h2 h3 h4 h5 hy inv
  exact PEqualNP.Outside.L_lib_572_aux.main n C hC f (fun _ => rfl) a b c x t hab hac hbc
    h1 h2 h3 h4 h5 hy essential (fun j hj => (Finset.mem_filter.mp hj).2)
