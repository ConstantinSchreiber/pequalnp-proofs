import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_550_aux

variable {K : Type} [Field K] {q : ℕ} {V : Type} [AddCommGroup V] [Module K V]
  {W : Type} [AddCommGroup W] [Module K W]

def foldL (A : Fin q → V →ₗ[K] V) : List (Fin q) → V →ₗ[K] V
  | [] => LinearMap.id
  | a :: u => foldL A u ∘ₗ A a

theorem foldL_apply (A : Fin q → V →ₗ[K] V) (u : List (Fin q)) (x : V) :
    foldL A u x = u.foldl (fun y a => A a y) x := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => simp [foldL, ih]

theorem foldL_append (A : Fin q → V →ₗ[K] V) (u v : List (Fin q)) (x : V) :
    foldL A (u ++ v) x = foldL A v (foldL A u x) := by
  simp [foldL_apply, List.foldl_append]

noncomputable def P (A : Fin q → V →ₗ[K] V) (s : V) : (List (Fin q) →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K (fun w => foldL A w s)

theorem P_single (A : Fin q → V →ₗ[K] V) (s : V) (w : List (Fin q)) (k : K) :
    P A s (Finsupp.single w k) = k • foldL A w s := by
  simp [P]

theorem P_shift (A : Fin q → V →ₗ[K] V) (s : V) (u : List (Fin q)) (c : List (Fin q) →₀ K) :
    P A s (Finsupp.mapDomain (fun w => w ++ u) c) = foldL A u (P A s c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp [Finsupp.mapDomain_add, h₁, h₂]
  | single w k => simp [Finsupp.mapDomain_single, P_single, foldL_append]

theorem out_eq (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W) (s : V) (t : W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K)
    (hfg : ∀ w, f (foldL A w s) = g (foldL B w t)) (c : List (Fin q) →₀ K) :
    f (P A s c) = g (P B t c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp [h₁, h₂]
  | single w k => simp [P_single, hfg]

theorem ker_le (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W) (s : V) (t : W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K)
    (hB : ∀ y : W, (∀ w, g (foldL B w y) = 0) → y = 0)
    (hfg : ∀ w, f (foldL A w s) = g (foldL B w t)) (c : List (Fin q) →₀ K)
    (hc : P A s c = 0) : P B t c = 0 := by
  apply hB
  intro w
  rw [← P_shift, ← out_eq A B s t f g hfg, P_shift, hc, map_zero, map_zero]

theorem main (s : V) (t : W) (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K)
    (hX : Submodule.span K (Set.range fun w : List (Fin q) => w.foldl (fun x a => A a x) s) = ⊤)
    (hY : Submodule.span K (Set.range fun w : List (Fin q) => w.foldl (fun y a => B a y) t) = ⊤)
    (hA : ∀ x : V, (∀ w : List (Fin q), f (w.foldl (fun y a => A a y) x) = 0) → x = 0)
    (hB : ∀ y : W, (∀ w : List (Fin q), g (w.foldl (fun x a => B a x) y) = 0) → y = 0)
    (hfg : ∀ w : List (Fin q),
      f (w.foldl (fun x a => A a x) s) = g (w.foldl (fun y a => B a y) t)) :
    ∃! H : V ≃ₗ[K] W, H s = t ∧ (∀ x, g (H x) = f x) ∧
      ∀ (a : Fin q) (x : V), H (A a x) = B a (H x) := by
  have hX' : Submodule.span K (Set.range fun w : List (Fin q) => foldL A w s) = ⊤ := by
    simpa only [foldL_apply] using hX
  have hY' : Submodule.span K (Set.range fun w : List (Fin q) => foldL B w t) = ⊤ := by
    simpa only [foldL_apply] using hY
  have hA' : ∀ x : V, (∀ w, f (foldL A w x) = 0) → x = 0 := by
    simpa only [foldL_apply] using hA
  have hB' : ∀ y : W, (∀ w, g (foldL B w y) = 0) → y = 0 := by
    simpa only [foldL_apply] using hB
  have hfg' : ∀ w, f (foldL A w s) = g (foldL B w t) := by
    simpa only [foldL_apply] using hfg
  have hPs : LinearMap.range (P A s) = ⊤ := by
    rw [P, Finsupp.range_linearCombination]; exact hX'
  have hQs : LinearMap.range (P B t) = ⊤ := by
    rw [P, Finsupp.range_linearCombination]; exact hY'
  obtain ⟨R, hR⟩ := (P A s).exists_rightInverse_of_surjective hPs
  obtain ⟨R', hR'⟩ := (P B t).exists_rightInverse_of_surjective hQs
  have hRa : ∀ x, P A s (R x) = x := fun x => by
    have := congrArg (fun φ => φ x) hR; simpa using this
  have hRb : ∀ y, P B t (R' y) = y := fun y => by
    have := congrArg (fun φ => φ y) hR'; simpa using this
  have k1 := ker_le A B s t f g hB' hfg'
  have k2 := ker_le B A t s g f hA' (fun w => (hfg' w).symm)
  have hH : ∀ c, P B t (R (P A s c)) = P B t c := by
    intro c
    have h0 : P A s (R (P A s c) - c) = 0 := by rw [map_sub, hRa, sub_self]
    have h1 := k1 _ h0
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have hG : ∀ c, P A s (R' (P B t c)) = P A s c := by
    intro c
    have h0 : P B t (R' (P B t c) - c) = 0 := by rw [map_sub, hRb, sub_self]
    have h1 := k2 _ h0
    rw [map_sub, sub_eq_zero] at h1
    exact h1
  have surjP : ∀ x, ∃ c, P A s c = x := fun x => ⟨R x, hRa x⟩
  have surjQ : ∀ y, ∃ c, P B t c = y := fun y => ⟨R' y, hRb y⟩
  let H : V ≃ₗ[K] W := LinearEquiv.ofLinearMap ((P B t) ∘ₗ R) ((P A s) ∘ₗ R')
    (by
      apply LinearMap.ext
      intro y
      obtain ⟨c, rfl⟩ := surjQ y
      simp [hG, hH])
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨c, rfl⟩ := surjP x
      simp [hG, hH])
  have HP : ∀ c, H (P A s c) = P B t c := fun c => hH c
  refine ⟨H, ⟨?_, ?_, ?_⟩, ?_⟩
  · have := HP (Finsupp.single [] 1)
    simpa [P_single, foldL] using this
  · intro x
    obtain ⟨c, rfl⟩ := surjP x
    rw [HP, out_eq A B s t f g hfg']
  · intro a x
    obtain ⟨c, rfl⟩ := surjP x
    have e1 : A a (P A s c) = P A s (Finsupp.mapDomain (fun w => w ++ [a]) c) := by
      rw [P_shift]; rfl
    have e2 : B a (P B t c) = P B t (Finsupp.mapDomain (fun w => w ++ [a]) c) := by
      rw [P_shift]; rfl
    rw [e1, HP, HP, e2]
  · rintro H' ⟨h1, h2, h3⟩
    have key : ∀ (w : List (Fin q)) (x : V), H' (foldL A w x) = foldL B w (H' x) := by
      intro w
      induction w with
      | nil => intro x; rfl
      | cons a w ih => intro x; simp [foldL, ih, h3]
    have key2 : ∀ c, H' (P A s c) = P B t c := by
      intro c
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c₁ c₂ h₁ h₂ => simp [h₁, h₂]
      | single w k => simp [P_single, key, h1]
    apply LinearEquiv.ext
    intro x
    obtain ⟨c, rfl⟩ := surjP x
    rw [key2, HP]

end PEqualNP.Outside.L_lib_550_aux

theorem PEqualNP.Outside.L_lib_550 : (∀ (K : Type) [Field K] (q d e : ℕ),
  let V := Fin d → K
  let W := Fin e → K
  ∀ (s : V) (t : W) (A : Fin q → V →ₗ[K] V) (B : Fin q → W →ₗ[K] W)
    (f : V →ₗ[K] K) (g : W →ₗ[K] K),
    let X := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    let Y := fun (w : List (Fin q)) => w.foldl (fun y a => B a y) t
    Submodule.span K (Set.range X) = ⊤ →
    Submodule.span K (Set.range Y) = ⊤ →
    (∀ x : V, (∀ w : List (Fin q), f (w.foldl (fun y a => A a y) x) = 0) → x = 0) →
    (∀ y : W, (∀ w : List (Fin q), g (w.foldl (fun x a => B a x) y) = 0) → y = 0) →
    (∀ w, f (X w) = g (Y w)) →
    ∃! H : V ≃ₗ[K] W, H s = t ∧ (∀ x, g (H x) = f x) ∧
      ∀ (a : Fin q) (x : V), H (A a x) = B a (H x)) := by
  intro K _ q d e V W s t A B f g X Y hX hY hA hB hfg
  exact PEqualNP.Outside.L_lib_550_aux.main s t A B f g hX hY hA hB hfg
