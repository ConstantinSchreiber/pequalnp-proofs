import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_544_aux

variable {K : Type} [Field K] {q d : ℕ}

def run (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) (w : List (Fin q)) :
    Fin d → K :=
  w.foldl (fun x a => A a x) s

def Good (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
    (P : Finset (List (Fin q))) : Prop :=
  (∀ w ∈ P, w.length < P.card) ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
  LinearIndepOn K (run s A) (↑P : Set (List (Fin q)))

theorem good_insert (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K))
    (P : Finset (List (Fin q))) (hP : Good s A P) (x : List (Fin q)) (hx : x ∉ P)
    (hlen : x.length ≤ P.card) (hpre : ∀ w a, w ++ [a] = x → w ∈ P)
    (hspan : run s A x ∉ Submodule.span K (run s A '' (↑P : Set (List (Fin q))))) :
    Good s A (insert x P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [Finset.card_insert_of_notMem hx]
    rcases Finset.mem_insert.mp hw with rfl | hw
    · omega
    · have := hP.1 w hw; omega
  · intro w a hw
    rcases Finset.mem_insert.mp hw with h | hw
    · exact Finset.mem_insert_of_mem (hpre w a h)
    · exact Finset.mem_insert_of_mem (hP.2.1 w a hw)
  · rw [Finset.coe_insert]
    exact hP.2.2.insert hspan

theorem good_card {s : Fin d → K} {A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)}
    {P : Finset (List (Fin q))} (hP : Good s A P) : P.card ≤ d := by
  have h : LinearIndependent K (fun w : P => run s A w.val) := hP.2.2
  have := h.fintype_card_le_finrank
  simpa using this

theorem closed_of_max {s : Fin d → K} {A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)}
    {P : Finset (List (Fin q))} (hP : Good s A P)
    (hmax : ∀ P', Good s A P' → P'.card ≤ P.card) :
    ∀ w, run s A w ∈ Submodule.span K (run s A '' (↑P : Set (List (Fin q)))) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    by_contra h
    have hx : ([] : List (Fin q)) ∉ P := fun hmem => h (Submodule.subset_span ⟨[], hmem, rfl⟩)
    have := hmax _ (good_insert s A P hP [] hx (Nat.zero_le _) (by intro w a h; simp at h) h)
    rw [Finset.card_insert_of_notMem hx] at this
    omega
  | append_singleton w a ih =>
    have hrun : ∀ u, run s A (u ++ [a]) = A a (run s A u) := by
      intro u; simp [run, List.foldl_append]
    rw [hrun]
    have hle : Submodule.span K (run s A '' (↑P : Set (List (Fin q)))) ≤
        (Submodule.span K (run s A '' (↑P : Set (List (Fin q))))).comap (A a) := by
      rw [Submodule.span_le]
      rintro _ ⟨u, hu, rfl⟩
      change A a (run s A u) ∈ Submodule.span K (run s A '' (↑P : Set (List (Fin q))))
      rw [← hrun]
      by_contra h
      have hx : u ++ [a] ∉ P := fun hmem => h (Submodule.subset_span ⟨_, hmem, rfl⟩)
      have hl := hP.1 u hu
      have := hmax _ (good_insert s A P hP (u ++ [a]) hx (by simp; omega)
        (by
          intro w' a' h'
          obtain ⟨rfl, -⟩ := List.append_inj' h' rfl
          exact hu) h)
      rw [Finset.card_insert_of_notMem hx] at this
      omega
    exact hle ih

theorem main (s : Fin d → K) (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) :
    ∃ P : Finset (List (Fin q)), P.card ≤ d ∧
      (∀ w ∈ P, w.length < d) ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => run s A w.val) ∧
      ∀ w, run s A w ∈ Submodule.span K (run s A '' (↑P : Set (List (Fin q)))) := by
  have hex : ∃ P, Good s A P ∧ ∀ P', Good s A P' → P'.card ≤ P.card := by
    by_contra hno
    push Not at hno
    have key : ∀ n, ∃ P, Good s A P ∧ n ≤ P.card := by
      intro n
      induction n with
      | zero => exact ⟨∅, ⟨by simp, by simp, by simp⟩, Nat.zero_le _⟩
      | succ n ih =>
        obtain ⟨P, hP, hn⟩ := ih
        obtain ⟨P', hP', h⟩ := hno P hP
        exact ⟨P', hP', by omega⟩
    obtain ⟨P, hP, hn⟩ := key (d + 1)
    have := good_card hP
    omega
  obtain ⟨P, hP, hmax⟩ := hex
  exact ⟨P, good_card hP, fun w hw => lt_of_lt_of_le (hP.1 w hw) (good_card hP), hP.2.1,
    hP.2.2, closed_of_max hP hmax⟩

end PEqualNP.Outside.L_lib_544_aux

theorem PEqualNP.Outside.L_lib_544 : (∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∃ P : Finset (List (Fin q)), P.card ≤ d ∧
      (∀ w ∈ P, w.length < d) ∧ (∀ w a, w ++ [a] ∈ P → w ∈ P) ∧
      LinearIndependent K (fun w : P => run w.val) ∧
      ∀ w, run w ∈ Submodule.span K (run '' (↑P : Set (List (Fin q))))) := by
  intro K _ q d V s A run
  exact PEqualNP.Outside.L_lib_544_aux.main s A
