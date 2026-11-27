import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25576 : (let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
[output 596, output (596 ^^^ 12), output 6040, output (6040 ^^^ 12),
  output 565, output (565 ^^^ 12)] = [18, 0, 0, 45, 45, 18] ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    (w = 596 ∨ w = 6040 ∨ w = 565) ∧
    label (output w.toNat) = label (output (w ^^^ 12).toNat)) := by
  refine ⟨by decide +kernel, ?_⟩
  intro label
  by_cases h1 : label 18 = label 0
  · refine ⟨(596 : BitVec 17), Or.inl rfl, ?_⟩
    convert h1 using 2 <;> decide +kernel
  · by_cases h2 : label 0 = label 45
    · refine ⟨(6040 : BitVec 17), Or.inr (Or.inl rfl), ?_⟩
      convert h2 using 2 <;> decide +kernel
    · refine ⟨(565 : BitVec 17), Or.inr (Or.inr rfl), ?_⟩
      have h3 : label 45 = label 18 := by
        revert h1 h2
        cases label 18 <;> cases label 0 <;> cases label 45 <;> simp
      convert h3 using 2 <;> decide +kernel
