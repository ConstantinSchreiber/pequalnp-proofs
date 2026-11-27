import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25549 : (let k : Nat := 17
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
output 128218 = 100 ∧ output 128222 = 100 ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    label (output w.toNat) = label (output (w ^^^ 4).toNat)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro label
  refine ⟨128218#17, ?_⟩
  congr 1
