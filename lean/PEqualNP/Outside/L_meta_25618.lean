import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25618_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 22]⟩], 25⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 16 := by decide +kernel

lemma h_rep : Represents (fun (u v : Fin 5) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 5)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_25618_aux

theorem PEqualNP.Outside.L_meta_25618 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 16 ∧
  PEqualNP.Represents.Represents (fun (u v : Fin 5) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % 5)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_25618_aux.circ, PEqualNP.Outside.L_meta_25618_aux.h_ok, PEqualNP.Outside.L_meta_25618_aux.h_sz, PEqualNP.Outside.L_meta_25618_aux.h_rep⟩
