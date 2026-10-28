module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Basic
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coverage.Finite
/-!
# Checked generator edges in the outer M₁₂ overlap

Short degree-24 permutation arrays are compared with the original attributed
ATLAS generators. Their action on the three separating points certifies every
edge of the 128-element word enumeration. This is the interpretation required
before the finite multiplication table can be used in the coverage proof.

Source context: Aschbacher--Smith F.1.12(I)(13), pp.262–263, and 14.2.21,
p.988. The literal overlap and the nonsplit first endpoint come from `Basic`.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Coverage
set_option maxRecDepth 100000
private def fastA : Equiv.Perm (Fin 24) where
  toFun := ![16, 13, 7, 3, 21, 10, 15, 23, 8, 9, 17, 6, 11, 14, 18, 12, 0, 20, 1, 19, 5, 4, 2, 22]
  invFun := ![16, 18, 22, 3, 21, 20, 11, 2, 8, 9, 5, 12, 15, 1, 13, 6, 0, 10, 14, 19, 17, 4, 23, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def fastB : Equiv.Perm (Fin 24) where
  toFun := ![9, 6, 10, 4, 3, 18, 1, 15, 21, 0, 2, 22, 14, 17, 12, 7, 19, 13, 5, 16, 23, 8, 11, 20]
  invFun := ![9, 6, 10, 4, 3, 18, 1, 15, 21, 0, 2, 22, 14, 17, 12, 7, 19, 13, 5, 16, 23, 8, 11, 20]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def fastC : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 23, 3, 4, 11, 12, 18, 19, 9, 10, 5, 6, 22, 14, 17, 21, 15, 7, 8, 20, 16, 13, 2]
  invFun := ![0, 1, 23, 3, 4, 11, 12, 18, 19, 9, 10, 5, 6, 22, 14, 17, 21, 15, 7, 8, 20, 16, 13, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def fastGenerator : Fin 3 → Equiv.Perm (Fin 24) := ![fastA, fastB, fastC]
private theorem fastGenerator_eq : fastGenerator = Overlap.generatorPerm := by
  funext j
  fin_cases j <;> decide +kernel
private theorem step_check : ∀ (i : Fin 128) (j : Fin 3),
    let p := FiniteWords.evaluate fastGenerator (Data.overlapWords i) * fastGenerator j
    Overlap.indexSignature (step i j) =
      ((p 0).val, (p 1).val, (p 2).val) := by decide +kernel

theorem element_step (i : Fin 128) (j : Fin 3) :
    Overlap.element (step i j) = Overlap.element i * Overlap.generator j := by
  apply Overlap.signature_injective
  rw [Overlap.signature_element]
  change _ = (((Overlap.element i).val.val ((Overlap.generator j).val.val 0)).val,
    ((Overlap.element i).val.val ((Overlap.generator j).val.val 1)).val,
    ((Overlap.element i).val.val ((Overlap.generator j).val.val 2)).val)
  rw [Overlap.element_val, Overlap.generator_val]
  simpa only [fastGenerator_eq, Equiv.Perm.mul_apply] using step_check i j

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions.Coverage
