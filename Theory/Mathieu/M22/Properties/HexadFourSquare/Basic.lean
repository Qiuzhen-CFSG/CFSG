module

public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# The native commuting-square witness for a hexad complement

This specifies a concrete square-root identity in the literal degree-22 M₂₂,
independent of any central cover. It is preserved by changing the A₆ actor
coordinates. CentralExtensionCommutingPair turns the identity into commuting
lifts in every central extension. No existence assertion is made here.

The consumer is the quartic splitting reduction for Aschbacher–Smith I.2.2(6),
printed p.412. Native witness construction remains a separate obligation.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22HexadFourSquare
open scoped Pointwise

/-- Two independent involutions in the specified native actor, with a square
root of the first commuting with the second in the ambient M₂₂. -/
def HasSquare {B : Finset (Fin 22)}
    (j : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B) : Prop :=
  ∃ a b : alternatingGroup (Fin 6), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 ∧
    ∃ r : M22, r ^ 2 = (j a : M22) ∧ Commute r (j b : M22)

/-- An explicit change of actor marking preserves the same native square root. -/
theorem HasSquare.comp_mulEquiv {B : Finset (Fin 22)}
    {j : alternatingGroup (Fin 6) →* MulAction.stabilizer M22 B}
    (h : HasSquare j) (alpha : alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6)) :
    HasSquare (j.comp alpha.toMonoidHom) := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, r, hr, hrb⟩ := h
  refine ⟨alpha.symm a, alpha.symm b, ?_, ?_, ?_, ?_, ?_, r, ?_, ?_⟩
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · simpa using ha1
  · simpa using hb1
  · intro hh
    apply hab
    exact alpha.symm.injective (by simpa only [map_mul, map_one] using hh)
  · simpa using hr
  · simpa using hrb

end Sporadic.Mathieu.M22HexadFourSquare
