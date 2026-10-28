module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.MathieuRows.RowExclusions
public import Theory.Quasithin.EvenCharacteristic

/-!
# Excluding the whole Mathieu branch for maximal two-locals

A maximal two-local contained in a conjugate of max1 equals that conjugate,
since max1 is itself a two-local. Its intrinsic core quotient is therefore
M24. The original normal-residual quotient obstruction rules this out without
classifying smaller radicals. This is the shorter branch used by the original
binary doubled-module configuration, which already supplies local maximality.

Source: An--O'Brien--Wilson (2003), Section 4, p.122, and the maximal-two-local
form of the Kleidman--Wilson (1988), Section 2, reduction.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

/-- Every actual conjugate of max1 retains its concrete Mathieu core quotient. -/
def conjugateMathieuQuotientEquiv (g : Model) :
    let M := max1.map (MulAut.conj g).toMonoidHom
    M ⧸ pCore 2 M ≃* Sporadic.Mathieu.M24 :=
  (coreQuotientCongr ((MulAut.conj g).subgroupMap max1).symm).trans
    ((QuotientGroup.quotientMulEquivOfEq (localKernel_eq_twoCore _ _).symm).trans
      (localQuotientEquivM24 _ _))

/-- For a maximal two-local, the source quotient obstruction removes the
entire Mathieu placement branch, without classifying its smaller radicals. -/
theorem maximal_local_not_le_mathieu (M : Subgroup Model) (hM : IsMaximalTwoLocal M)
    (hq : ¬ (Nonempty ((M ⧸ pCore 2 M) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
         Nonempty ((M ⧸ pCore 2 M) ≃* Sporadic.Mathieu.M24) ∨
         Nonempty ((M ⧸ pCore 2 M) ≃* alternatingGroup (Fin 8)))) (g : Model) :
    ¬ M ≤ max1.map (MulAut.conj g).toMonoidHom := by
  intro hle
  have he : M = max1.map (MulAut.conj g).toMonoidHom :=
    le_antisymm hle (hM.2
      (Theory.Quasithin.isTwoLocal_map (MulAut.conj g) embedded_localKernel_isTwoLocal) hle)
  exact hq (Or.inr (Or.inl ⟨(coreQuotientCongr (MulEquiv.subgroupCongr he)).trans
    (conjugateMathieuQuotientEquiv g)⟩))

end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
