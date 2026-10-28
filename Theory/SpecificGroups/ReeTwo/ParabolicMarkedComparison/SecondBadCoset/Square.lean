module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondBadCoset
/-!
# The square of the twisted reflected action

The native composite of the central twist and reflection squares to conjugation
by root seven. The packed certificate is transported to the actual automorphism,
retaining precisely the square needed by the no-involution equation.

Source: the binary Ree F.1.12 extension calculation used in J.4.5.
-/

public section
noncomputable section
namespace ReeTwo.SylowModel.CollectedBitVectors
open CubicAction

private def innerSevenPacked : PackedElement 2048 :=
  product (product (pack (generator 7)) coreEnumeration) (pack ((generator 7)⁻¹))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem bad_square_check :
    equal (badPacked (badPacked coreEnumeration)) innerSevenPacked=BitVec.allOnes 2048 := by
  decide +kernel

/-- The twisted reflection squares to the actual inner action of root seven. -/
theorem badActor_square : badActor^2=MulAut.conj (generator 7) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨k,rfl⟩:=coreEnumerationEquiv.surjective a
  have h1:=read_badPacked coreEnumeration k (coreEnumerationEquiv k) (read_coreEnumeration k)
  have h2:=read_badPacked (badPacked coreEnumeration) k (badActor (coreEnumerationEquiv k)) h1
  have hm:(equal (badPacked (badPacked coreEnumeration)) innerSevenPacked).getLsbD k.val=true := by
    rw [bad_square_check]
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true k.isLt
  rw [equal_spec,h2] at hm
  simp only [innerSevenPacked,read_product,read_pack,read_coreEnumeration] at hm
  apply A.subtype_injective
  exact hm

end ReeTwo.SylowModel.CollectedBitVectors
