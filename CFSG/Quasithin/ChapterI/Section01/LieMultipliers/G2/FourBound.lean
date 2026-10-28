module

public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.G2
public import Theory.SpecificGroups.G2.MultiplierFourBound.Complete
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# The field-four multiplier bound for the actual source quotient

The intrinsic G₂(4) multiplier calculation bounds the center of every finite
quasisimple group whose literal central quotient is the octonion model.
For the existing source covering, a nontrivial center then identifies that
center with C₂ and makes the covering universal. The former independent
upper-bound premise is completely discharged.

Source: Aschbacher–Smith I.1.3(1) and I.2.2(5), printed pp.407–411
(PDF pp.418–422); the same bound is used for the quasisimple overcomponent
in the source argument of 9.4.1.
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.G2

open Theory.GroupTheory PerfectCentralCovering Atlas.G2.FiniteCover

/-- The center bound uses the actual source quotient map, in any universe. -/
public theorem fourSourceCenter_card_le_two
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ Subgroup.center L ≃* FourBase) :
    Nat.card (Subgroup.center L) ≤ 2 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hk : f.ker = Subgroup.center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let c : Cover L FourBase := {
    toMonoidHom := f
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := hk.le }
  simpa only [show c.toMonoidHom.ker = Subgroup.center L from hk] using
    MultiplierFourBound.cover_kernel_card_le_two c

/-- A source marking over any four-element coefficient field gives the same
center bound through the coefficientwise octonion group isomorphism. -/
public theorem fourSourceCenter_card_le_two_of_field
    {L F : Type*} [Group L] [Finite L] [IsQuasisimple L] [Field F] [Finite F]
    (e : L ⧸ Subgroup.center L ≃* Atlas.G2.Model F) (hF : Nat.card F = 4) :
    Nat.card (Subgroup.center L) ≤ 2 := by
  let a : F ≃+* FourField := by
    let := Fintype.ofFinite F
    let := Fintype.ofFinite FourField
    apply FiniteField.ringEquivOfCardEq
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 2 (by decide)]
    decide
  exact fourSourceCenter_card_le_two (e.trans (Atlas.G2.fieldEquiv a))

universe w

/-- The source's nontrivial cover is universal with center C₂, with its
multiplier bound supplied by the intrinsic calculation. -/
public theorem fourSourceCover_universal
    {L : Type} [Group L] [Finite L] [IsQuasisimple L]
    (e : L ⧸ Subgroup.center L ≃* FourBase) (hZ : Subgroup.center L ≠ ⊥) :
    Covering.IsUniversal.{0, 0, w} (fourSourceCover e) ∧
      Nonempty (Subgroup.center L ≃* Multiplicative (ZMod 2)) :=
  fourSourceCover_universal_of_bound e hZ MultiplierFourBound.card_kernel_le_two

end CFSG.Quasithin.ChapterI.LieMultipliers.G2
