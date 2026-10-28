module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.Coordinates
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Natural.FieldModel

/-!
# The natural L2(4) action on the native inner quintet translations

The actual subgroup fixing the distinguished source tetrad pointwise has the
literal inner translations as its linear-action kernel. Its quotient is
identified with SL2(4) through the two systematic F4 coordinates of the
coordinate-zero hexacode. Under the resulting binary linear equivalence,
native conjugation is exactly matrix multiplication on the natural F4 plane.
The displayed action formula uses the literal quotient map of this geometric
preimage. It does not identify the entire quintet quotient with SL2(4).

The imported coordinate calculation proves irreducibility for the full native
Q action, unconditionally. Intrinsic-core identification and its transport to
`innerConjugation innerInputs` belong to the group-structure assembly.

Source: Aschbacher--Smith H.14.3(2), printed p.397, with the marking on p.396.
The licensed hexacode ingredients and their attribution are recorded in the
imported `Coordinates` and `FieldModel` modules.
-/

@[expose] public section

noncomputable section
open MathieuCode.M22Quintet
open Representation
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22ChapterH.Quintet

/-- The actual geometric quotient, identified by its natural SL2(4) matrices. -/
def naturalActorModelEquiv :
    (naturalActor ⧸ naturalActorTranslations) ≃* SL2FourNatural.SL :=
  naturalActorQuotientEquiv.trans Hexacode.ZeroNatural.modelEquiv

/-- Native translations in the two genuine F4 coordinates. -/
def innerTranslationNaturalEquiv : Additive innerTranslationGroup ≃ₗ[ZMod 2]
    SL2FourNatural.V :=
  innerTranslationCoordinates.trans Hexacode.ZeroNatural.vectorCoordinates

/-- The native conjugation action is the natural action, with the literal quotient map. -/
theorem innerTranslation_natural (a : naturalActor) (v : Additive innerTranslationGroup) :
    innerTranslationNaturalEquiv (innerTranslationConjugation a.val v) =
      SL2FourNatural.action (naturalActorModelEquiv (QuotientGroup.mk a))
        (innerTranslationNaturalEquiv v) := by
  change Hexacode.ZeroNatural.vectorCoordinates
    (innerTranslationCoordinates (innerTranslationConjugation a.val v)) =
      SL2FourNatural.action
        (Hexacode.ZeroNatural.modelEquiv (naturalActorQuotientEquiv (QuotientGroup.mk a)))
        (Hexacode.ZeroNatural.vectorCoordinates (innerTranslationCoordinates v))
  rw [innerTranslationCoordinates_actor, naturalActorQuotientEquiv_mk]
  exact (Hexacode.ZeroNatural.matrixAction_equivariant
    (naturalActorProjection a) (innerTranslationCoordinates v)).symm

/-- The same actor quotient over the canonical field of four elements. -/
def naturalActorStandardEquiv :
    (naturalActor ⧸ naturalActorTranslations) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  naturalActorModelEquiv.trans SL2FourNatural.standardGroupEquiv

/-- The actual binary linear marking over the canonical field. -/
def innerTranslationStandardEquiv : Additive innerTranslationGroup ≃ₗ[ZMod 2]
    (Fin 2 → GaloisField 2 2) :=
  innerTranslationNaturalEquiv.trans SL2FourNatural.standardVectorEquiv

theorem innerTranslation_standard_natural (a : naturalActor)
    (v : Additive innerTranslationGroup) :
    innerTranslationStandardEquiv (innerTranslationConjugation a.val v) =
      specialLinearNatural 2 (naturalActorStandardEquiv (QuotientGroup.mk a))
        (innerTranslationStandardEquiv v) := by
  change SL2FourNatural.standardVectorEquiv
    (innerTranslationNaturalEquiv (innerTranslationConjugation a.val v)) = _
  rw [innerTranslation_natural, SL2FourNatural.standard_equivariant]
  rfl

/-- The geometric preimage lies in native M22, as it fixes the deleted points. -/
theorem naturalActor_inner (a : naturalActor) : a.val.val ∈ L := by
  apply (MathieuCode.m22ToPairStabilizer_mem_range_iff_fixed_zero _).mpr
  have h := (mem_naturalActor_iff a.val).mp a.property 0
  rw [naturalPointCoordinates_zero] at h
  change a.val.val.val.val (0 : Fin 24) = 0
  exact h

/-- The displayed quotient is precisely the faithful quotient of the native conjugation action. -/
theorem innerTranslation_actor_kernel :
    (innerTranslationConjugation.comp naturalActor.subtype).ker = naturalActorTranslations := by
  ext a
  change innerTranslationConjugation a.val = 1 ↔ a ∈ naturalActorTranslations
  rw [← QuotientGroup.eq_one_iff (N := naturalActorTranslations) a]
  constructor
  · intro h
    apply naturalActorModelEquiv.injective
    rw [naturalActorModelEquiv.map_one]
    apply SL2FourNatural.action_faithful
    rw [SL2FourNatural.action.map_one]
    apply LinearEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := innerTranslationNaturalEquiv.surjective w
    rw [← innerTranslation_natural, h]
    rfl
  · intro h
    apply LinearMap.ext
    intro v
    apply innerTranslationNaturalEquiv.injective
    rw [innerTranslation_natural, h, naturalActorModelEquiv.map_one, SL2FourNatural.action.map_one]
    rfl

end Sporadic.Mathieu.M22ChapterH.Quintet
