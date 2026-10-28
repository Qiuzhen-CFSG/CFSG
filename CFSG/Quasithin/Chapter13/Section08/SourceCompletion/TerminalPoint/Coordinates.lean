module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceSix
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.LinearModels
/-!
# Whole-module coordinates at the original A₆ terminal point

The recognized natural component section and U_H=[U_H,K] produce a
perfect central cover of the natural A₆ module. The existing cover theorem
identifies that entire module with the natural module or the augmentation
core, and the faithful extension theorem identifies the full actor.
The second construction preserves a specified A₆ marking compatible with
the intrinsic K/O₂(K) quotient. Neither construction replaces the cover
by its four-dimensional quotient.

The component section and commutator generation are earlier source inputs
from 13.8.21 and 13.8.26--27, supplied by the six/G₂ assembly. These are
strictly earlier inputs than whole-module terminal coordinates.
Source: Aschbacher--Smith, printed pp.957,962--963,968--969.
-/
public section
open Subgroup Representation BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
open A6Endgame.PointNormalizer A6Endgame.IntersectionBalance
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
/-- The supplied quotient action has the literal source conjugation formula. -/
theorem starAction_isConjugation
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁) :
    IsConjugation H V₃ V₁ (tildeRepresentation H (Source.UH H V₃) V₁ a) := by
  intro h u
  exact congrArg Additive.ofMul (a.conjugation h u)

/-- Construct both whole-module coordinates from the recognized component
section. The original quotient and any central covering kernel are retained. -/
theorem coordinates_of_component_section
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal)
    (hkernel : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃,K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hs : HasSectionModel H V₃ V₁ (tildeRepresentation H (Source.UH H V₃) V₁ a)
      K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    (∃ e : Source.Hstar H ≃* A6, LinearCoordinates a (A6.subtype.comp e.toMonoidHom)) ∨
      (∃ e : Source.Hstar H ≃* S6, LinearCoordinates a e.toMonoidHom) := by
  obtain ⟨f,_,_,hm,hcoords⟩ := ComponentSieve.SixAndG2.SourceSix.full_action_of_section
    hKH hK hKn (tildeRepresentation H _ V₁ a) (starAction_isConjugation a)
    hkernel hgen eK hs
  rcases hm with ⟨e,he⟩ | ⟨e,he⟩
  · left
    refine ⟨e,?_⟩
    rcases hcoords with ⟨F,hF⟩ | ⟨F,hF⟩
    · exact Or.inl ⟨F,fun g v => by simpa only [MonoidHom.comp_apply,
        Subgroup.coe_subtype,MulEquiv.coe_toMonoidHom,he] using hF g v⟩
    · exact Or.inr ⟨F,fun g v => by simpa only [MonoidHom.comp_apply,
        Subgroup.coe_subtype,MulEquiv.coe_toMonoidHom,he] using hF g v⟩
  · right
    refine ⟨e,?_⟩
    rcases hcoords with ⟨F,hF⟩ | ⟨F,hF⟩
    · exact Or.inl ⟨F,fun g v => by simpa only [MulEquiv.coe_toMonoidHom,he] using hF g v⟩
    · exact Or.inr ⟨F,fun g v => by simpa only [MulEquiv.coe_toMonoidHom,he] using hF g v⟩

/-- With the intrinsic component marking compatible with the given A₆
actor, the cover construction preserves that same actor marking. -/
theorem alternating_coordinates_of_component_section
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃,K⁆)
    (e : Source.Hstar H ≃* A6) (eK : (K ⧸ pCore 2 K) ≃* A6)
    (hmark : ∀ k : K, e (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
      eK (QuotientGroup.mk' (pCore 2 K) k))
    (hs : HasSectionModel H V₃ V₁ (tildeRepresentation H (Source.UH H V₃) V₁ a)
      K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    LinearCoordinates a (A6.subtype.comp e.toMonoidHom) := by
  have hactor (g : Source.Hstar H) : modelActor hKH hK eK (e g) = g := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (eK.symm (e g))
    have he : eK (QuotientGroup.mk' (pCore 2 K) k) = e g := by rw [hk]; simp
    rw [← he,modelActor_mk]
    exact e.injective ((hmark k).trans he)
  rcases alternatingSix_module_of_section hKH hK (tildeRepresentation H _ V₁ a)
      (starAction_isConjugation a) hgen eK hs with ⟨F,hF⟩ | ⟨F,hF⟩
  · exact Or.inl ⟨F,fun g v => by simpa only [hactor, alternatingNaturalRepresentation, alternatingCoreRepresentation,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom] using hF (e g) v⟩
  · exact Or.inr ⟨F,fun g v => by simpa only [hactor, alternatingNaturalRepresentation, alternatingCoreRepresentation,
      MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom] using hF (e g) v⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
