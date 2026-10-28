module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.Basic
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.MarkedModules
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.MarkedCores
public import Theory.GroupAction.NoncentralTwoChiefLength.CoreMaps
import Mathlib.Tactic

/-!
# Compatible section models for the final filtration comparison

The section data consist of actual surjective homomorphisms, their exact
kernels, and their equivariance formulas. The standard and opposite natural
actions retain the common cubic actor and the proved outer automorphism.
The two possibilities for a module are the literal four-dimensional natural
module and its five-dimensional augmentation cover; their contributions are
computed by the checked marked-module theorems.

`DualSectionModels` uses the exact denominator `C_UH(QH)` from 13.7.4(2).
Its two maps give compatible coordinates for that quotient and its
contragredient dual. `FiltrationModels.uh` separately describes `UH/V₁`;
these denominators are never equated. The parabolic maps are defined on the
whole common local overgroup, so the two-core quotient maps are subsequently
constructed using the two-group kernel theorem.

The source theorem's owner supplies these module and local quotient
identifications, abelianness of `UL`, and the earlier local containments.
This interface contains no chief-factor totals or inequalities.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.7.4, 13.8.27 and the last paragraph of 13.8.33, printed p.968.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
open Representation.BinaryFixedPoints
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels

/-- The two possible source modules; neither constructor specifies a numerical count. -/
inductive ModuleShape
  | natural
  | augmentation

namespace ModuleShape

abbrev Carrier : ModuleShape → Type
  | .natural => Natural
  | .augmentation => Augmentation

instance (s : ModuleShape) : AddCommGroup s.Carrier := by cases s <;> infer_instance
instance (s : ModuleShape) : Module (ZMod 2) s.Carrier := by cases s <;> infer_instance

noncomputable def standard : (s : ModuleShape) → Representation (ZMod 2) cubicActor s.Carrier
  | .natural => standardNatural
  | .augmentation => standardAugmentation

noncomputable def opposite : (s : ModuleShape) → Representation (ZMod 2) cubicActor s.Carrier
  | .natural => oppositeNatural
  | .augmentation => oppositeAugmentation

theorem standard_length (s : ModuleShape) :
    letI := action s.standard
    FixedPoints.cubicLength cubicActor (Multiplicative s.Carrier) = 2 := by
  cases s
  · exact standardNatural_cubicLength
  · exact standardAugmentation_cubicLength

theorem opposite_length (s : ModuleShape) :
    letI := action s.opposite
    FixedPoints.cubicLength cubicActor (Multiplicative s.Carrier) = 1 := by
  cases s
  · exact oppositeNatural_cubicLength
  · exact oppositeAugmentation_cubicLength

theorem standard_dual_length (s : ModuleShape) :
    letI := action s.standard.dual
    FixedPoints.cubicLength cubicActor (Multiplicative (Module.Dual (ZMod 2) s.Carrier)) = 2 := by
  cases s
  · exact standardNaturalDual_cubicLength
  · exact standardAugmentationDual_cubicLength
end ModuleShape
end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels
variable {G : Type*} [Group G] (A N R : Subgroup G) (f : A →* cubicActor)

/-- A quotient map to the natural L-side module, with the outer marking retained. -/
abbrev OppositeSection (s : ModuleShape) :=
  letI := action s.opposite
  ConjugationSection (Y := Multiplicative s.Carrier) A N R f

/-- A quotient map to the standard H-side natural module or its cover. -/
abbrev StandardSection (s : ModuleShape) :=
  letI := action s.standard
  ConjugationSection (Y := Multiplicative s.Carrier) A N R f

/-- The contragredient action on the dual of the very same specified module. -/
abbrev StandardDualSection (s : ModuleShape) :=
  letI := action s.standard.dual
  ConjugationSection (Y := Multiplicative (Module.Dual (ZMod 2) s.Carrier)) A N R f

open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The L-side two-core uses the duad actor, the outer image of the common actor. -/
abbrev DuadCoreSection :=
  letI := conjMulDistribMulActionOfLeNormalizer duadCubicActor (H1.pCoreIn 2)
    duadCubicActor_normalizes_parabolic_core
  ConjugationSection (Y := H1.pCoreIn 2) A N R (cubicActorEquiv.toMonoidHom.comp f)

/-- The H-side two-core uses the original syntheme marking. -/
abbrev SynthemeCoreSection :=
  letI := conjMulDistribMulActionOfLeNormalizer cubicActor (H2.pCoreIn 2)
    cubicActor_normalizes_parabolic_core
  ConjugationSection (Y := H2.pCoreIn 2) A N R f

variable {A N R f}

theorem opposite_section_length [Finite G] (s : ModuleShape)
    (d : OppositeSection A N R f s)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A N R = 1 := by
  let := action s.opposite
  exact (d.length_eq hA hR hf).trans s.opposite_length

theorem standard_section_length [Finite G] (s : ModuleShape)
    (d : StandardSection A N R f s)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A N R = 2 := by
  let := action s.standard
  exact (d.length_eq hA hR hf).trans s.standard_length

theorem standard_dual_section_length [Finite G] (s : ModuleShape)
    (d : StandardDualSection A N R f s)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A N R = 2 := by
  let := action s.standard.dual
  exact (d.length_eq hA hR hf).trans s.standard_dual_length

theorem duad_core_section_length [Finite G] (d : DuadCoreSection A N R f)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A N R = 1 := by
  let := conjMulDistribMulActionOfLeNormalizer duadCubicActor (H1.pCoreIn 2)
    duadCubicActor_normalizes_parabolic_core
  exact (d.length_eq hA hR (cubicActorEquiv.surjective.comp hf)).trans
    ((conjugationCubicLength_eq _ _ duadCubicActor_normalizes_parabolic_core).symm.trans
      duadCubicActor_parabolic_core_length)

theorem syntheme_core_section_length [Finite G] (d : SynthemeCoreSection A N R f)
    (hA : IsPGroup 3 A) (hR : IsPGroup 2 R) (hf : Function.Surjective f) :
    sectionCubicLength A N R = 1 := by
  let := conjMulDistribMulActionOfLeNormalizer cubicActor (H2.pCoreIn 2)
    cubicActor_normalizes_parabolic_core
  exact (d.length_eq hA hR hf).trans
    ((conjugationCubicLength_eq _ _ cubicActor_normalizes_parabolic_core).symm.trans
      cubicActor_parabolic_core_length)

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefModels

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
open ChiefModels
variable {G : Type*} [Group G]

/-- The denominator in 13.7.4(2), kept separate from the central line V₁. -/
def dualDenominator (H V₃ : Subgroup G) : Subgroup G :=
  Source.UH H V₃ ⊓ centralizer (Source.QH H : Set G)

/-- Compatible coordinates for the actual dual sections. The first map identifies
`UH/C_UH(QH)` and the second identifies `QH/HC` with its contragredient dual.
Both maps retain their kernels and the same marked actor. -/
structure DualSectionModels (A H V₃ : Subgroup G) (f : A →* cubicActor) where
  shape : ModuleShape
  primal : StandardSection A (dualDenominator H V₃) (Source.UH H V₃) f shape
  dual : StandardDualSection A (Source.HC H V₃) (Source.QH H) f shape

/-- The concrete maps needed for the final comparison. These are quotient maps
with specified kernels and equivariance, not chief-factor counts. The source
assembly supplies them from 13.8.27, 13.7.4 and the abelian module reduction. -/
structure FiltrationModels (A Q L H V₃ V V₁ P : Subgroup G)
    (f : A →* cubicActor) where
  spanShape : ModuleShape
  centralizerShape : ModuleShape
  uhShape : ModuleShape
  v : OppositeSection A ⊥ V f .natural
  span : OppositeSection A V (Source.UL L H V₃) f spanShape
  centralizer : OppositeSection A (CQUL Q L H V₃) Q f centralizerShape
  uh : StandardSection A V₁ (Source.UH H V₃) f uhShape
  duality : DualSectionModels A H V₃ f
  leftQuotient : LocalCoreQuotient A Q P duadCubicActor
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 (cubicActorEquiv.toMonoidHom.comp f)
  rightQuotient : LocalCoreQuotient A (Source.QH H) P cubicActor
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2 f

/-- Count both sections of the exact source duality, without changing its denominator. -/
theorem DualSectionModels.lengths [Finite G] {A H V₃ : Subgroup G}
    {f : A →* cubicActor} (d : DualSectionModels A H V₃ f)
    (hA : IsPGroup 3 A) (hUH : IsPGroup 2 (Source.UH H V₃))
    (hf : Function.Surjective f) :
    sectionCubicLength A (dualDenominator H V₃) (Source.UH H V₃) = 2 ∧
      sectionCubicLength A (Source.HC H V₃) (Source.QH H) = 2 :=
  ⟨standard_section_length d.shape d.primal hA hUH hf,
    standard_dual_section_length d.shape d.dual hA (isPGroup_pCoreIn 2 H) hf⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
