module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
public import Theory.GroupTheory.CharacteristicImageNormalizer

/-!
# Normalization and a marked generator of the original scalar residual

Characteristicity of the central preimage and of its two-residual makes
N_G(K) normalize the literal X. Its exact original quotient image supplies
a lift of the marked cubic scalar. No split complement is assumed.

Source: the use of X in Aschbacher--Smith12.7.19, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

omit [Finite G] in
/-- The full normalizer of K preserves its unchanged scalar residual. -/
theorem tripleSixScalarResidual_normalizer :
    normalizer (K : Set G) ≤ normalizer (tripleSixScalarResidual K : Set G) := by
  let Z := centralPreimage (pCore 2 K)
  exact (normalizer_le_normalizer_characteristic_image K Z).trans
    (normalizer_le_normalizer_characteristic_map Z (pResidual 2 Z) K.subtype K.subtype_injective)

/-- A marked cubic scalar has a lift in the actual residual, with its
original K-quotient value retained. -/
theorem tripleSixScalarResidual_scalar_lift (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    ∃ (c : tripleSixScalarResidual K) (hcK : (c : G) ∈ K),
      a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨c.val,hcK⟩) = Atlas.Codes.hexEvenZ := by
  have hz : Atlas.Codes.hexEvenZ ∈ center Atlas.Codes.HexEvenAutomorphisms := by
    rw [←Hexacode.even_kernel_eq_center,Atlas.Codes.hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hm := (tripleSixScalarResidual_image D a).symm ▸ hz
  obtain ⟨c,hc,he⟩ := hm
  exact ⟨⟨c.val,hc⟩,c.property,he⟩

end CFSG.Quasithin.Chapter12.Section07
