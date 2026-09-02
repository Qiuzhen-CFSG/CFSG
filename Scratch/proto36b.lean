module
import Stellmacher.SectionsOneToFourDefs
open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionThree
universe u
variable {G : Type u} [Group G] [Finite G]
variable (P A A0 : Subgroup G) (a : G)
noncomputable example : Prop :=
  (A : Set G) = (Subgroup.zpowers a : Set G) * (A0 : Set G)
noncomputable example (Z L : Subgroup G) : Prop :=
  ∀ z₁ z₂ : G, z₁ ∈ conjugateOrbitSet Z L → z₂ ∈ conjugateOrbitSet Z L →
    ∃ t : L, Theory.Comparator.IsInvolution (t : G) ∧
      (t : G) * z₁ * (t : G)⁻¹ = z₂
end Stellmacher.SectionThree
