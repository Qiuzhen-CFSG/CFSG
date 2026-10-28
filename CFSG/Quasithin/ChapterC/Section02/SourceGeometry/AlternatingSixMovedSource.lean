module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMoved
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedModel

/-!
# The original A₆ star commutator has order sixteen or thirty-two

The actual C.2.7 input supplies the complete B.5 moved-section classification.
Comparison with its specified alternating-six component retains the Irr⁺
natural quotient. The universal augmentation cover then bounds the literal
commutator subgroup, without a splitting premise or a block identification.

Source: Aschbacher–Smith C.2.7 and B.5.1, pp.145–147 and99–103; used in
14.6.10(5), p.1029.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- All B.5 rows and central-cover premises are discharged by the original
C.2.7 input and its given alternating-six star component. -/
theorem star_alternatingSix_moved_card_from_source
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    Nat.card (⁅starV K R, K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) = 16 ∨
    Nat.card (⁅starV K R, K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) = 32 := by
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  obtain ⟨hi,⟨a⟩⟩ := AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans e)
  exact star_alternatingSix_moved_card K R hCJ c.sectionData hi a

/-- The sufficient rank bound on the original star commutator. -/
theorem star_alternatingSix_moved_card_le_thirtyTwo
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6)) :
    Nat.card (⁅starV K R, K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G)) ≤ 32 := by
  rcases star_alternatingSix_moved_card_from_source h e with hc | hc <;> omega

end CFSG.Quasithin.ChapterC.C27Source
