module

public import CFSG.Quasithin.ChapterB.Section01.IrreducibleSections

/-!
# The representation inputs to the alternating-cover step of B.1.13

The source selects an Irr⁺ section detecting the order-three center before
invoking the faithful irreducible FF exclusion for 3.A₇. B.1.11 by itself does
not assert that center detection. These two explicit contracts separate the
section construction from the intrinsic representation exclusion; neither
contract is asserted here. The restriction identity uses the literal maps
and quotient actions, so their composition has no unproved transport premise.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.13,
printed pp. 73–74 (PDF pp. 84–85), and the reference to B.4.2 there.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
universe u v w

/-- The precise remaining representation theorem: a faithful irreducible
binary action of a triple cover of A₇ admits no FF extension in its linear
normalizer. The homomorphism and normality refer to the actual acting group. -/
def SevenFFExclusion : Prop :=
  ∀ {L : Type u} {H : Type v} {W : Type w}
    [Group L] [Finite L] [IsQuasisimple L] [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ι : L →* H), Function.Injective ι → ι.range.Normal →
    ∀ (σ : Representation (ZMod 2) H W),
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
      Nat.card (center L) = 3 →
      Function.Injective (σ.comp ι) → Representation.IsIrreducible (σ.comp ι) →
      ¬ IsFFModule (imageRepresentation σ)

/-- An actual member of Irr⁺ with an FF overgroup action and faithful L-action
on its literal central quotient. This is stronger than the output of B.1.11. -/
def HasFaithfulIrreducibleFFSection {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  ∃ (H : Subgroup G) (I : Submodule (ZMod 2) V), L ≤ H ∧
    ∃ (hI : IsIrrPlus ρ L I)
      (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)),
      IsFFModule (imageRepresentation (centralSectionRepresentation ρ L H I hHI hHN)) ∧
      Function.Injective (centralQuotientRepresentation ρ L I hI.choose)

/-- Restricting the overgroup action along the actual subgroup inclusion
gives exactly the central quotient action used in Irr⁺. -/
theorem centralSection_comp_inclusion {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L H : Subgroup G) (hLH : L ≤ H)
    (I : Submodule (ZMod 2) V) (hLI : L ≤ subspaceStabilizer ρ I)
    (hHI : H ≤ subspaceStabilizer ρ I) (hHN : H ≤ normalizer (L : Set G)) :
    (centralSectionRepresentation ρ L H I hHI hHN).comp (inclusion hLH) =
      centralQuotientRepresentation ρ L I hLI := by
  rfl

end CFSG.Quasithin.ChapterB.ComponentRecognition.AlternatingCovers
