module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.PairedMovement
public import Theory.Representation.AlternatingSixPairedCovers.InvolutionMovement

/-!
# The A₆ critical-pair obstruction from the same paired covers

The simultaneous quadratic calculation now proves rank two and an actual
component involution for every positive-rank quadratic member of the original
whole action. All involutions move at least three dimensions, so rank one is
impossible. The existing F.9 equality/transvection argument therefore excludes
this A₆ marked action without an actor-classification callback.

This is still a conditional source application: constructing these precise
paired support markings from original 14.6.20–23 belongs to
qt-e-suitable-component-marking, using qt-e-suitable-component-supports.
Final suitable choice belongs to qt-e-suitable-existence. Source:
Aschbacher–Smith, original 14.6.24(2), printed p.1041.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The original-source A₆ obstruction, with every simultaneous actor and
movement premise discharged from the same paired covers. -/
theorem terminal_obstruction_of_paired_covers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) ρ)
    (C : AlternatingSixPairedCovers.Data ρ) : False := by
  apply terminal_obstruction_of_paired_actors hG T hempty hM hunique hmany hcard e hab s C
  intro B _ hB
  obtain ⟨hr,ht⟩ := C.quadratic_member B hB.1 hB.2.1 hB.2.2
  exact ⟨hr.le,ht⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
