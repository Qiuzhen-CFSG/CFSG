module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AmbientSylowCommutator
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.CrossCentralization
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.BlockRecovery.Original
/-!
# The original natural component has the literal commutator Sylow

The original component remains subnormal in its orbit–Baumann join, by
restriction from the original maximal local subgroup. Thus the actual
Baumann Sylow supplied by E.2.3 restricts to a full Sylow of L. The natural
block torus calculation identifies it with [Baum(T),A] itself.

The intrinsic core=U equality remains an explicit recovery input. This
module does not yet assert that the second component is a block or shares
this Sylow. Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open ChapterC Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original E.2.3 Sylow statement gives the source commutator Sylow in L. -/
theorem source_original_natural_commutator_sylow (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hL : IsL2EvenBlock L 2) (hcore : pCore 2 L = blockU L)
    (hS : Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (localOrbit T L ⊔ ChapterB.baumann (T : Subgroup G)))
    (hAL : A ≤ L) (hA : Nat.card A = 3)
    (hAS : A ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (hSL : ChapterB.baumann (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ⁅ChapterB.baumann (T : Subgroup G),A⁆ = ChapterB.baumann (T : Subgroup G) ⊓ L ∧
      Chapter1.IsSylowIn 2 ⁅ChapterB.baumann (T : Subgroup G),A⁆ L := by
  let X := localOrbit T L ⊔ ChapterB.baumann (T : Subgroup G)
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hXM : X ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hsub := (D.component_in_maximalLocal.subgroupOf_of_le hLX hXM).subnormal
  exact IsL2EvenBlock.ambient_odd_commutator_sylow_of_subnormal
    L (ChapterB.baumann (T : Subgroup G)) A X hL hcore hS hLX hsub hAL
      (by rw [hA]; decide) (by intro he; rw [he,card_bot] at hA; contradiction) hAS hSL
end CFSG.Quasithin.Chapter10
