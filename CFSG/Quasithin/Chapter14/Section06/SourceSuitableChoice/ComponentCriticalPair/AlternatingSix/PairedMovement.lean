module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Application
public import Theory.Representation.AlternatingSixPairedCovers.Movement

/-!
# The terminal A₆ obstruction after the paired movement calculation

The original H = Mc action now supplies both nontrivial component sections
and the absence of transvections directly from its marked natural or
five-dimensional covering supports. The existing critical-pair selection and
F.9 equality argument therefore need only the simultaneous quadratic-actor
classification. All quotient and group markings are unchanged.

This is still a conditional source application. Construction of the support
markings and the quadratic-actor bound belongs to qt-e-suitable-component-marking,
using the actual 14.6.20–23 input from qt-e-suitable-component-supports. Final
suitable choice belongs to qt-e-suitable-existence. Source: Aschbacher–Smith,
original 14.6.24(2), printed p.1041.
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

/-- Original-source consumer of the simultaneous paired-module calculations.
The two nontrivial sections and absence of transvections are now proved
from the paired covers. Only the simultaneous quadratic-actor classification
remains explicit in this consumer. -/
theorem terminal_obstruction_of_paired_actors
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
    (C : AlternatingSixPairedCovers.Data ρ)
    (hpaired : ∀ B : Subgroup (Source.Hstar Mc),
      0 < rank B → Reorientation.QuadraticMember ρ B →
      rank B ≤ 2 ∧ ∃ t : alternatingGroup (Fin 6), orderOf t = 2 ∧ C.component t ∈ B) : False := by
  apply terminal_obstruction_of_paired_calculations hG T hempty hM hunique hmany hcard
    e hab s ?_ C C.nontrivial_sections.1 C.nontrivial_sections.2 hpaired
  intro a ha
  apply C.two_le_movement a
  intro he
  subst a
  simp at ha

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
