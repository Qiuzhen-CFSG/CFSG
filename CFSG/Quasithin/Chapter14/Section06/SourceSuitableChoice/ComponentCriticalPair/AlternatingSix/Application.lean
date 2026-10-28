module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Selection
public import Theory.Representation.AlternatingSixPairedCovers.Inputs

/-!
# Source application of the paired-cover calculation

The original rank-two setup constructs a critical pair and, using the absence
of involution transvections, selects a positive-rank quadratic actor with the
required denominator comparison. A paired-model rank bound and an involution
in its alternating component then force rank two and fixed codimension four.
The proved equality/transvection consequence of F.9 gives the contradiction.

Source: Aschbacher--Smith, 14.6.24(2), printed p. 1041. This is a conditional
consumer, not yet the exclusion of the A6 quotient alternative: the concrete
model calculations and the identification of these data with the literal
14.6.20--23 component supports must still be discharged.
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
The critical pair, its denominator comparison, rank two, and the equality case
are all derived. The remaining model inputs are stated explicitly. -/
theorem terminal_obstruction_of_paired_calculations
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
    (hno : ∀ a : Source.Hstar Mc, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a))
    (C : AlternatingSixPairedCovers.Data ρ)
    (hU : ∃ g, C.first.toRepresentation g ≠ 1)
    (hQ : ∃ g, C.first.quotientRepresentation g ≠ 1)
    (hpaired : ∀ B : Subgroup (Source.Hstar Mc),
      0 < rank B → Reorientation.QuadraticMember ρ B →
      rank B ≤ 2 ∧ ∃ t : alternatingGroup (Fin 6), orderOf t = 2 ∧ C.component t ∈ B) : False := by
  obtain ⟨c,hb,_,_,hp,hcomparison,hquadratic⟩ :=
    terminal_critical_quadratic_selection hG T hempty hM hunique hmany hcard e hab s hno
  obtain ⟨hrank,t,ht,htB⟩ := hpaired _ hp hquadratic
  exact terminal_two_sections_obstruction hG T hempty hM hunique hmany hcard e hab
    c hb s hcomparison hrank C.component C.first hU hQ t ht htB

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
