module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Equality
public import Theory.Representation.AlternatingSixInvolutionDisplacement

/-!
# Two A6 sections exclude a small critical actor

An involution in A6 moves at least two dimensions on each nontrivial binary
section. The submodule and its literal quotient therefore force movement
at least four. If this involution lies in the critical actor, a rank bound
of two and the proved F.9 estimate force rank two and fixed codimension four.
The equality theorem then contradicts its action on the actual denominator.

The two sections need not be direct summands. In particular the intended
application takes the image of one covering support and then the quotient
by that image, retaining any common central kernel of the covers.

Source: Aschbacher--Smith, 14.6.24(2), printed p.1041. The simultaneous
quadratic-action calculation on the diagram-twisted supports must supply
the rank bound and the involution in the component image.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer

variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Two actual component sections force the equality obstruction. Only the
upper rank bound is supplied by the paired-module classification. -/
theorem critical_two_sections_obstruction
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison : Reorientation.denominatorRank D.Vplus D.V₁ c ≤
      rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (hrank : rank (Source.starImage D.H (c.Ugamma D.Vplus)) ≤ 2)
    (f : alternatingGroup (Fin 6) →* Source.Hstar D.H)
    (U : Subrepresentation (ρ.comp f))
    (hU : ∃ g, U.toRepresentation g ≠ 1)
    (hQ : ∃ g, U.quotientRepresentation g ≠ 1)
    (t : alternatingGroup (Fin 6)) (ht : orderOf t = 2)
    (htB : f t ∈ Source.starImage D.H (c.Ugamma D.Vplus)) : False := by
  have ht4 : 4 ≤ fixedCodim ρ (zpowers (f t)) := by
    have ht4 := AlternatingSixInvolutionDisplacement.four_le_fixedCodim_of_nontrivial_submodule_and_quotient
      (ρ.comp f) U hU hQ t ht (mem_zpowers t)
    change 4 ≤ Module.finrank (ZMod 2)
      (E ⧸ fixedSpace (ρ.comp f) (zpowers t)) at ht4
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers] at ht4
    exact ht4
  have hlo : 4 ≤ fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus)) := by
    have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr htB))
    have hcyc := fixedCodim_add_finrank ρ (zpowers (f t))
    have hwhole := fixedCodim_add_finrank ρ (Source.starImage D.H (c.Ugamma D.Vplus))
    omega
  have hbound := SourceCompletion.f9_fixedCodim_le_twice_rank D h c hb s hcomparison
  have hr : rank (Source.starImage D.H (c.Ugamma D.Vplus)) = 2 := by omega
  have hc : fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus)) = 4 := by omega
  exact critical_equality_obstruction D h c hb s hcomparison hr hc ⟨f t,htB⟩ ht4

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Apply the two-section obstruction to the original terminal H=Mc.
No F.9 setup, elementary-section instance, or equality conclusion is assumed. -/
theorem terminal_two_sections_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) Mc (localModule T M))
    (hb : 3 ≤ c.path.length)
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) ρ)
    (hcomparison : Reorientation.denominatorRank (localModule T M) (centralInvolutions T) c ≤
      rank (Source.starImage Mc (c.Ugamma (localModule T M))))
    (hrank : rank (Source.starImage Mc (c.Ugamma (localModule T M))) ≤ 2)
    (f : alternatingGroup (Fin 6) →* Source.Hstar Mc)
    (U : Subrepresentation (ρ.comp f))
    (hU : ∃ g, U.toRepresentation g ≠ 1)
    (hQ : ∃ g, U.quotientRepresentation g ≠ 1)
    (t : alternatingGroup (Fin 6)) (ht : orderOf t = 2)
    (htB : f t ∈ Source.starImage Mc (c.Ugamma (localModule T M))) : False := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis :=
    ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact critical_two_sections_obstruction D h c hb s hcomparison hrank f U hU hQ t ht htB

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
