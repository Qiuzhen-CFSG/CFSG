module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Sieve
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.MovedSpace

/-!
# The B.5 source reduction for the original moved-module classification

The source hypotheses construct the actual faithful FF action and its SQTK
cover. The original component belongs to its best-offender group and has
image PSL₂(4) or PSL₃(2). The S₃ and outer A₆ rows are impossible. In the
quasisimple row, component maximality identifies the generalized Fitting
subgroup with this same original component, so all six B.5.1 clauses now
apply to it with their original module and quotient data.

The accompanying coordinates identify its moved vector space, central
subspace and dimension with U, C_U(L) and rank U. This is the checked source
reduction, not the four-way marking theorem: the remaining work must extract
the natural, symmetric-five, repeated-natural and rank-four rows and prove
[Ω₁Z(T),L]=1 in the last case. The only earlier premise retained here is
L=[L,J(T)], whose source discharge belongs to `qt-d-1317-supplements`.

Source: Aschbacher--Smith 13.1.10, printed pp.871--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The first surviving B.5 row is marked by the original component image. -/
theorem reducedOffender_component_cases
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    let J := offenderSubgroup (reducedRepresentation L)
    let K := (NormalizerReducedAction.componentImage L).subgroupOf J
    let ρ := (reducedRepresentation L).comp J.subtype
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ K) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (HyperplaneCase ρ) := by
  rcases reducedOffender_three_cases h hmany hL hn hmove with ⟨hq,hd⟩ | hd
  · apply Or.inl
    have hc := reducedOffender_component h hmany hL hn hmove
    have he := hc.eq_of_le
      (show IsComponent (offenderSubgroup (reducedRepresentation L))
        (generalizedFitting (offenderSubgroup (reducedRepresentation L))) from
        ⟨(inferInstance : (generalizedFitting _).Normal).isSubnormal, hq⟩)
      (component_le_generalizedFitting _ _ hc)
    rw [he]
    exact hd
  · exact Or.inr hd

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
