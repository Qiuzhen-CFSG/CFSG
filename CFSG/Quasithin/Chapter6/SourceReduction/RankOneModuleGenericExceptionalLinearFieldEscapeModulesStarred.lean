module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesTransfer
public import Theory.Representation.BinaryOffender.CubicOrbitRestriction
public import CFSG.Quasithin.ChapterD.Section02.Inheritance

/-!
# Minimum cubic offenders centralize the original residual component

D.2.7 bounds the ratio on the image of a minimum offender on a moved
homogeneous orbit. The orbit and its central quotient have the same
relative kernel, so this bound descends to the same faithful quotient
used by the original diagram argument. Its strict lower bound forces
the offender to centralize the component, even when it was not faithful
on that component. The Chapter 12 consumer supplies the orbit, bound,
and minimum offender from the original source groups.

Source: Aschbacher--Smith D.2.7 and 5.1.23, printed pp.180,645--646,
refs/quasithin.pdf. The geometric cubic bound and the remaining
three-prime component exclusion are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
variable {X W : Type*} [Group X] [Finite X]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem starred_centralizes_residual_of_orbit_bound
    (ρ : Representation (ZMod 2) X W) (K P : Subgroup X) [IsQuasisimple K]
    (hP : IsPGroup 2 P) (hs : HasFaithfulHomogeneousOrbitSection ρ K P)
    (hb : ResidualOrbitCubicBound ρ K P)
    {E : Subgroup X} (hEP : E ≤ P) (hE : E ∈ ChapterD.QhatStar ρ) :
    E ≤ centralizer (K : Set X) := by
  obtain ⟨I,hI,_⟩ := hs
  let U := orbitSpan ρ P I
  let J := K ⊔ P
  have hk := centralSection_kernel_le_centralizer_of_not_fixed ρ K J le_sup_left U
    (fun hh => hI.isIrrPlus.not_le_fixedSpace ρ ((le_orbitSpan ρ P I).trans hh))
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)
  by_contra hnot
  have hnon : ¬ U ≤ fixedSpace ρ E := by
    intro hfix
    apply hnot
    intro e he
    let e₀ : J := ⟨e,mem_sup_right (hEP he)⟩
    have hz : e₀ ∈ (orbitSectionRepresentation ρ hI).ker := by
      apply (centralSectionRepresentation_ker_iff _ _ _ _ _ _ e₀).mpr
      intro v hv
      change ρ e v - v ∈ fixedSpace ρ K
      have heq : ρ e v = v := hfix hv ⟨e,he⟩
      rw [heq,sub_self]
      exact Submodule.zero_mem _
    exact (hk (mem_map_of_mem J.subtype hz)).2
  have hstab : E ≤ subspaceStabilizer ρ U := hEP.trans (orbitSpan_invariant ρ P I)
  have hr := (ChapterD.RPlusBound.restricted ρ
    (show E ∈ ChapterD.RPlusBound ρ (cubicRatio ρ) from
      ⟨⟨hE.1.2.1,hE.1.2.2.2.le⟩,ChapterD.QhatStar.mem_RPlus ρ hE⟩) U hstab hnon).2
  exact not_le_of_gt (hb I hI)
    ((orbitSection_cubicRatio_le_restricted_actionRatio ρ hP hI hEP
      hE.1.2.1 hE.1.2.2.1 hnon).trans (hr.trans hE.1.1))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
