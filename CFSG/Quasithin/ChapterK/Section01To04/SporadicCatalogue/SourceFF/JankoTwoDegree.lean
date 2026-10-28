module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Basic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TraceCompleteness
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddPrimary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.AutomorphismRankBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.FourConjugateGeneration
public import Theory.Representation.NormalPSubgroupKernel

/-!
# The original J2 FF source has a center-free component and degree twelve

The actual odd-primary cover theorem makes the component center a two-group;
faithful irreducibility in characteristic two kills it. Four-conjugate
generation and the sufficient automorphism two-rank bound six put the original
FF module in degree at most twenty-four. The complete binary degree spectrum
then excludes twenty-eight and leaves twelve.

The original actor, generalized Fitting subgroup, faithful module and literal
central-quotient marking are preserved. No module recognition is assumed.
Source: Aschbacher--Smith B.4.2 and K.4, printed pp.86 and 457--460;
GM02 Proposition 5.1, J2 paragraph.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The literal J2 central quotient forces the original binary FF module into degree twelve. -/
theorem j2_center_and_degree (h : RankOne.SourceHypotheses ρ L) (hff : IsFFModule ρ)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier)) :
    center L = ⊥ ∧ Module.finrank (ZMod 2) V = 12 := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  have hz2 := Theory.SpecificGroups.J2HSMultipliers.J2.center_isPGroup_of_quotient_equiv e
  have hk := normal_p_subgroup_le_ker (ρ.comp (generalizedFitting G).subtype)
    (center (generalizedFitting G)) hz2
  have hZ : center (generalizedFitting G) = ⊥ := by
    apply bot_unique
    simpa only [(ρ.comp (generalizedFitting G).subtype).ker_eq_bot_iff.mpr
      (h.faithful.comp (generalizedFitting G).subtype_injective)] using hk
  refine ⟨hZ, ?_⟩
  let eL : generalizedFitting G ≃* Carrier :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) := h.quasisimple.simple
  let : IsSimpleGroup Carrier := e.symm.isSimpleGroup
  let : IsSimpleGroup (generalizedFitting G) := eL.isSimpleGroup
  have hr : primeRank 2 G ≤ 6 :=
    (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
      h.faithful h.irreducible e).trans automorphism_primeRank_le_six
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  have hd : Module.finrank (ZMod 2) V ≤ 24 := by
    simpa using finrank_le_of_cubicRatio_le_of_conjugates ρ (generalizedFitting G) hfix
      (m := 1) (FourConjugateGeneration.involution_conjugate_generation_bound eL) hr
      (by simpa only [Nat.cast_one] using (isFFModule_iff_cubicRatio_le_one ρ).mp hff)
  let σ := (ρ.comp (generalizedFitting G).subtype).comp eL.symm.toMonoidHom
  have hfσ : Function.Injective σ :=
    h.faithful.comp ((generalizedFitting G).subtype_injective.comp eL.symm.injective)
  have hiσ : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eL.symm.toMonoidHom eL.symm.surjective _).mpr h.irreducible
  exact Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hfσ hiσ (by omega)

end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
