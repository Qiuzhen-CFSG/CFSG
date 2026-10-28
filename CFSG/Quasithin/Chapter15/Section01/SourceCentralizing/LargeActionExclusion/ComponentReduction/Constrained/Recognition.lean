module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Exclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Exclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne

/-!
# Constrained quotient recognition after the original block exclusions

The original marker excludes rank one, and the actual exchanged residual
excludes the binary SL3 block. The permutation argument excludes A7;
A6 and G2 are excluded by their literal centralizer identities. The only
surviving catalogue rows give actual SL4(2) or SL5(2) quotient isomorphisms.

Catalogue exhaustiveness remains with qt-e-1515-constrained-source-catalogue;
its final discharge belongs to qt-e-1515-constrained-linear-quotient. The
original-marker input is constructed in the actual Nine application.
Source: Aschbacher--Smith 15.1.21, 15.1.24--26, pp.1097--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- All small-block exclusions are discharged on the same original component;
only genuine source-catalogue exhaustiveness remains explicit. -/
theorem ExchangedSource.constrained_linear_quotient_of_catalogue
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hc : d.ConstrainedAlternatives) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
  s.constrained_linear_quotient_of_source_alternatives hG hM.1.2 h hc
    (sp.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ)
    (s.no_constrained_l3 (h := h) sp hG hempty hM.1.2 hu)
    (s.no_constrained_a7 hG hM.1.2 h)

/-- The recognized quotient, attached to the original fitting premise. -/
theorem ExchangedSource.hasExchangedLinearSource_of_catalogue
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfit : generalizedFitting d.L = pCore 2 d.L)
    (hc : d.ConstrainedAlternatives) : d.HasExchangedLinearSource :=
  ⟨s,hfit,s.constrained_linear_quotient_of_catalogue (h := h) sp hG hempty hM hJ hu hc⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
