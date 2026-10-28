module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MaximalCentralizers
public import Theory.SpecificGroups.Held.OrdinaryLocal
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.OrdinaryLocal
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore

/-!
# Initial Held and Rudvalis rows with central two-covers

The actual quotient Sylow fixers are inner, and their Sylow centers have
order two. The maximal two-central centralizer therefore lifts through the
perfect central two-cover and forces equality with the original M_L.
For Rudvalis, simplicity is inherited from the source component and the
earlier odd-index maximal two-core theorem supplies the remaining model
premise. Both full initial sporadic constructors are proved without an
exchanged-source witness or any catalogue assumption.

The initial exhaustion and the later 15.1.22 clauses remain with this
ordinary catalogue owner. In particular, the later characteristic-subgroup
exclusion of Rudvalis is separate from its initial 15.1.20 row.
Source: Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The complete initial Held row retains the original two-core quotient,
all central two-covers, and the literal Sylow-center centralizer. -/
theorem PreExclusionSource.ordinary20_of_held_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Held.He) :
    d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.sporadic .he (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  apply s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
    Held.LocalPairs.center_eq_bot
  · intro P a ha
    obtain ⟨t,ht⟩ := Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow
      Held.Realization.normalizer_surjective P a ha
    exact ⟨t,ht.symm⟩
  · exact Held.LocalPairs.SylowGeometry.Calculations.inner_center_card
  · exact Held.OrdinaryLocal.twoCentral_centralizer_isCoatom

/-- The Rudvalis initial row uses simplicity inherited from the source
component and discharges the odd-index two-core premise by the proved earlier
subgroup calculation. It retains every central two-cover. -/
theorem PreExclusionSource.ordinary20_of_rudvalis_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Rudvalis.Model) :
    d.Ordinary20Alternatives := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let f := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup Rudvalis.Model := f.symm.isSimpleGroup
  apply Ordinary20Alternatives.sporadic .ru (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  apply s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
    Rudvalis.LowCentralizers.model_center_eq_bot
  · intro _ a _
    obtain ⟨t,ht⟩ := Rudvalis.component_conj_surjective a
    exact ⟨t,ht.symm⟩
  · exact Rudvalis.InvolutionCentralizers.sylow_center_card
  · exact Rudvalis.OrdinaryLocal.twoCentral_centralizer_isCoatom
      Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
