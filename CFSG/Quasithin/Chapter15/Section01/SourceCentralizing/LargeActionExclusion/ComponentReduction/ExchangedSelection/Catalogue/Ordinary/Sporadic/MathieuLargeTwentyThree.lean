module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MaximalCentralizers
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLarge
public import Theory.Mathieu.M23.OrdinarySource
public import Theory.Mathieu.M23.Properties.ElementarySylowFixers

/-!
# The initial M₂₃ row through its actual central cover

The original Sylow-center hypothesis first puts the actual marked centralizer
inside M_L. The empty faithful-local-family hypothesis then places the residual
of its literal quotient-model image inside the marked involution centralizer.
The native M₂₃ centralizer is perfect and its center is the marked involution
line. Hence residual containment makes it normal in that image, and preservation
of its marked center gives equality. No maximal-overgroup classification is used.

The full central two-cover, original L/O₂(L) quotient map, and original datum
are retained. Source: Aschbacher--Smith 14.1.6 and 15.1.20(3d), pp.977,1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The complete original M₂₃ constructor, retaining central two-covers.
The genuinely required empty-family hypothesis discharges residual control. -/
theorem PreExclusionSource.ordinary20_of_mathieuTwentyThree_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M23) : d.Ordinary20Alternatives := by
  let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
    (subgroupOfEquivOfLe d.L_component.1)
  let : IsSimpleGroup (d.L ⧸ center d.L) := IsQuasisimple.simple
  let ec := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq).trans e
  let : IsSimpleGroup Sporadic.Mathieu.M23 := ec.symm.isSimpleGroup
  apply Ordinary20Alternatives.sporadic .m23 (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  apply s.centralizer_eq_of_quotient_residual_control (h := h) hG hempty hM hu hL e
  · exact Sporadic.Mathieu.M23Geometry.m23_center_eq_bot
  · intro Q a ha
    obtain ⟨g,hg⟩ := Sporadic.Mathieu.m23_conj_surjective a
    exact ⟨g,hg.symm⟩
  · exact Sporadic.Mathieu.m23_sylow_center_card_le_two
  · intro U t ht _ hCU hR
    exact Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.centralizer_eq_of_residual_le
      U t ht hCU hR

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
