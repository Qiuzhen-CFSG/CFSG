module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuEleven
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLarge
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLargeTwentyThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLargeTwentyFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MaximalCentralizers
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.HeldRudvalis
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.HigmanSims
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.JankoFour

/-!
# The complete initial ordinary sporadic family

The sporadic marking in 1.1.5 excludes J₃. The ten remaining actual carriers
are exhausted here using their source Ordinary20 rows; the J₄ case is
impossible by its local M₂₄ subgroup. Every surviving row retains its literal
Sylow-center centralizer and the entire central two-cover.

This assembles the sporadic branch of Aschbacher--Smith 15.1.20(3), printed
pp.1096--1097, at the original component. The later HS/Ru exclusions and
Ordinary22 residual refinements are separate obligations of this owner.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Every sporadic marking allowed by 1.1.5 supplies the full initial row at the
same original component, with no residual local or model callback. -/
theorem PreExclusionSource.ordinary20_of_sporadic_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (name : SporadicName) (not_j3 : name ≠ .j3)
    (model : Nonempty ((d.L ⧸ pCore 2 d.L) ≃* name.Carrier)) :
    d.Ordinary20Alternatives := by
  obtain ⟨e⟩ := model
  cases name with
  | m11 => exact s.ordinary20_of_mathieuEleven_quotient (h := h) hG hM hu hL e
  | m12 => exact s.ordinary20_of_mathieuTwelve_quotient (h := h) hG hM hu hL e
  | m22 => exact s.ordinary20_of_mathieuTwentyTwo_quotient (h := h) hG hempty hM hu hL e
  | m23 => exact s.ordinary20_of_mathieuTwentyThree_quotient (h := h) hG hempty hM hu hL e
  | m24 => exact s.ordinary20_of_mathieuTwentyFour_quotient (h := h) hG hempty hM hu hL e
  | j2 => exact s.ordinary20_of_jankoTwo_quotient (h := h) hG hM hu hL e
  | j3 => exact (not_j3 rfl).elim
  | j4 => exact s.ordinary20_of_jankoFour_quotient (h := h) hG hempty hM hJ hu hL e
  | hs => exact s.ordinary20_of_higmanSims_quotient (h := h) hG hM hu hL e
  | he => exact s.ordinary20_of_held_quotient (h := h) hG hM hu hL e
  | ru => exact s.ordinary20_of_rudvalis_quotient (h := h) hG hM hu hL e

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
