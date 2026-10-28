module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryClosure
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinarySmallCovers
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterM22
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterHS
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5Catalogue
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5G2Source
public import Theory.SpecificGroups.JankoTwo.CentralCoverElementary
public import Theory.Mathieu.SchurMultipliers.SourceCovers
public import Theory.Mathieu.SchurMultipliers.M23Kernel
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.Janko

/-!
# Remaining actual ordinary quotients at the original triple-six point

The unchanged elementary module of order 64 eliminates the alternating,
small Mathieu, Hall--Janko and Higman--Sims covers. The genuine center point
excludes the centerless Mathieu and Janko-four covers. The actual G₂ radical
center bound removes G₂(4). The remaining Held and Rudvalis local inspections
are kept explicit alongside the required PSL₃(4) quotient.

Source: Aschbacher--Smith 12.7.5 and C.3.1, printed pp.840 and 149--151.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation PerfectCentralCovering
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ClassificationModels
variable {G : Type*} [Group G] [Finite G]

/-- The original C.2.8 module and central point narrow the complete ordinary
catalogue to the actual three remaining models. -/
theorem ordinary_tripleSix_models
    {H M L R U : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R U)
    (a : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hU : Nat.card U = 64) (J : Subgroup H) (hJ : IsComponent H J)
    (hz : center J ≠ ⊥) :
    ClassicalGroup.IsPSL (J ⧸ center J) 3 4 ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) ∨
      Nonempty ((J ⧸ center J) ≃* Rudvalis.Model) := by
  let := hJ.2
  have hUH : U ≤ H := h.module_le.trans
    ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
  have hUJ : U.subgroupOf H ≤ J := (h.ordinary_module_placement J hJ).1.trans inf_le_right
  let A := (U.subgroupOf H).subgroupOf J
  let : IsElementaryAbelian 2 U := h.module_elementary
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hUJ
  have hA : Nat.card A = 64 :=
    (Nat.card_congr ((subgroupOfEquivOfLe hUJ).trans
      (subgroupOfEquivOfLe hUH)).toEquiv).trans hU
  have hc : center J = pCore 2 J :=
    IsQuasisimple.center_eq_pCore (hJ.1.pPrimeCore_eq_bot h.oddCore_eq_bot J)
  have hp : IsPGroup 2 (center J) := hc ▸ pCore_isPGroup
  rcases h.ordinary_normal_natural_a5_models a J hJ hz with
    hm | hm | ⟨n,hn,⟨e⟩⟩ | hm | ⟨n,hn,⟨e⟩⟩
  · exact .inl hm
  · exact (h.ordinary_not_g2_four_of_module_card hU J hJ hm).elim
  · exact (original_point_ordinary_not_alternating A hA hn e).elim
  · exact (original_point_ordinary_not_psl_four_two A hA hm).elim
  · cases n with
    | m11 =>
      apply False.elim
      apply hz
      rw [←centralQuotientCover_ker e]
      exact Sporadic.Mathieu.SchurMultipliers.m11_cover_kernel_eq_bot (centralQuotientCover e)
    | m12 => exact (original_point_ordinary_not_m12 A hA e).elim
    | m22 => exact (original_point_ordinary_not_m22 A hA hp e).elim
    | m23 => exact (hz (Sporadic.Mathieu.SchurMultipliers.m23_center_eq_bot_of_centralQuotientEquiv e)).elim
    | m24 => exact (hz (Sporadic.Mathieu.SchurMultipliers.m24_center_eq_bot_of_centralQuotientEquiv e)).elim
    | j4 => exact (hz (Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv e hp)).elim
    | j3 => exact (hn rfl).elim
    | j2 => exact (Sporadic.LeechRelated.J2.quasisimple_elementary_sixty_four_false e A hA).elim
    | hs => exact (original_point_ordinary_not_hs A hA hp e).elim
    | he => exact .inr (.inl ⟨e⟩)
    | ru => exact .inr (.inr ⟨e⟩)

/-- All inputs to the three-model remainder are produced by the original
chosen-module configuration at the unchanged even-orbit point. -/
theorem original_tripleSix_point_ordinary_models_at
    {T : Sylow 2 G} {K U : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    ClassicalGroup.IsPSL (J ⧸ center J) 3 4 ∨
      Nonempty ((J ⧸ center J) ≃* Held.He) ∨
      Nonempty ((J ⧸ center J) ≃* Rudvalis.Model) := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  have h28 := original_tripleSix_pushingUp_at h structural D a t ht heven
  have hUL : U ≤ Lt := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  have hLH : Lt ≤ H := (map_subtype_le _).trans inf_le_right
  have hLJ := h28.ordinary_component_contains_original J hJ
  have htH : (t : G) ∈ H := hLH (hUL t.property)
  let tJ : J := ⟨⟨t,htH⟩,hLJ (hUL t.property)⟩
  have htZ : tJ ∈ center J := mem_center_iff.mpr fun x =>
    Subtype.ext (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))
  have hz : center J ≠ ⊥ := by
    intro he
    have ht1 : tJ = 1 := mem_bot.mp (he ▸ htZ)
    exact ht (Subtype.ext (congrArg (fun x : J => ((x : H) : G)) ht1))
  exact ordinary_tripleSix_models h28 (tripleSixPointResidualQuotientEquiv D a t ht heven)
    ((Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card)
    J hJ hz

end CFSG.Quasithin.Chapter12.Section07
