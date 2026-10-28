module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceCubicComponent

/-!
# Excluding the equal-centralizer rows in Case I

The literal fixed plane V₁ centralizes Y=O^{3′}(M ∩ G₁). The preceding
component theorem identifies Y with O^{3′}(M ∩ L), while the exchanged
plane proves that V₁ does not centralize L. Consequently their centralizers
in the same S cannot agree. This is the exclusion of rows (2), (4), (5),
and (7) used in 15.1.26, once the actual quotient and centralizer catalogue
has supplied that row's equality. No replacement actor or Sylow is used.

Source: Aschbacher--Smith 15.1.24(4), 15.1.25(1),(3), and 15.1.26,
printed pp.1101--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- The original Nine component cannot belong to a source22 row whose cubic
residual has the same centralizer in S as L. The earlier source input and the
literal quotient facts remain explicit at their mathematical boundaries. -/
theorem PreparedChosenModule.source_caseI_nine_no_equal_centralizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      pPrimeCore 2 d.G1 = ⊥ ∧ IsQuasisimple (d.L ⧸ pCore 2 d.L) ∧
      d.L ∈ Chapter1.L G d.S ∧ Chapter1.IsSylowIn 2 d.SL d.L ∧
      (Facts (d.L ⧸ pCore 2 d.L) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) := by
  let := h.elementary
  obtain ⟨d,hr,hz,ho,hq,hL,hSL,_,_,_,_,_,_,hm⟩ :=
    h.source_caseI_nine_cubic_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,hr,hz,ho,hq,hL,hSL,?_⟩
  intro hf heq
  obtain ⟨_,hY,hn⟩ := hm hf
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let Y := (primeToResidual 3 C).map C.subtype
  let V1 := V ⊓ centralizer (R : Set G)
  have hYR : Y ≤ R := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hV1SY : V1 ≤ d.S ⊓ centralizer (Y : Set G) :=
    le_inf (le_inf (inf_le_left.trans hVT)
      (inf_le_left.trans (V.le_centralizer.trans
        (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
      (inf_le_right.trans (centralizer_le hYR))
  have heq' : d.S ⊓ centralizer (Y : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
    change d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map
      (M ⊓ d.G1).subtype) : Set G) = _
    rw [hY]
    exact heq
  exact hn ((hV1SY.trans heq'.le).trans inf_le_right)
end CFSG.Quasithin.Chapter15.Section01
