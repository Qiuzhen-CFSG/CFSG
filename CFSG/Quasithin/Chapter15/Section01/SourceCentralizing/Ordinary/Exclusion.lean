module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Models
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Selection
/-!
# Ordinary small components in the Case-I Nine branch

For the marked subgroup selected in the original Nine case, the cubic residual
escapes the distinguished maximal subgroup and its fixed plane does not centralize
the component.  The ordinary Mathieu and J₂ model bounds force equality of the
two residual centralizers, contradicting that fixed-plane movement.  The selection
is shared by both arguments, so no identification of existential markers is used.

Every recognized small model supplies the source cubic Facts from its concrete
center, three-rank and outer-automorphism APIs. Source: Aschbacher–Smith, *The
Classification of Quasithin Groups*, Section 15.1, (15.1.20)–(15.1.26).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
theorem PreparedChosenModule.source_caseI_nine_ordinary_small_model_exclusion
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.SmallOrdinaryModel (d.L ⧸ pCore 2 d.L)) := by
  let := h.elementary
  obtain ⟨d,hr,hz,ho,hq,hL,hSL,_,_,_,_,_,_,hout,hm⟩ :=
    h.source_caseI_nine_fixed_plane_movement_and_escape hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,hr,hz,ho,hq,hL,hSL,?_⟩
  intro hc he
  let := hq
  have hf := CaseIComponentData.facts_of_small_model he
  have heq := d.ordinary_small_model_centralizer hG hM.1.2 hu h hc ho hSL hf he hout
  have hY := (d.source_cubic_component hG h hf).2
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
  exact hm hf ((hV1SY.trans heq'.le).trans inf_le_right)

theorem PreparedChosenModule.source_caseI_nine_ordinary_m11_exclusion
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
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11)) := by
  obtain ⟨d,hr,hz,ho,hq,hL,hSL,hn⟩ :=
    h.source_caseI_nine_ordinary_small_model_exclusion hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,hr,hz,ho,hq,hL,hSL,?_⟩
  rintro hc ⟨e⟩
  exact hn hc (Or.inl ⟨e⟩)

end CFSG.Quasithin.Chapter15.Section01
