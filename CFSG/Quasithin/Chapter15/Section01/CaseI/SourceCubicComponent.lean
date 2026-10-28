module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceFixedPlaneMovement
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# The original component is the cubic residual

In the ordinary rank-two quotient rows of 15.1.22, the C-component is
O^{3′}(G₁). The local rank bound is obtained from the original marked
centralizer. Intersecting that residual with M identifies the actual
actor Y=O^{3′}(M ∩ G₁) with O^{3′}(M ∩ L), placing Y in L.
Together with the exchanged-plane calculation this supplies the source
15.1.25(1),(3) deductions for the same selected component.

Source: Aschbacher--Smith 15.1.25(1),(3), printed p.1102, using A.3.18.
The component quotient marking and earlier 15.1.14 remain source inputs.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- The rank-two quotient identifies the actual component and the residual
of its intersection with M. No normality of L is assumed. -/
theorem CaseIComponentData.source_cubic_component
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    [IsQuasisimple (d.L ⧸ pCore 2 d.L)]
    (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    d.L = (primeToResidual 3 d.G1).map d.G1.subtype ∧
      (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype =
        (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype := by
  let := h.elementary
  have hZp : IsPGroup 2 d.Z1 :=
    (IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left)
  have hrG : primeRank 3 d.G1 ≤ 2 :=
    (caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot hZp).stronglyQuasithin 3 Nat.prime_three (by decide)
  let K := d.L.subgroupOf d.G1
  let a : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let b : (K ⧸ pCore 2 K) ≃* (d.L ⧸ pCore 2 d.L) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  have hF := Facts.of_equiv b hf
  have he := d.L_isCComponent_in_G1.eq_primeToResidual_three_of_rank_outer_two
    hF.1 hF.2.1 hrG hF.2.2
  have hLres : d.L = (primeToResidual 3 d.G1).map d.G1.subtype := by
    have hh := congrArg (map d.G1.subtype) he
    rwa [map_subgroupOf_eq_of_le (show d.L ≤ d.G1 from d.L_component.1)] at hh
  refine ⟨hLres,?_⟩
  have hh := embedded_primeToResidual_intersection 3 d.G1 M
  rw [←hLres,inf_comm d.L M,inf_comm d.G1 M] at hh
  exact hh.symm

/-- Original 15.1.25(1),(3) for the same Nine component, keeping only its
model quotient facts and the earlier residual centralization explicit. -/
theorem PreparedChosenModule.source_caseI_nine_cubic_component
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
      let R := (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype
      let V1 := V ⊓ centralizer (R : Set G)
      let V2 := ⁅V,R⁆
      Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧ V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      d.Z1 ≤ V1 ∧ d.S.relIndex (T : Subgroup G) = 2 ∧
      (Facts (d.L ⧸ pCore 2 d.L) →
        d.L = (primeToResidual 3 d.G1).map d.G1.subtype ∧
        (primeToResidual 3 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype =
          (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ∧
        ¬ V1 ≤ centralizer (d.L : Set G)) := by
  obtain ⟨d,hr,hz,ho,hq,hL,hSL,hc1,hc2,hv,hi,hZ,hS,hm⟩ :=
    h.source_caseI_nine_fixed_plane_movement hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,hr,hz,ho,hq,hL,hSL,hc1,hc2,hv,hi,hZ,hS,?_⟩
  intro hf
  let := hq
  have hh := d.source_cubic_component hG h hf
  exact ⟨hh.1,hh.2,hm hf⟩
end CFSG.Quasithin.Chapter15.Section01
