module
public import Stellmacher.SectionEight.EightSixCostFourModuleCenter
public import Stellmacher.SectionEight.GeneratedEightSixNextCoreEightReduction
public import Theory.GroupTheory.CentralCommutatorEightSupplement

/-!
# The quaternion-product module in the cost-four branch

In the selected length-two configuration of (8.6), a minimal actor of
commutator cost four makes the next module V a central product of two
quaternion groups. Its selected orbit subgroup U, the E-closure of the
initial center, is self-centralizing in V. Both conclusions concern the
actual graph subgroups and keep the selected geometric witnesses.

The selected orbit is elementary abelian of order eight, contains the next
central line Z, and lies in V. Since [V,V]≤[V,Qnext]=Z, it is normal in V.
The preceding module-center theorem identifies Z with the full center of V;
module saturation and the residual cardinality theorem give |V|=32.
After restriction to the native group V, the central-commutator theorem
identifies the centralizer of U and produces an elementary-eight supplement.
The two elementary eights then yield the existing quaternion-product
recognition hypotheses. The intrinsic centralizer equality transports back
to V∩C_G(U)=U.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (8.6)(b2) and
the normalizer argument in (b3), printed p.44. No equality of V with the
next two-core or quaternion-model premise is assumed.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
open scoped commutatorElement
universe u
public theorem eight_six_cost_four_module_quaternion
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hcost : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 4)
    : IsCentralProductQ8Q8 (VAt ctx.Γ ctx.criticalPath.firstStep) ∧
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        Subgroup.centralizer (conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E : Set G) =
          conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let U := conjugateClosure (ZAt Γ cp.a) E
  have hUV : U ≤ V := eight_six_conjugate_closure_le _ _ _
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
    (geom.group_le.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hseed : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hZline := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hZU : Z ≤ U := hZline.2.trans hseed
  have hUcard : Nat.card U = 8 := eight_six_selected_orbit_card_eight
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
  have hUelem : IsElementaryAbelian 2 U := eight_six_selected_orbit_elementary ctx E hcore
  have hVR : V ≤ QAt Γ cp.firstStep := SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hVV : ⁅V,V⁆ ≤ Z := (Subgroup.commutator_mono le_rfl hVR).trans_eq data.first_commutator
  have hnormalizer : V ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hUV le_rfl).trans (hVV.trans hZU))
  let N := U.subgroupOf V
  have hNnormal : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormalizer
  let _ := hNnormal
  let _ := hUelem
  have hNelem : IsElementaryAbelian 2 N := IsElementaryAbelian.subgroupOf hUV
  have hNcard : Nat.card N = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv).trans hUcard
  have hcenterV : CenterAmbient V = Z := eight_six_cost_four_module_center
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL
      ha hout hlarge hmin hQ hcost
  have hmap : (N ⊓ Subgroup.center V).map V.subtype = Z := by
    rw [Subgroup.map_inf _ _ _ V.subtype_injective]
    change (U.subgroupOf V).map V.subtype ⊓ CenterAmbient V = Z
    rw [Subgroup.map_subgroupOf_eq_of_le hUV,hcenterV,inf_eq_right.mpr hZU]
  have hderived : _root_.commutator V ≤ N ⊓ Subgroup.center V := by
    apply (Subgroup.map_le_map_iff_of_injective V.subtype_injective).mp
    rw [Subgroup.map_subtype_commutator,hmap]
    exact hVV
  have hfixed : Nat.card (N ⊓ Subgroup.center V : Subgroup V) = 2 := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective,hmap]
    exact hZline.1
  obtain ⟨hWnormal,hW,action,hformula,hkernel,hgenerate⟩ :=
    eight_six_next_quotient_module_data_local ctx hcenter hlength hcard data.first_commutator
  let _ := hWnormal
  have hmodule := eight_six_cost_four_full_module_card ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ hcost
      hWnormal hW action hformula hkernel hgenerate
  have hVcard : Nat.card V = 32 := by
    change Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 32
    rw [hmodule.2]
    exact (eight_six_cost_four_residual_card ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL
        ha hout hlarge hmin hQ hcost).1
  obtain ⟨hcentralizer,_⟩ :=
    Subgroup.centralizer_eq_and_center_card_two_of_central_commutator N hNelem hNcard
      hVcard hderived hfixed
  obtain ⟨other,hother,hotherCard,hjoin,hcenterCard⟩ :=
    Subgroup.exists_elementary_eight_supplement_of_central_commutator N hNelem hNcard
      hVcard hderived hfixed
  refine ⟨eight_six_quaternion_product_of_native_elementary_eights V other N hother hNelem
    hotherCard hNcard hjoin hNnormal hcenterCard,?_⟩
  apply le_antisymm
  · intro v hv
    have hvn : (⟨v,hv.1⟩ : V) ∈ Subgroup.centralizer (N : Set V) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro n hn
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hv.2 n hn
    rw [hcentralizer] at hvn
    exact hvn
  · exact le_inf hUV (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative U))
end Stellmacher.SectionEight
