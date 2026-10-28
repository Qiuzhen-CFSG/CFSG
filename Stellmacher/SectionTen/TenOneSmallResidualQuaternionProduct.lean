module
public import Stellmacher.SectionTen.TenOneSmallResidualCenter
public import Stellmacher.SectionEight.GeneratedEightSixNextCoreEightReduction
public import Theory.GroupTheory.CentralCommutatorEightSupplement

/-!
# The small residual quaternion central product

In the order-eight, SL2(2) branch of Section Ten, the first residual two-core
is a central product of two quaternion groups of order eight. This is the
specific structure obtained in the proof of Stellmacher (10.1)(a), Journal
of Algebra 190 (1997), printed p.60.

The actual core has order thirty-two, a normal elementary subgroup V of
order eight, and center Z of order two containing the derived subgroup.
The central-commutator supplement theorem constructs a second elementary
eight generating the core with V. The proved elementary-pair recognition
then gives commuting quaternion factors, and the existing ambient transport
supplies the campaign's central-product predicate. No extraspecial or
central-product recognition hypothesis is assumed.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_quaternion_product
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    IsCentralProductQ8Q8 (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) := by
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hRcard : Nat.card R = 32 := ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
  have hcenter : CenterAmbient R = Z := ten_one_small_residual_center ctx middle hpath hsmall hmodel
  have hderived : ⁅R,R⁆ ≤ Z := ten_one_small_residual_commutator_le_center ctx middle hpath hsmall hmodel
  have hline : ⁅V,R⁆ = Z := ten_one_small_module_core_commutator ctx middle hpath hsmall hmodel
  obtain ⟨hN,_,_⟩ := ten_one_small_residual_quotient_elementary ctx middle hpath hsmall hmodel
  let _ := hN
  have hZV : Z ≤ V := by
    rw [← hline]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hVR).mp hN)
  have hZnative : Subgroup.center R = Z.subgroupOf R := by
    rw [← hcenter]
    exact (Subgroup.comap_map_eq_self_of_injective R.subtype_injective _).symm
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_commutator_and_kernel ctx.toAmbientSectionNineContext hb
      ctx.criticalPath.firstStep ⟨1,ctx.Γ.act_one _⟩).1
  have hcenterCard : Nat.card (Subgroup.center R) = 2 := by
    rw [← Subgroup.card_map_of_injective R.subtype_injective]
    change Nat.card (CenterAmbient R) = 2
    rwa [hcenter]
  let D := V.subgroupOf R
  have hcenterD : Subgroup.center R ≤ D := by
    rw [hZnative]
    exact fun _ hx => hZV hx
  have hderivedNative : commutator R ≤ D ⊓ Subgroup.center R := by
    intro x hx
    have hxZ : (x : G) ∈ Z := hderived (by
      rw [← Subgroup.map_subtype_commutator R]
      exact Subgroup.mem_map_of_mem R.subtype hx)
    refine ⟨hZV hxZ,?_⟩
    rwa [hZnative]
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
      ctx.commutator_eq).longer_case hb).1
  have hD : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hVR
  have hDcard : Nat.card D = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVR).toEquiv]
    exact hsmall
  obtain ⟨C,hC,hCcard,hjoin,_⟩ :=
    Subgroup.exists_elementary_eight_supplement_of_central_commutator D hD hDcard hRcard
      hderivedNative (by rw [inf_eq_right.mpr hcenterD]; exact hcenterCard)
  exact SectionEight.eight_six_quaternion_product_of_native_elementary_eights R C D
    hC hD hCcard hDcard hjoin hN hcenterCard
end Stellmacher.SectionTen

