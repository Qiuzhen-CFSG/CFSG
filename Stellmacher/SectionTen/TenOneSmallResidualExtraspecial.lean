module
public import Stellmacher.SectionTen.TenOneSmallResidualQuaternionProduct
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexModelSetup
public import Theory.ElementaryAbelian.Extraspecial

/-!
# The extraspecial residual core in the small branch

The actual small, SL2(2) branch of Section Ten has an extraspecial first
residual two-core of order thirty-two. This is exactly the residual-core
clause in Stellmacher (10.1)(a2), Journal of Algebra 190 (1997), printed p.59.

The proved quaternion central-product model gives the order. Its already
identified center is the first central line of order two, and the derived
subgroup lies in this center and in the elementary module V. The elementary
central-commutator theorem makes every square central, so the central quotient
is elementary abelian. Counting gives quotient order sixteen and hence its
nontriviality, completing all fields of the extraspecial predicate.
-/
namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_extraspecial
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    IsExtraspecial 2 (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) ∧
      Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) = 2^5 := by
  let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  let Z := ZAt ctx.Γ ctx.criticalPath.firstStep
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hRcard : Nat.card R = 32 := SectionEight.eight_six_quaternion_quaternion_card
    (ten_one_small_residual_quaternion_product ctx middle hpath hsmall hmodel)
  have hcenter : CenterAmbient R = Z := ten_one_small_residual_center ctx middle hpath hsmall hmodel
  have hderived : ⁅R,R⁆ ≤ Z := ten_one_small_residual_commutator_le_center ctx middle hpath hsmall hmodel
  have hline : ⁅V,R⁆ = Z := ten_one_small_module_core_commutator ctx middle hpath hsmall hmodel
  obtain ⟨hN,_,_⟩ := ten_one_small_residual_quotient_elementary ctx middle hpath hsmall hmodel
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
  let W := R ⧸ Subgroup.center R
  let _ : IsMulCommutative W :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (hderivedNative.trans inf_le_right)
  have helementary : IsElementaryAbelian 2 W := ⟨by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center R) x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.square_mem_center_of_elementary_central_commutator D hD hderivedNative r)⟩
  have hWcard : Nat.card W = 16 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
    rw [hRcard,hcenterCard] at hh
    change 32 = Nat.card W * 2 at hh
    omega
  have hnontrivial : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; decide)
  exact ⟨⟨hcenterCard,helementary,hnontrivial⟩,hRcard⟩
end Stellmacher.SectionTen

