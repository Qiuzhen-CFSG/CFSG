module
public import Theory.GroupTheory.Commutator.ElementaryIndexTwoQuadratic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quadratic action on an elementary quotient through index two

Let T normalize V and Z, with Z normal in V and V/Z elementary abelian
at the prime two. If a subgroup Q of index two in T centralizes V modulo
Z, then the double commutator [[V,T],T] is contained in Z. The group and
its subgroups may be infinite; Z need not be central in V or in T.

Work in the normalizer of Z and quotient by its normal subgroup Z. The
literal image of V is a homomorphic image of V/Z and is therefore elementary
abelian. The Q image centralizes it and has index dividing two in the T
image. Index one gives trivial action; index two invokes the established
elementary index-two quadratic theorem. The quotient kernel then pulls the
vanishing double commutator back to the exact ambient containment.

This is the source-neutral quotient step used from assertion (11) to (12)
in Stellmacher (8.6), Journal of Algebra 190 (1997), printed p.43. Its local
group and geometric hypotheses are supplied by the Section Eight consumer.
-/

open scoped commutatorElement IsMulCommutative
namespace Subgroup

public theorem commutator_commutator_le_of_elementary_quotient_index_two
    {G : Type*} [Group G] (V Z Q T : Subgroup G)
    (hZV : Z ≤ V) (hTV : T ≤ normalizer (V : Set G))
    (hTZ : T ≤ normalizer (Z : Set G))
    (hN : (Z.subgroupOf V).Normal)
    (helementary : let _ := hN; IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
    (hQT : Q ≤ T) (hindex : Q.relIndex T = 2) (hVQ : ⁅V,Q⁆ ≤ Z) :
    ⁅⁅V,T⁆,T⁆ ≤ Z := by
  let _ := hN
  let _ : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V) := helementary
  let K := normalizer (Z : Set G)
  let ZK := Z.subgroupOf K
  let _ : ZK.Normal := inferInstance
  let π : K →* K ⧸ ZK := QuotientGroup.mk' ZK
  have hVK : V ≤ K := (normal_subgroupOf_iff_le_normalizer hZV).mp hN
  have hQK : Q ≤ K := hQT.trans hTZ
  let VK := V.subgroupOf K
  let QK := Q.subgroupOf K
  let TK := T.subgroupOf K
  let Vbar := VK.map π
  let Qbar := QK.map π
  let Tbar := TK.map π
  have hπker : π.ker = ZK := QuotientGroup.ker_mk' _
  let inclusion := Subgroup.inclusion hVK
  let φ : (V ⧸ Z.subgroupOf V) →* K ⧸ ZK :=
    QuotientGroup.map (Z.subgroupOf V) ZK inclusion (fun _ hx => hx)
  have hφimage : (⊤ : Subgroup (V ⧸ Z.subgroupOf V)).map φ = Vbar := by
    apply le_antisymm
    · rintro _ ⟨point, _, rfl⟩
      obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) point
      exact mem_map_of_mem π lift.property
    · rintro _ ⟨point, hpoint, rfl⟩
      exact ⟨QuotientGroup.mk' (Z.subgroupOf V) ⟨point, hpoint⟩, mem_top _, rfl⟩
  let _ : IsElementaryAbelian 2 (⊤ : Subgroup (V ⧸ Z.subgroupOf V)) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ Z.subgroupOf V)) point) }
  let _ : IsElementaryAbelian 2 Vbar := hφimage ▸ IsElementaryAbelian.map φ
  have hTnormal : Tbar ≤ normalizer (Vbar : Set (K ⧸ ZK)) := by
    apply le_normalizer_iff.mpr
    rintro actor ⟨actorK, hactor, rfl⟩ point ⟨pointK, hpoint, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    apply mem_map_of_mem
    exact (mem_normalizer_iff.mp (hTV hactor) pointK).mp hpoint
  have hQcentral : Qbar ≤ centralizer (Vbar : Set (K ⧸ ZK)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (map_eq_bot_iff _).mpr
    rw [hπker]
    intro point hpoint
    apply hVQ
    have hm := mem_map_of_mem K.subtype hpoint
    rw [map_commutator, map_subgroupOf_eq_of_le hVK,
      map_subgroupOf_eq_of_le hQK] at hm
    exact hm
  have hidx : Qbar.relIndex Tbar ∣ 2 := by
    have hh := relIndex_dvd_of_le_left TK (le_comap_map π QK)
    rw [relIndex_comap, relIndex_subgroupOf hTZ, hindex] at hh
    exact hh
  have hdouble : ⁅⁅Vbar,Tbar⁆,Tbar⁆ = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with hone | htwo
    · have hcentral := (relIndex_eq_one.mp hone).trans hQcentral
      rw [commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mpr hcentral), commutator_bot_left]
    · exact commutator_commutator_eq_bot_of_centralizing_index_two
        Vbar Qbar Tbar hTnormal (map_mono (fun _ hx => hQT hx)) hQcentral htwo
  have hbound : ⁅⁅VK,TK⁆,TK⁆ ≤ ZK := by
    rw [← hπker, ← map_eq_bot_iff, map_commutator, map_commutator]
    exact hdouble
  have hm := map_mono (f := K.subtype) hbound
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hVK,
    map_subgroupOf_eq_of_le hTZ, map_subgroupOf_eq_of_le Z.le_normalizer] at hm
  exact hm

end Subgroup
