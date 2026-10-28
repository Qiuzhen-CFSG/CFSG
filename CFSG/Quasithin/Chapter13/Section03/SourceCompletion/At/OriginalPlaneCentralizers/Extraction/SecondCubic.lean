module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.SecondCubic
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.LocalControl

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Extraction.SecondCubic`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]


private theorem second_cubic_derived : secondCubic ∈ commutator (Atlas.G2.Model K) := by
  have he : cubicCommutator.val = secondCubic := by
    apply rho_injective
    apply LinearMap.ext
    intro v
    rw [cubicCommutator_action, secondCubic_action]
  exact he ▸ cubicCommutator.property

omit [Finite G] in
theorem MarkedPlane.chart_injective (d : MarkedPlane V) : Function.Injective d.chart := by
  intro a b hab
  apply automizerRepresentation_injective V
  apply LinearMap.ext
  intro v
  apply d.coordinates.injective
  rw [d.equivariant, d.equivariant, hab]

theorem Context.component_action_ker (s : Context T L V) (d : MarkedPlane V) :
    (d.chart.comp (V.normalizerMonoidHom.rangeRestrict.comp
      (inclusion s.chosen.normalizes))).ker = pCore 2 L := by
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived := Atlas.G2.isSimple_commutator_binary
  rw [← s.chosen.centralizer_eq_core_of_simple s.quotient.isSimpleGroup]
  ext x
  change d.chart (V.normalizerMonoidHom.rangeRestrict (inclusion s.chosen.normalizes x)) = 1 ↔ _
  rw [← map_one d.chart, d.chart_injective.eq_iff]
  rw [← Subtype.coe_inj]
  change (V.normalizerMonoidHom (inclusion s.chosen.normalizes x) : MulAut V) = 1 ↔ _
  change inclusion s.chosen.normalizes x ∈ V.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

theorem Context.second_cubic_order_three (s : Context T L V) (d : MarkedPlane V) :
    ∃ n : normalizer (V : Set G), n.val ∈ L ∧ orderOf n.val = 3 ∧
      d.chart (V.normalizerMonoidHom.rangeRestrict n) = secondCubic := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect s.maximal.1
  have hd : secondCubic ∈ (inducedAutomizer V L).map d.chart :=
    (component_actor_image s.chosen.normalizes s.actor d.chart d.coordinates d.equivariant).symm ▸
      second_cubic_derived
  obtain ⟨a, ⟨n, hnL, rfl⟩, hn⟩ := hd
  let f : L →* Atlas.G2.Model K := d.chart.comp
    (V.normalizerMonoidHom.rangeRestrict.comp (inclusion s.chosen.normalizes))
  let x : L := ⟨n.val, hnL⟩
  have hx : f x = secondCubic := hn
  obtain ⟨r, _, hodd, hr⟩ := f.exists_odd_power_with_image x (by rw [hx, orderOf_secondCubic]; decide)
  have hr' : f r = secondCubic := hr.trans hx
  have hpow : r ^ 3 ∈ pCore 2 L := by
    rw [← s.component_action_ker d]
    change f (r^3) = 1
    rw [map_pow, hr', ← orderOf_secondCubic, pow_orderOf_eq_one]
  have hpowone : r ^ 3 = 1 := by
    by_contra hne
    have hdvd := (pCore_isPGroup (p := 2) (G := L)).dvd_orderOf
      (g := ⟨r ^ 3, hpow⟩) (fun h => hne (congrArg Subtype.val h))
    have hdvd' : 2 ∣ orderOf (r ^ 3) := by
      simpa only [← Subgroup.orderOf_coe] using hdvd
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (hdvd'.trans (orderOf_dvd_of_mem_zpowers ((zpowers r).pow_mem (mem_zpowers r) 3))))
  have hord : orderOf r = 3 := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpowone)
    (by simpa only [hr', orderOf_secondCubic] using orderOf_map_dvd f r)
  refine ⟨⟨r.val, s.chosen.normalizes r.property⟩, r.property, ?_, hr'⟩
  simpa only [Subgroup.orderOf_coe] using hord

private theorem secondCubic_plane_iff (v : W) : rho secondCubic v ∈ plane ↔ v ∈ plane := by
  rw [secondCubic_action, mem_plane, mem_plane]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  constructor
  · rintro ⟨h3,h4,h13,h24⟩
    exact ⟨by simpa [h3] using h13, by simpa [h4] using h24, h3, h4⟩
  · rintro ⟨h1,h2,h3,h4⟩
    simp [h1,h2,h3,h4]

omit [Finite G] in
theorem second_cubic_normalizes_plane (d : MarkedPlane V)
    (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = secondCubic) :
    n.val ∈ normalizer (d.A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let v : Additive V := Additive.ofMul ⟨x,d.le_module hx⟩
    have hv : d.coordinates v ∈ plane := d.plane_space ▸
      (mem_pointCoordinateSubspace d.coordinates d.A v).mpr hx
    apply (mem_pointCoordinateSubspace d.coordinates d.A
      (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v)).mp
    rw [d.plane_space, d.equivariant, hn, secondCubic_plane_iff]
    exact hv
  · intro hx
    have hxV : x ∈ V := (mem_normalizer_iff.mp n.property x).mpr (d.le_module hx)
    let v : Additive V := Additive.ofMul ⟨x,hxV⟩
    have hv : d.coordinates (automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict n) v) ∈ plane := d.plane_space ▸
      (mem_pointCoordinateSubspace d.coordinates d.A _).mpr hx
    rw [d.equivariant, hn, secondCubic_plane_iff] at hv
    exact (mem_pointCoordinateSubspace d.coordinates d.A v).mp (d.plane_space.symm ▸ hv)

omit [Finite G] in
theorem second_cubic_not_centralizes_plane (d : MarkedPlane V)
    (n : normalizer (V : Set G))
    (hn : d.chart (V.normalizerMonoidHom.rangeRestrict n) = secondCubic) :
    n.val ∉ centralizer (d.A : Set G) := by
  intro hc
  let v := d.coordinates.symm firstVector
  have hv : v.toMul.val ∈ d.A :=
    (mem_pointCoordinateSubspace d.coordinates d.A v).mp (by
      rw [d.plane_space, LinearEquiv.apply_symm_apply, mem_plane]
      decide)
  have hf : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change n.val * v.toMul.val * n.val⁻¹ = v.toMul.val
    rw [← hc _ hv, mul_inv_cancel_right]
  have he := d.equivariant (V.normalizerMonoidHom.rangeRestrict n) v
  rw [hf, hn] at he
  dsimp only [v] at he
  rw [LinearEquiv.apply_symm_apply] at he
  have h0 := congrFun he 0
  rw [secondCubic_action] at h0
  exact one_ne_zero (show (1:K)=0 from h0)

theorem Context.plane_cubic_escape (s : Context T L V) (d : MarkedPlane V) :
    ∃ n : normalizer (d.A : Set G), orderOf n = 3 ∧
      n.val ∈ L ∧ n.val ∉ centralizer (d.A : Set G) := by
  obtain ⟨n,hnL,ho,hn⟩ := s.second_cubic_order_three d
  refine ⟨⟨n.val,second_cubic_normalizes_plane d n hn⟩,?_,hnL,
    second_cubic_not_centralizes_plane d n hn⟩
  simpa only [←Subgroup.orderOf_coe] using ho

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
