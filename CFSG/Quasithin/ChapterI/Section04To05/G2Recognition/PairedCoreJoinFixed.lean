module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreJoin
public import Theory.GroupTheory.PGroup.ExtraspecialCubicCentralInvolution

/-!
# Cubic fixed points in the actual extraspecial join

The order-243 join J is normal in the full normalizer of the original
Sylow P. An involution normalizing P and centralizing K = Z(J) has
abelian fixed group in J, since its ambient centralizer has three-part
nine. The class-two fixed-center lemma therefore gives C_J(v) = K.
Every cubic element of P centralizing v then fixes at least 27 elements
of J: fixed points on the elementary quotient J/K lift through its
central inversion, and a cubic action on that order-81 quotient has at
least nine fixed points.

The final theorem supplies v from the actual marked torus, so no new
involution or fixed-point hypothesis is imposed on the source. These
are deductions from Aschbacher–Smith I.4(G1)–(G2), printed p.417. The
remaining diagonal transport and Sylow-nine exclusion are separate from
these fixed-point conclusions. Chapter14PairedCoreJoin gives the literal
SourceLocalData application.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

theorem paired_cores_join_fixed (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (v : G) (hv : orderOf v=2)
    (hvN : v∈normalizer (t.commonLineCore:Set G))
    (hvK : v∈Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)) :
    let J := cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    J ⊓ Subgroup.centralizer ({v}:Set G)=K ∧
      ∀ a : G, a∈t.commonLineCore → orderOf a=3 → Commute v a →
        27≤Nat.card (J ⊓ Subgroup.centralizer ({a}:Set G) : Subgroup G) := by
  let J := cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  let P := t.commonLineCore
  have hJP : J≤P := sup_le (t.left_oddCore_le_commonLineCore hc) (t.right_oddCore_le_commonLineCore hc)
  have hPN : P≤normalizer (J:Set G) := (t.paired_cores_join_card_normal hc).2
  have hvJ : v∈normalizer (J:Set G) := t.paired_cores_join_normalizer hc hvN
  let α := J.normalizerMonoidHom ⟨v,hvJ⟩
  have hα : Function.Involutive α := by
    intro u
    have hh : (⟨v,hvJ⟩:normalizer (J:Set G))^2=1 := Subtype.ext
      (by change v^2=1; simpa only [hv] using pow_orderOf_eq_one v)
    have he : α^2=1 := by change (J.normalizerMonoidHom _)^2=1; rw [←map_pow,hh,map_one]
    exact congrArg (fun f : MulAut J => f u) he
  have hZ : (center J).map J.subtype=K := by
    rw [←centerIn_eq_map_center]
    exact (t.paired_cores_join_center_derived hc).2.1
  have hαZ (u : J) (hu : u∈center J) : α u=u := by
    apply Subtype.ext
    change v*(u:G)*v⁻¹=(u:G)
    have huK : (u:G)∈K := hZ ▸ mem_map_of_mem J.subtype hu
    rw [←hvK u huK,mul_inv_cancel_right]
  have hαcomm : IsMulCommutative α.fixedSubgroup := by
    let F := P ⊓ Subgroup.centralizer ({v}:Set G)
    let : IsMulCommutative F := t.commonLineCore_involution_fixed_commutative v hv
    let e := J.normalizerFixedEquiv ⟨v,hvJ⟩
    refine ⟨⟨fun x y => ?_⟩⟩
    apply e.injective
    rw [map_mul,map_mul]
    apply Subtype.ext
    have hF (u : α.fixedSubgroup) : ((e u):G)∈F := ⟨hJP (e u).property.1,(e u).property.2⟩
    exact congrArg (fun u : F => (u:G)) (mul_comm' (⟨e x,hF x⟩:F) ⟨e y,hF y⟩)
  let : IsExtraspecial 3 J := t.paired_cores_join_extraspecial hc
  let : IsElementaryAbelian 3 (J ⧸ center J) := IsExtraspecial.quotient_elementary_abelian 3 J
  have hclass : _root_.commutator J≤center J := Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hJ := (t.paired_cores_join_card_normal hc).1
  have hfix : α.fixedSubgroup=center J := α.fixed_eq_center_of_abelian_fixed hα
    (by rw [hJ]; decide) hclass hαZ hαcomm
  have hambient : α.fixedSubgroup.map J.subtype=J ⊓ Subgroup.centralizer ({v}:Set G) := by
    ext u
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      have hh := congrArg (fun u : J => (u:G)) ((MulAut.mem_fixedSubgroup α w).mp hw)
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hu
      refine ⟨⟨u,hu.1⟩,?_,rfl⟩
      apply (MulAut.mem_fixedSubgroup α _).mpr
      apply Subtype.ext
      change v*u*v⁻¹=u
      rw [←mem_centralizer_singleton_iff.mp hu.2,mul_inv_cancel_right]
  refine ⟨hambient.symm.trans (by rw [hfix,hZ]),?_⟩
  intro a ha ha3 hva
  let β := J.normalizerMonoidHom ⟨a,hPN ha⟩
  have hβ3 : β^3=1 := by
    have hh : (⟨a,hPN ha⟩:normalizer (J:Set G))^3=1 := Subtype.ext
      (by change a^3=1; simpa only [ha3] using pow_orderOf_eq_one a)
    change (J.normalizerMonoidHom _)^3=1
    rw [←map_pow,hh,map_one]
  have hαβ : α*β=β*α := by
    change J.normalizerMonoidHom _ * J.normalizerMonoidHom _ = _
    rw [←map_mul,←map_mul]
    congr 1
    exact Subtype.ext hva.eq
  have hβZ (u : J) (hu : u∈center J) : β u=u := by
    apply Subtype.ext
    change a*(u:G)*a⁻¹=(u:G)
    have huK : (u:G)∈K := hZ ▸ mem_map_of_mem J.subtype hu
    have huC := (t.commonLineCore_centralizer hc).ge huK
    rw [huC a ha,mul_inv_cancel_right]
  have hh := MulAut.cubic_fixed_card_ge_twentySeven_of_central_involution hJ α β
    hα hβ3 hαβ hαZ hβZ hαcomm
  rwa [Nat.card_congr (J.normalizerFixedEquiv ⟨a,hPN ha⟩).toEquiv] at hh

/-- The original torus supplies the involution required by the fixed-point bound. -/
theorem exists_paired_cores_join_fixed (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let J := cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    ∃ v : G, v∈t.torus.map c.H.subtype ∧ orderOf v=2 ∧
      J ⊓ Subgroup.centralizer ({v}:Set G)=K ∧
      ∀ a : G, a∈t.commonLineCore → orderOf a=3 → Commute v a →
        27≤Nat.card (J ⊓ Subgroup.centralizer ({a}:Set G) : Subgroup G) := by
  obtain ⟨v,hvT,hv,hvK⟩ := t.core_intersection_centralizing_involution hc
  have hvN : v∈normalizer (t.commonLineCore:Set G) := by
    rw [t.commonLineCore_normalizer hc]
    exact t.torus_normalizes_core_intersection hvT
  exact ⟨v,hvT,hv,t.paired_cores_join_fixed hc v hv hvN hvK⟩

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
