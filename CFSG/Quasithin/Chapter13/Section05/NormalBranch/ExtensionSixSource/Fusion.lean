module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource.Geometry
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit.TwoCentralizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
/-!
# Marked involution fusion in the original quaternion core

The natural A₆ action fuses every two nonidentity elements of V under the
original L. The actual F.9 action kernel bounds C_H(U_H) by O₂(H), while
the source S₃ × S₃ quotient supplies an order-nine actor. The intrinsic
quaternion-product orbit theorem therefore fuses all noncentral involutions
of U_H. A nonidentity vector in V₊ outside V₁ connects that orbit to the
original marked involution z, so every involution of U_H lies in z^G.

This is the first two fusion steps in the S₆ extension argument; the
remaining placement of L-involutions in U_H belongs to LocalPlacement.
All maps, modules, and subgroups retain the original source coordinates.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
  (b : Conclusions D M 6 g)

include d in
/-- L fuses the nonidentity elements of the original natural module. -/
theorem module_nonidentity_conjugate (x y : G) (hx : x ∈ D.V) (hy : y ∈ D.V)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ l ∈ D.L, l*x*l⁻¹ = y := by
  let xx : D.V := ⟨x,hx⟩
  let yy : D.V := ⟨y,hy⟩
  have hx0 : (d.coordinate xx).toAdd ≠ 0 := by
    intro hh
    have he : d.coordinate xx = 1 := Multiplicative.toAdd.injective hh
    exact hx1 (congrArg Subtype.val ((map_eq_one_iff d.coordinate d.coordinate.injective).mp he))
  have hy0 : (d.coordinate yy).toAdd ≠ 0 := by
    intro hh
    have he : d.coordinate yy = 1 := Multiplicative.toAdd.injective hh
    exact hy1 (congrArg Subtype.val ((map_eq_one_iff d.coordinate d.coordinate.injective).mp he))
  obtain ⟨a,ha⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
    (d.coordinate xx).toAdd (d.coordinate yy).toAdd hx0 hy0
  obtain ⟨l,hl⟩ := SourceSixBlock.actor_surjective d a
  refine ⟨l,l.property,?_⟩
  have he := d.conjugation l xx
  change _ = BinaryPermutation.naturalRepresentation (Fin 6) (SourceSixBlock.actor d l).val _ at he
  rw [hl,ha] at he
  exact congrArg Subtype.val (d.coordinate.injective (Multiplicative.toAdd.injective he))

include d h e hseed hn hU b
/-- The actual H action fuses the noncentral involutions of U_H. -/
theorem noncentral_core_involutions_conjugate (x y : G) (hx : x ∈ D.UH) (hy : y ∈ D.UH)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxZ : x ∉ D.V₁) (hyZ : y ∉ D.V₁) :
    IsConj x y := by
  let U := D.UH.subgroupOf D.H
  let : U.Normal := h.UH_normal
  let a : U ≃* D.UH := subgroupOfEquivOfLe h.UH_le_H
  let q := (SourceOrthogonal.quaternion d h e hseed hn hU).map a.symm
  have hcent : centralizer (U : Set D.H) ≤ pCore 2 D.H := by
    intro v hv
    have hvQ : (v:G) ∈ D.QH := by
      rw [←h.kernel_UH_eq_QH]
      apply (h.mem_kernel_iff h.UH_le_H).mpr
      refine ⟨v.property,fun u hu=>?_⟩
      have hc := congrArg Subtype.val (hv (⟨u,h.UH_le_H hu⟩ : D.H) hu)
      have he : ⁅u,(v:G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hc
      rw [he]
      exact D.V₁.one_mem
    exact (show D.QH.subgroupOf D.H = pCore 2 D.H from
      comap_map_eq_self_of_injective D.H.subtype_injective _) ▸ hvQ
  have htwo : IsPGroup 2 (centralizer (U : Set D.H)) := pCore_isPGroup.to_le hcent
  have hstar : Nat.card (Section08.Source.Hstar D.H) = 36 := by
    rw [Nat.card_congr (b.nine rfl).1.some.toEquiv]
    simp only [OmegaPlusFour,S3,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  have hdiv : 3^2 ∣ Nat.card D.H := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D.H),hstar]
    exact dvd_mul_of_dvd_left (by norm_num) _
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n:=2) hdiv
  let xx : U := ⟨⟨x,h.UH_le_H hx⟩,hx⟩
  let yy : U := ⟨⟨y,h.UH_le_H hy⟩,hy⟩
  have hnz (u : U) (hu : (u:G) ∉ D.V₁) : u ∉ center U := by
    intro hc
    apply hu
    rw [←SourceOrthogonal.center_map d h e hseed hn hU]
    exact mem_map_of_mem D.UH.subtype ((centerCongr a ⟨u,hc⟩).property)
  have ho (u : U) : orderOf u = orderOf (u:G) := by
    exact (orderOf_injective (D.H.subtype.comp U.subtype)
      (D.H.subtype_injective.comp U.subtype_injective) u).symm
  have hc := isConj_noncentral_involutions_of_order_nine_of_two_centralizer U htwo q A hA
    xx yy ((ho xx).trans hx2) (hnz xx hxZ) ((ho yy).trans hy2) (hnz yy hyZ)
  exact D.H.subtype.map_isConj hc

/-- Every involution of the original quaternion core belongs to the marked class. -/
theorem core_involutions_fused (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (x : G) (hx : x ∈ D.UH) (hx2 : orderOf x = 2) : IsConj z x := by
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx2
  by_cases hxZ : x ∈ D.V₁
  · obtain ⟨w,hw,hu⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
    have hz' := hu ⟨z,hz⟩ (fun he => hz1 (congrArg Subtype.val he))
    have hx' := hu ⟨x,hxZ⟩ (fun he => hx1 (congrArg Subtype.val he))
    have he : z = x := congrArg Subtype.val (hz'.trans hx'.symm)
    rw [←he]
  obtain ⟨v,hv,hvZ⟩ := SetLike.exists_of_lt h.point_lt
  have hv1 : v ≠ 1 := fun he => hvZ (he.symm ▸ D.V₁.one_mem)
  have hvV : v ∈ D.V := h.plus_le hv
  have hv2 : orderOf v = 2 := by
    let := h.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hvV) hv1
  obtain ⟨l,hl,hconj⟩ := module_nonidentity_conjugate d z v
    (h.plus_le (h.point_lt.le hz)) hvV hz1 hv1
  exact (isConj_iff.mpr ⟨l,hconj⟩).trans
    (noncentral_core_involutions_conjugate d h e hseed hn hU b v x
      (le_conjugateSpanBy D.Vplus D.H hv) hx hv2 hx2 hvZ hxZ)
end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ExtensionSixSource
