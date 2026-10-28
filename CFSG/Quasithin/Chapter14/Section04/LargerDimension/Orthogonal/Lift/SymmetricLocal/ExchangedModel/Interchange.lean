module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.MovedSection
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.Cubic
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Preserving
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.PrimePowerDecomposition

/-!
# The cubic obstruction to a factor-preserving exchanged involution

The literal residual map has two-group kernel, so every cubic matrix actor
has an actual cubic lift in the original K₀. A fixed-point-free actor on
Uˣ/Z(Uˣ) fixes at most two elements of Uˣ. The joint-core intersection bound
instead gives at least four whenever it fixes sixteen elements of D.

This excludes the preserving alternative of the finite normalizer theorem
and proves interchange of the actual matrix-factor images. The original
cubic bound is an explicit premise of swaps_of_original_cubic_bound;
OriginalCubic proves it from OriginalMovedAction, and Assembly discharges it.
Elementary structure of D is proved from the exchanged moved section, so
neither it nor the source interchange is taken as a symmetry certificate.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

namespace CaseThreeAction
variable {H U : Subgroup G} (m : CaseThreeAction H U)

/-- A fixed-point-free matrix actor fixes at most the central involution in U. -/
theorem fixed_card_le_two [Finite G] [IsExtraspecial 2 U]
    (h : H) (hf : ∀ v : Binary.V, m.action h v = v → v = 0) :
    Nat.card (U ⊓ centralizer ({(h:G)}:Set G) : Subgroup G) ≤ 2 := by
  have hle : U ⊓ centralizer ({(h:G)}:Set G) ≤ (center U).map U.subtype := by
    intro u hu
    let v : U := ⟨u,hu.1⟩
    have he : U.normalizerMonoidHom ⟨h,m.normalizes h.property⟩ v = v := by
      apply Subtype.ext
      change (h:G)*u*(h:G)⁻¹=u
      rw [← mem_centralizer_singleton_iff.mp hu.2, mul_inv_cancel_right]
    have hz : (m.projection v).toAdd = 0 := by
      apply hf
      have hh := m.projection_equivariant h v
      rw [he] at hh
      exact (congrArg Multiplicative.toAdd hh).symm
    have hv : v ∈ center U := by
      apply (QuotientGroup.eq_one_iff v).mp
      apply m.coordinates.injective
      change m.projection v = m.coordinates 1
      rw [map_one]
      exact hz
    exact ⟨v,hv,rfl⟩
  have hb := card_le_of_le hle
  rw [← Nat.card_congr ((center U).equivMapOfInjective U.subtype U.subtype_injective).toEquiv,
    IsExtraspecial.center_order_p 2 U] at hb
  exact hb
end CaseThreeAction

/-- Taking the odd part gives a cubic lift through a two-group kernel. -/
private theorem cubic_lift {P Q : Type*} [Group P] [Finite P] [Group Q]
    (f : P →* Q) (hk : IsPGroup 2 f.ker) (r : Q)
    (hrange : r ∈ f.range) (hr : orderOf r = 3) :
    ∃ c : P, orderOf c = 3 ∧ f c = r := by
  obtain ⟨a,ha⟩ := hrange
  obtain ⟨u,v,⟨n,hu⟩,hv,_,huv,humem,_⟩ :=
    exists_prime_power_decomposition 2 Nat.prime_two a
  have hur : f u ∈ zpowers r := by
    rw [← ha, ← MonoidHom.map_zpowers]
    exact mem_map_of_mem f humem
  have hfu : f u = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 3 (2^n) from (by decide : Nat.Coprime 3 2).pow_right n)
    · simpa only [hr] using orderOf_dvd_of_mem_zpowers hur
    · apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow,hu,map_one]
  have hfv : f v = r := by
    have hh := congrArg f huv
    rw [map_mul,hfu,one_mul,ha] at hh
    exact hh
  exact ⟨v,(f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk v hv).symm.trans
    (hfv ▸ hr),hfv⟩

/-- Elementary structure of D also follows from the exchanged moved section. -/
theorem common_lift_elementary [Finite G]
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2) (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z}:Set G)).pCoreIn 2 = U) (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z}:Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z}:Set G) ⊓ centralizer ({conjugateElement z x}:Set G)).pCoreIn 2 =
      centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x}:Set G)) (conjugateCore U x))
    (d : OriginalMovedAction U z (conjugateElement z x)) :
    IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)) := by
  let V := conjugateCore U x
  let i := conjugateElement z x
  let K := diagonalResidual (centralizer ({z}:Set G)) i
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective
  let _ : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hzH : z ∈ centralizer ({i}:Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
  have hKC : K ≤ centralizer ({z}:Set G) ⊓ centralizer ({i}:Set G) := map_subtype_le _
  have hi : orderOf i = 2 := by simpa only [i,conjugateElement,MulEquiv.orderOf_eq] using hz
  obtain ⟨hm,hirr⟩ := exchanged_moved_section U z x hz hZ hUcore hUcard hiz hDcard hDcore m d.nonsolvable
  have heq := (symmetric_lift_of_marked_actions U z x hz hZ hUcore hUcard hiz hDcard hDcore m d).1
  rw [← heq]
  exact (centralizerLift_elementary_and_card V K i z hi hz (conjugateCore_center U z x hZ)
    (m.normalizes hzH) hzH (exchanged_involution_not_mem_core U z x hUcore hUcard hDcard hDcore)
    ((hKC.trans inf_le_right).trans m.normalizes) (hKC.trans inf_le_left) hm hirr).1

/-- The precise remaining source assembly: original cubic fixed points rule
out the factor-preserving alternative for the actual exchanged actor. -/
theorem swaps_of_original_cubic_bound [Finite G]
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2) (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z}:Set G)).pCoreIn 2 = U) (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z}:Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z}:Set G) ⊓ centralizer ({conjugateElement z x}:Set G)).pCoreIn 2 =
      centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x}:Set G)) (conjugateCore U x))
    (d : OriginalMovedAction U z (conjugateElement z x))
    (hfix : ∀ k : diagonalResidual (centralizer ({z}:Set G)) (conjugateElement z x),
      orderOf k = 3 → 16 ≤ Nat.card
        (centralizerLift U z (conjugateElement z x) ⊓ centralizer ({(k:G)}:Set G) : Subgroup G)) :
    Binary.InvolutionResidual.SwapsFactors (m.action
      ⟨z,mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm⟩) := by
  let V := conjugateCore U x
  let i := conjugateElement z x
  let C := centralizer ({z}:Set G) ⊓ centralizer ({i}:Set G)
  let K := diagonalResidual (centralizer ({z}:Set G)) i
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective
  let _ : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hzH : z ∈ centralizer ({i}:Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
  let a : centralizer ({i}:Set G) := ⟨z,hzH⟩
  let f := m.residualMap C inf_le_right
  let R := f.range
  let t := m.action a
  have hn : ¬ Group.IsSolvable (pResidual 2 C) := by
    intro hs
    let _ := hs
    let er := (pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective
    exact d.nonsolvable (Group.isSolvable_of_surjective (f := er.toMonoidHom) er.surjective)
  have ht : t ^ 2 = 1 := by
    have ha2 : a^2=1 := Subtype.ext (hz ▸ pow_orderOf_eq_one z)
    change (m.action a)^2=1
    rw [← map_pow,ha2,map_one]
  have hne : t ≠ 1 := by
    intro he
    have hm := (exchanged_moved_section U z x hz hZ hUcore hUcard hiz hDcard hDcore m d.nonsolvable).1
    have hc := m.subspace_card
      (((⁅V,zpowers z⁆).subgroupOf V).map (QuotientGroup.mk' (center V)))
    change m.action a = 1 at he
    rw [m.subspace_moved a hz, he] at hc
    simp only [show (1 : Binary.V ≃ₗ[ZMod 2] Binary.V).toLinearMap = LinearMap.id from rfl,
      sub_self, LinearMap.range_zero, Nat.card_unique] at hc
    have hh : (1 : ℕ) = 16 := hc.trans hm
    norm_num at hh
  have hcomm : ∀ r : R, Commute t (Binary.linearAction (r:Binary.G)) := by
    intro r
    obtain ⟨c,hc⟩ := r.property
    have hh : Commute a (inclusion (show C ≤ centralizer ({i}:Set G) from inf_le_right) (c:C)) := by
      apply Subtype.ext
      exact (mem_centralizer_singleton_iff.mp c.val.property.1).symm
    change Commute (m.action a) (Binary.linearAction r.val)
    rw [← hc,m.residualMap_spec]
    exact hh.map m.action
  rcases Binary.InvolutionResidual.swapsFactors_or_exists_cubic t (m.action_normalizes a) ht hne
      R (m.residualMap_nonsolvable C inf_le_right hn) hcomm with hswap | ⟨r,hr,hfree⟩
  · exact hswap
  obtain ⟨c,hc3,hcr⟩ := cubic_lift f (m.residualMap_kernel_isPGroup C inf_le_right)
    r.val r.property (by simpa only [Subgroup.orderOf_coe] using hr)
  let k : K := ⟨(c:C),mem_map_of_mem C.subtype c.property⟩
  have hk3 : orderOf k = 3 := by
    have he : orderOf k = orderOf c := by
      rw [← Subgroup.orderOf_coe k, ← Subgroup.orderOf_coe c, ← Subgroup.orderOf_coe (c:C)]
    exact he.trans hc3
  have hlarge := four_le_exchanged_actor_centralizer_card U z x hz hUcore hUcard hiz
    (common_lift_elementary U z x hz hZ hUcore hUcard hiz hDcard hDcore m d)
    hDcard hDcore (k:G) (hfix k hk3)
  have hsmall := m.fixed_card_le_two
    (inclusion (show C ≤ centralizer ({i}:Set G) from inf_le_right) (c:C)) (by
      intro v hv
      apply hfree v
      have he : Binary.linearAction (r:Binary.G) =
          m.action (inclusion (show C ≤ centralizer ({i}:Set G) from inf_le_right) (c:C)) := by
        rw [← hcr]
        exact m.residualMap_spec C inf_le_right c
      change Binary.linearAction (r:Binary.G) v = v
      rw [he]
      exact hv)
  change Nat.card (conjugateCore U x ⊓ centralizer ({(k:G)}:Set G) : Subgroup G) ≤ 2 at hsmall
  omega

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
