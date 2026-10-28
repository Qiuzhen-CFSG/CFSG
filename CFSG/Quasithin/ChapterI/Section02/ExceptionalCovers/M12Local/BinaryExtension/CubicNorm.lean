module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.Quotient
public import Mathlib.Tactic.Group
/-!
# Cubic norm and the extra central-class involution

Conjugation by the marked cubic lift descends to the actual quotient R/⟨v₄⟩.
Its fixed subgroup is precisely the injected ambient center. In the elementary
branch the three-term norm is a homomorphism onto that center and provides a
specific complement, as well as a retraction on R itself.

The fusion mark for the extra involution supplies an involutory lift in the
actual centralizer. A lift there differs from a conjugate of u by a central
involution, so its square is one. Extending the core retraction to the whole
centralizer is a separate remaining step.

Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open Theory.LinearAlgebra.BinaryCubicOrbits
variable {K : Type*} [Group K] {u : K}
namespace MarkedSquareCoordinates
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12}
variable {m : Sporadic.Mathieu.M12SmallPair.CoverOrbitData}
variable (d : MarkedSquareCoordinates e u m)
include d

theorem noncentral : u ∉ center K := by
  intro h
  have he := d.quotient_mark
  rw [show QuotientGroup.mk' (center K) u = 1 from (QuotientGroup.eq_one_iff u).mpr h,
    map_one] at he
  have ho := Sporadic.Mathieu.M12SmallPair.z_order
  rw [← he, orderOf_one] at ho
  omega

/-- The actual central-class fusion supplies an involutory lift of the extra actor. -/
theorem exists_extra_lift (hZ : Nat.card (center K) = 2) (hu : orderOf u = 2) :
    ∃ w : centralizer ({u} : Set K), w ^ 2 = 1 ∧
      e (QuotientGroup.mk' (center K) (w : K)) = m.extra ∧
      (w : K) ∉ centralizerTwoResidual u := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨w, hw, hwm⟩ := show m.extra ∈ (centralizer ({u} : Set K)).map f from
    d.centralizer_image ▸ m.extra_mem
  obtain ⟨g,hg⟩ := isConj_iff.mp m.extra_fusion
  obtain ⟨g',hg'⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) g
  change e (QuotientGroup.mk' (center K) g') = g at hg'
  let v := g' * u * g'⁻¹
  have hv : f v = m.extra := by
    change e (QuotientGroup.mk' (center K) (g' * u * g'⁻¹)) = m.extra
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hg', d.quotient_mark]
    exact hg
  have hv2 : v ^ 2 = 1 := by
    have hu2 : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
    calc
      v ^ 2 = g' * u ^ 2 * g'⁻¹ := by dsimp [v]; simp only [pow_two]; group
      _ = 1 := by rw [hu2]; group
  have hd : w * v⁻¹ ∈ center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change f (w * v⁻¹) = e 1
    rw [map_mul, map_inv, hwm, hv, mul_inv_cancel, map_one]
  have hd2 : (w * v⁻¹) ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨w * v⁻¹, hd⟩ : center K))
    rw [hZ] at hp
    exact congrArg Subtype.val hp
  have hcomm : Commute (w * v⁻¹) v := (mem_center_iff.mp hd v).symm
  have hw2 : w ^ 2 = 1 := by
    have hs := hcomm.mul_pow 2
    simpa only [inv_mul_cancel_right, hd2, hv2, one_mul] using hs
  refine ⟨⟨w, hw⟩, Subtype.ext hw2, hwm, ?_⟩
  intro hx
  apply m.extra_not_mem
  rw [← d.residual_image]
  exact mem_map.mpr ⟨w, hx, hwm⟩

/-- The line removed from the core is also central in the full centralizer. -/
theorem root_square_commutes (c : centralizer ({u} : Set K)) :
    Commute ((d.root : K) ^ 2) (c : K) := by
  have hd : ((d.root : K) ^ 2)⁻¹ * u ∈ center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center K) (((d.root : K) ^ 2)⁻¹ * u) = 1
    rw [map_mul, map_inv, d.toSquareCoordinates.root_square_mark, inv_mul_cancel]
  have he : (d.root : K) ^ 2 = u * (((d.root : K) ^ 2)⁻¹ * u)⁻¹ := by group
  rw [he]
  exact (show Commute u (c : K) from
    (mem_centralizer_singleton_iff.mp c.property).symm).mul_left
    (show Commute (((d.root : K) ^ 2)⁻¹ * u) (c : K) from
      (mem_center_iff.mp hd c).symm).inv_left

theorem core_action_root_square : d.core_action (d.root ^ 2) = d.root ^ 2 := by
  apply Subtype.ext
  rw [d.core_action_apply]
  have hc := d.root_square_commutes
    ⟨d.cubic_lift, centralizerTwoResidual_le u d.cubic_lift.property⟩
  change (d.cubic_lift : K) * (d.root : K) ^ 2 * (d.cubic_lift : K)⁻¹ = _
  rw [hc.symm.eq, mul_inv_cancel_right]
  rfl

/-- Conjugation by the actual order-three lift descends to R/V₄. -/
noncomputable def quotientCubic : MulAut d.toSquareCoordinates.BinaryQuotient :=
  QuotientGroup.congr _ _ d.core_action (by
    change (zpowers (d.root ^ 2)).map d.core_action.toMonoidHom = zpowers (d.root ^ 2)
    rw [MonoidHom.map_zpowers]
    change zpowers (d.core_action (d.root ^ 2)) = _
    rw [d.core_action_root_square])

@[simp] theorem quotientCubic_mk (r : centralizerCore u) :
    d.quotientCubic (QuotientGroup.mk' d.toSquareCoordinates.squareLine r) =
      QuotientGroup.mk' d.toSquareCoordinates.squareLine (d.core_action r) := rfl

theorem quotientCubic_coordinates (r : d.toSquareCoordinates.BinaryQuotient) :
    (d.toSquareCoordinates.quotientCoordinates (d.quotientCubic r)).toAdd =
      cubic (d.toSquareCoordinates.quotientCoordinates r).toAdd := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective d.toSquareCoordinates.squareLine r
  exact d.cubic_equivariance r

theorem quotientCubic_center (z : center K) :
    d.quotientCubic (d.toSquareCoordinates.centerInjection z) =
      d.toSquareCoordinates.centerInjection z := by
  rw [SquareCoordinates.centerInjection_apply, d.quotientCubic_mk]
  congr 1
  apply Subtype.ext
  rw [d.core_action_apply]
  have hc := mem_center_iff.mp z.property (d.cubic_lift : K)
  change (d.cubic_lift : K) * (z : K) * (d.cubic_lift : K)⁻¹ = (z : K)
  rw [hc, mul_inv_cancel_right]

/-- Its fixed subgroup is exactly the image of the ambient center. -/
theorem quotientCubic_fixed_iff (r : d.toSquareCoordinates.BinaryQuotient) :
    d.quotientCubic r = r ↔ r ∈ d.toSquareCoordinates.quotientCenter := by
  constructor
  · intro hr
    rw [← d.toSquareCoordinates.quotientCoordinates_ker, MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    change (d.toSquareCoordinates.quotientCoordinates r).toAdd = 0
    apply (cubic_fixed_iff _).mp
    rw [← d.quotientCubic_coordinates, hr]
  · intro hr
    rw [← d.toSquareCoordinates.centerInjection_range] at hr
    obtain ⟨z, rfl⟩ := hr
    exact d.quotientCubic_center z

/-- The elementary-case norm uses the actual cubic conjugation action. -/
noncomputable def cubicNorm (hq : d.quadratic = 0) :
    d.toSquareCoordinates.BinaryQuotient →* d.toSquareCoordinates.BinaryQuotient := by
  let := d.toSquareCoordinates.quotient_elementary hq
  exact (MonoidHom.id _ * d.quotientCubic.toMonoidHom) *
    (d.quotientCubic.toMonoidHom.comp d.quotientCubic.toMonoidHom)

theorem cubicNorm_apply (hq : d.quadratic = 0)
    (r : d.toSquareCoordinates.BinaryQuotient) :
    d.cubicNorm hq r = r * d.quotientCubic r * d.quotientCubic (d.quotientCubic r) := rfl

theorem cubicNorm_mem (hq : d.quadratic = 0)
    (r : d.toSquareCoordinates.BinaryQuotient) :
    d.cubicNorm hq r ∈ d.toSquareCoordinates.quotientCenter := by
  rw [← d.toSquareCoordinates.quotientCoordinates_ker, MonoidHom.mem_ker]
  apply Multiplicative.toAdd.injective
  rw [d.cubicNorm_apply, d.toSquareCoordinates.quotientCoordinates.map_mul,
    d.toSquareCoordinates.quotientCoordinates.map_mul]
  change (d.toSquareCoordinates.quotientCoordinates r).toAdd +
    (d.toSquareCoordinates.quotientCoordinates (d.quotientCubic r)).toAdd +
    (d.toSquareCoordinates.quotientCoordinates (d.quotientCubic (d.quotientCubic r))).toAdd = 0
  rw [d.quotientCubic_coordinates, d.quotientCubic_coordinates, d.quotientCubic_coordinates]
  have hs : ∀ v : Space, v + cubic v + cubic (cubic v) = 0 := by decide +kernel
  exact hs _

theorem cubicNorm_retracts (hq : d.quadratic = 0) (z : center K) :
    d.cubicNorm hq (d.toSquareCoordinates.centerInjection z) =
      d.toSquareCoordinates.centerInjection z := by
  rw [d.cubicNorm_apply, d.quotientCubic_center, d.quotientCubic_center]
  have hs : (d.toSquareCoordinates.centerInjection z) ^ 2 = 1 :=
    (d.toSquareCoordinates.quotient_square_eq_one_iff _).mpr (by rw [hq]; rfl)
  rw [← pow_two, hs, one_mul]

/-- Identify the injected center with the literal quotient kernel. -/
noncomputable def quotientCenterEquiv :
    center K ≃* d.toSquareCoordinates.quotientCenter :=
  (MonoidHom.ofInjective (d.toSquareCoordinates.centerInjection_injective d.noncentral)).trans
    (MulEquiv.subgroupCongr d.toSquareCoordinates.centerInjection_range)

@[simp] theorem quotientCenterEquiv_apply (z : center K) :
    (d.quotientCenterEquiv z : d.toSquareCoordinates.BinaryQuotient) =
      d.toSquareCoordinates.centerInjection z := rfl

/-- The cubic norm is a retraction of the core quotient onto the actual ambient center. -/
noncomputable def quotientRetraction (hq : d.quadratic = 0) :
    d.toSquareCoordinates.BinaryQuotient →* center K :=
  d.quotientCenterEquiv.symm.toMonoidHom.comp
    ((d.cubicNorm hq).codRestrict d.toSquareCoordinates.quotientCenter (d.cubicNorm_mem hq))

theorem quotientRetraction_retracts (hq : d.quadratic = 0) (z : center K) :
    d.quotientRetraction hq (d.toSquareCoordinates.centerInjection z) = z := by
  apply d.quotientCenterEquiv.injective
  change d.quotientCenterEquiv (d.quotientCenterEquiv.symm _) = _
  rw [d.quotientCenterEquiv.apply_symm_apply]
  apply Subtype.ext
  exact d.cubicNorm_retracts hq z

/-- Pull the norm back along the source's actual core quotient map. -/
noncomputable def coreRetraction (hq : d.quadratic = 0) : centralizerCore u →* center K :=
  (d.quotientRetraction hq).comp (QuotientGroup.mk' d.toSquareCoordinates.squareLine)

theorem coreRetraction_retracts (hq : d.quadratic = 0) (z : center K) :
    d.coreRetraction hq ⟨z, d.ambient_center_le z.property⟩ = z :=
  d.quotientRetraction_retracts hq z

/-- The elementary quotient splits over the image of Z(K), with a specific norm kernel. -/
theorem quotientRetraction_complement (hq : d.quadratic = 0) :
    IsCompl (d.quotientRetraction hq).ker d.toSquareCoordinates.quotientCenter := by
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro r hr
    rw [← d.toSquareCoordinates.centerInjection_range] at hr
    obtain ⟨z, hz⟩ := hr.2
    have he : z = 1 := by
      rw [← d.quotientRetraction_retracts hq z, hz]
      exact hr.1
    rw [← hz, he, map_one]
    exact (⊥ : Subgroup d.toSquareCoordinates.BinaryQuotient).one_mem
  · apply codisjoint_iff.mpr
    apply top_unique
    intro r _
    let z := d.quotientRetraction hq r
    have hz : d.toSquareCoordinates.centerInjection z ∈ d.toSquareCoordinates.quotientCenter := by
      rw [← d.toSquareCoordinates.centerInjection_range]
      exact ⟨z,rfl⟩
    have hk : r * (d.toSquareCoordinates.centerInjection z)⁻¹ ∈
        (d.quotientRetraction hq).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, d.quotientRetraction_retracts]
      exact mul_inv_cancel _
    have hm := ((d.quotientRetraction hq).ker ⊔ d.toSquareCoordinates.quotientCenter).mul_mem
      (mem_sup_left hk) (mem_sup_right hz)
    simpa only [inv_mul_cancel_right] using hm

end MarkedSquareCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
