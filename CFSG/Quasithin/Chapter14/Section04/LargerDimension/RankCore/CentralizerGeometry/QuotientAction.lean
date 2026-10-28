module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Hyperplane
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift

/-!
# Commutators on the literal central quotient

The coordinates in `SourceAction` carry an ambient commutator to the
corresponding vector displacement. Thus subgroup commutator bounds give
precisely the subspace bound consumed by the hyperplane rank obstruction.
Conversely, two-core elements act trivially and have central commutators.
For extraspecial U, commutator duality removes this central discrepancy
by an inner correction, proving Q = U C_H(U).

Source: Aschbacher--Smith, 14.4.7, printed pp.1008--1009. The action-kernel
input is 12.8.4(4); the extraspecial inner correction is supplied by the
source-independent `ExtraspecialSuitableLift` theorem.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
variable {H V : Type*} [Group H] {U : Subgroup H} [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem SourceAction.vector_mul (d : SourceAction H U V) (u v : U) :
    d.vector (u * v) = d.vector u + d.vector v := by
  simp [SourceAction.vector]

theorem SourceAction.vector_inv (d : SourceAction H U V) (u : U) :
    d.vector u⁻¹ = -d.vector u := by
  simp [SourceAction.vector]

theorem SourceAction.vector_eq_zero_iff (d : SourceAction H U V) (u : U) :
    d.vector u = 0 ↔ u ∈ center U := by
  change d.coordinates (QuotientGroup.mk' (center U) u) = 1 ↔ _
  rw [map_eq_one_iff d.coordinates d.coordinates.injective]
  exact QuotientGroup.eq_one_iff u

theorem SourceAction.vector_surjective (d : SourceAction H U V) :
    Function.Surjective d.vector := by
  intro v
  obtain ⟨q, hq⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center U) q
  exact ⟨u, congrArg Multiplicative.toAdd hq⟩

theorem SourceAction.displacement (d : SourceAction H U V) (a : H) (u : U) :
    (d.representation (QuotientGroup.mk' (pCore 2 H) a) - (LinearMap.id : V →ₗ[ZMod 2] V)) (d.vector u) =
      d.vector (MulAut.conjNormal a u * u⁻¹) := by
  rw [d.vector_mul, d.vector_inv, d.conjugation]
  change _ - d.vector u = _
  rw [sub_eq_add_neg]

theorem SourceAction.image_displacement_le (d : SourceAction H U V)
    (D W A : Subgroup H) (hcomm : ⁅D, W⁆ ≤ A) (a : H) (ha : a ∈ D) :
    (d.image W).map
      (d.representation (QuotientGroup.mk' (pCore 2 H) a) - (LinearMap.id : V →ₗ[ZMod 2] V)) ≤ d.image A := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro v ⟨u, hu, rfl⟩
  change (d.representation _ - (LinearMap.id : V →ₗ[ZMod 2] V)) (d.vector u) ∈ d.image A
  rw [d.displacement]
  apply d.vector_mem_image
  exact hcomm (commutator_mem_commutator ha hu)

theorem SourceAction.core_fixes (d : SourceAction H U V) (a : H) (ha : a ∈ pCore 2 H)
    (u : U) : d.vector (MulAut.conjNormal a u) = d.vector u := by
  rw [d.conjugation, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff a).mpr ha, map_one]
  rfl

theorem SourceAction.centralizer_le_core (d : SourceAction H U V) :
    centralizer (U : Set H) ≤ pCore 2 H := by
  intro a ha
  apply (QuotientGroup.eq_one_iff a).mp
  apply d.faithful
  ext v
  obtain ⟨u, rfl⟩ := d.vector_surjective v
  change d.representation (QuotientGroup.mk' (pCore 2 H) a) (d.vector u) =
    d.representation 1 (d.vector u)
  rw [← d.conjugation, map_one]
  have hu : MulAut.conjNormal a u = u := by
    apply Subtype.ext
    change a * (u : H) * a⁻¹ = u
    rw [← ha u u.property, mul_inv_cancel_right]
  rw [hu]
  rfl

theorem SourceAction.commutator_le_center (d : SourceAction H U V)
    (D : Subgroup H) (hD : D ≤ pCore 2 H) :
    ⁅D, U⁆ ≤ (center U).map U.subtype := by
  apply commutator_le.mpr
  intro a ha u hu
  let c : U := MulAut.conjNormal a ⟨u, hu⟩ * (⟨u, hu⟩ : U)⁻¹
  have hc : c ∈ center U := by
    apply (d.vector_eq_zero_iff c).mp
    rw [d.vector_mul, d.vector_inv, d.core_fixes a (hD ha), add_neg_cancel]
  exact ⟨c, hc, rfl⟩

variable [Finite H] [IsExtraspecial 2 U]
theorem SourceAction.core_eq_sup_centralizer (d : SourceAction H U V)
    (hZ : ∀ (a : H) (z : U), z ∈ center U → MulAut.conjNormal a z = z) :
    pCore 2 H = U ⊔ centralizer (U : Set H) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
      (⊤ : Subgroup U) le_top (MulAut.conjNormal a) (hZ a) (by
        intro u _
        apply (d.vector_eq_zero_iff _).mp
        rw [d.vector_mul, d.vector_inv, d.core_fixes a ha, add_neg_cancel])
    have hc : a * (r : H) ∈ centralizer (U : Set H) := by
      intro u hu
      have hh := congrArg Subtype.val (hr ⟨u, hu⟩ (mem_top _))
      change a * ((r : H) * u * (r : H)⁻¹) * a⁻¹ = u at hh
      have he : (a * (r : H)) * u * (a * (r : H))⁻¹ = u := by
        simpa only [mul_inv_rev, mul_assoc] using hh
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he : a = (a * (r : H)) * (r : H)⁻¹ := by group
    rw [he]
    exact (U ⊔ centralizer (U : Set H)).mul_mem (mem_sup_right hc)
      (mem_sup_left (U.inv_mem r.property))
  · exact sup_le (le_sSup ⟨inferInstance, IsExtraspecial.isPGroup 2 U⟩)
      d.centralizer_le_core
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
