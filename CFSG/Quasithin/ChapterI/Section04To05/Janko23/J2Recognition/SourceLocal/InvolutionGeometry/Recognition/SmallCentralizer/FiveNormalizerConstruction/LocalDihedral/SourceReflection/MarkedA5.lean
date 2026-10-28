module
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry

/-!
# A reflection for a marked subgroup of order five in A₅

The existing pentagon embedding gives a rotation of order five and an
involutive reflection that inverts it. Sylow conjugacy places any specified
subgroup of order five onto the rotation subgroup and transports the reflection
back, preserving its normalizer membership and its action on every element.

Source application: Aschbacher, *Sporadic Groups* (1994), 47.1, p.260.
-/

open Subgroup
open scoped Pointwise
namespace J2Reflection
open alternatingGroup.FiveLocalGeometry
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def rot : A5 := dihedralHom (.r 1)
private def refl : A5 := dihedralHom (.sr 0)
private theorem rot_order : orderOf rot = 5 := by
  rw [rot, orderOf_injective _ dihedralHom_injective, DihedralGroup.orderOf_r_one]
private theorem refl_order : orderOf refl = 2 := by
  rw [refl, orderOf_injective _ dihedralHom_injective, DihedralGroup.orderOf_sr]
private theorem refl_rot : refl * rot * refl⁻¹ = rot⁻¹ := by
  change dihedralHom (.sr 0) * dihedralHom (.r 1) * (dihedralHom (.sr 0))⁻¹ =
    (dihedralHom (.r 1))⁻¹
  simp only [← map_inv, ← map_mul]
  congr 1
private theorem refl_normalizes : refl ∈ normalizer (zpowers rot : Set A5) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (refl * rot * refl⁻¹) = _
  rw [refl_rot, zpowers_inv]
private theorem refl_inverts {p : A5} (hp : p ∈ zpowers rot) :
    refl * p * refl⁻¹ = p⁻¹ := by
  obtain ⟨k, rfl⟩ := hp
  change MulAut.conj refl (rot ^ k) = _
  rw [map_zpow]
  change (refl * rot * refl⁻¹) ^ k = _
  rw [refl_rot, inv_zpow]

public theorem exists_reflection {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 5) :
    ∃ t : H, t ∈ normalizer (P : Set H) ∧ orderOf t = 2 ∧
      ∀ p ∈ P, t * p * t⁻¹ = p⁻¹ := by
  let R := zpowers rot
  have hPe : Nat.card (P.map e.toMonoidHom) = 5 := by
    rw [card_map_of_injective e.injective, hP]
  have hR : Nat.card R = 5 := (Nat.card_zpowers rot).trans rot_order
  let S : Sylow 5 A5 := Sylow.ofCard (P.map e.toMonoidHom)
    (by rw [hPe, card]; decide +kernel)
  let T : Sylow 5 A5 := Sylow.ofCard R (by rw [hR, card]; decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 S T
  have hg' : (P.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = R :=
    congrArg (fun U : Sylow 5 A5 => (U : Subgroup A5)) hg
  let a : H ≃* A5 := e.trans (MulAut.conj g)
  have ha : P.map a.toMonoidHom = R := by
    rw [map_map] at hg'
    exact hg'
  have ht : a.symm refl ∈ normalizer (P : Set H) := by
    have hs := refl_normalizes
    rw [← show P.map a.toMonoidHom = zpowers rot from ha,
      ← map_equiv_normalizer_eq P a, mem_map_equiv] at hs
    exact hs
  refine ⟨a.symm refl, ht, (a.symm.orderOf_eq refl).trans refl_order, ?_⟩
  intro p hp
  apply a.injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  apply refl_inverts
  change a p ∈ R
  rw [← ha]
  exact mem_map_of_mem _ hp
end J2Reflection
