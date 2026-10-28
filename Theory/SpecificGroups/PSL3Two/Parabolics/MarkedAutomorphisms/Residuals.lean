module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Intrinsic residual and core identifications

The explicit point mark is normal with two-group quotient in its parabolic.
Each marked element is a product of elements of order dividing three, which
proves the reverse inclusion in the two-residual. Its translations form the
normal four-group, and every element of two-power order belongs to this group.
One fixed diagram automorphism transports all identifications to the line.

Source: Aschbacher–Smith 13.8.21(1), printed p.957.
-/

public section
namespace Matrix.PSL3Two.MarkedAutomorphisms
open Subgroup

/-- The embedded intrinsic two-residual of a parabolic. -/
@[expose] def residual (P : Subgroup SL) : Subgroup SL := (pResidual 2 P).map P.subtype

theorem point_residual : residual pointParabolicSL = pointA := by
  let N := pointA.subgroupOf pointParabolicSL
  have hn : N.Normal := by
    constructor
    intro a ha g
    exact pointA_conj g g.property a ha
  let := hn
  have hp : IsPGroup 2 (pointParabolicSL ⧸ N) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact parabolic_square g g.property
  apply le_antisymm
  · exact (map_mono (sInf_le ⟨hn, hp⟩ : pResidual 2 pointParabolicSL ≤ N)).trans_eq
      (map_subgroupOf_eq_of_le pointA_le)
  · have hcube (x : SL) (hx : x ∈ pointParabolicSL) (h3 : x ^ 3 = 1) :
        x ∈ residual pointParabolicSL := by
      let y : pointParabolicSL := ⟨x, hx⟩
      have hy3 : y ^ 3 = 1 := Subtype.ext h3
      exact ⟨y, mem_pResidual_of_orderOf_coprime
        (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hy3) (by decide)), rfl⟩
    intro x hx
    rcases cubic_factor x hx with h | h
    · exact hcube x (pointA_le hx) h
    · have hc := hcube cubic (pointA_le cubic_mem) cubic_cube
      have hd := hcube (cubic⁻¹ * x)
        (pointParabolicSL.mul_mem (pointParabolicSL.inv_mem (pointA_le cubic_mem))
          (pointA_le hx)) h
      simpa only [mul_inv_cancel_left] using (residual pointParabolicSL).mul_mem hc hd

theorem pointParabolic_map_diagram :
    pointParabolicSL.map diagram.toMonoidHom = lineParabolicSL := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (diagram_point_line x).mpr hx
  · intro hg
    refine ⟨diagram g, ?_, diagram_involutive g⟩
    apply (diagram_point_line (diagram g)).mp
    rwa [diagram_involutive]

theorem line_residual : residual lineParabolicSL = lineA := by
  have h := map_embedded_pResidual 2 pointParabolicSL diagram.toMonoidHom
  change (residual pointParabolicSL).map diagram.toMonoidHom =
    residual (pointParabolicSL.map diagram.toMonoidHom) at h
  rw [point_residual, pointParabolic_map_diagram, pointA_map_diagram] at h
  exact h.symm

/-- Two-power order, rather than trivial action on the whole component,
forces an element of the residual into its four-group. -/
theorem point_two_element (g : SL) (hg : g ∈ pointA)
    (hp : ∃ n : ℕ, g ^ (2 ^ n) = 1) : g ∈ pointV := by
  rcases pointA_order_test g hg with h | h
  · exact h
  · obtain ⟨n, hn⟩ := hp
    have ho : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 2 3).pow_left n)
      (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one h)
    rw [orderOf_eq_one_iff.mp ho]
    exact pointV.one_mem

theorem point_core : pointA.pCoreIn 2 = pointV := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := pointA) ⟨y, hy⟩
    apply point_two_element y y.property
    exact ⟨n, congrArg (fun z : pCore 2 pointA => (z : SL)) hn⟩
  · have hn : (pointV.subgroupOf pointA).Normal := by
      constructor
      intro a ha g
      exact pointV_conj g g.property a ha
    have hp : IsPGroup 2 (pointV.subgroupOf pointA) := by
      intro x
      exact ⟨1, Subtype.ext (Subtype.ext (pointV_square x x.property))⟩
    have hm := map_mono (f := pointA.subtype)
      (le_sSup ⟨hn, hp⟩ : pointV.subgroupOf pointA ≤ pCore 2 pointA)
    rwa [map_subgroupOf_eq_of_le pointV_le] at hm

theorem line_core : lineA.pCoreIn 2 = lineV := by
  have h := map_pCoreIn_of_injective 2 pointA diagram.toMonoidHom diagram.injective
  rw [point_core, pointV_map_diagram, pointA_map_diagram] at h
  exact h.symm

theorem card_point_residual : Nat.card (residual pointParabolicSL) = 12 := by
  rw [point_residual, card_pointA]

theorem card_line_residual : Nat.card (residual lineParabolicSL) = 12 := by
  rw [line_residual]
  let e := (diagram.subgroupMap pointA).trans
    (MulEquiv.subgroupCongr pointA_map_diagram)
  exact (Nat.card_congr e.toEquiv).symm.trans card_pointA

/-- The core quotient is genuinely cubic. -/
theorem card_point_core_quotient : Nat.card (pointA ⧸ pCore 2 pointA) = 3 := by
  have hc : Nat.card (pCore 2 pointA) = 4 := by
    have he := Nat.card_congr
      ((pCore 2 pointA).equivMapOfInjective pointA.subtype pointA.subtype_injective).toEquiv
    change Nat.card (pCore 2 pointA) = Nat.card (pointA.pCoreIn 2) at he
    rw [point_core, card_pointV] at he
    exact he
  have h := card_eq_card_quotient_mul_card_subgroup (pCore 2 pointA)
  rw [card_pointA, hc] at h
  omega

/-- The same cubic quotient for the compatible line mark. -/
theorem card_line_core_quotient : Nat.card (lineA ⧸ pCore 2 lineA) = 3 := by
  let e : pointA ≃* lineA :=
    (diagram.subgroupMap pointA).trans (MulEquiv.subgroupCongr pointA_map_diagram)
  let q := QuotientGroup.congr (pCore 2 pointA) (pCore 2 lineA) e (pCore_map_iso 2 e)
  exact (Nat.card_congr q.toEquiv).symm.trans card_point_core_quotient

end Matrix.PSL3Two.MarkedAutomorphisms
