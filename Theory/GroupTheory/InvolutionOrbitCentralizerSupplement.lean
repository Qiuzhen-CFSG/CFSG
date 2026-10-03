module

public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Centralizer supplements from involution conjugacy

If all involutions in a coset of a normal subgroup are conjugate under that
subgroup, an abelian quotient is covered by the involution centralizer.
Correct any lift by the core conjugator relating its conjugate involution
to the original one. This is the Frattini argument for the involution orbit.
-/

open Subgroup
namespace Subgroup
variable {P : Type*} [Group P]

/-- Core transitivity on the involution coset makes its centralizer cover the quotient. -/
public theorem centralizer_quotient_surjective_of_involution_orbit
    (H : Subgroup P) [H.Normal] [IsMulCommutative (P ⧸ H)]
    (t : P) (ht : t ^ 2 = 1)
    (horbit : ∀ v : P, v ^ 2 = 1 → v * t⁻¹ ∈ H →
      ∃ p : H, (p : P) * t * (p : P)⁻¹ = v) :
    Function.Surjective ((QuotientGroup.mk' H).comp
      (centralizer ({t} : Set P)).subtype) := by
  let q := QuotientGroup.mk' H
  intro y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective H y
  have hv : (s * t * s⁻¹) ^ 2 = 1 := by
    calc
      _ = s * t ^ 2 * s⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [ht]; group
  have hcoset : (s * t * s⁻¹) * t⁻¹ ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((s * t * s⁻¹) * t⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      (IsMulCommutative.is_comm (M := P ⧸ H)).comm (q s) (q t)]
    group
  obtain ⟨p, hp⟩ := horbit _ hv hcoset
  have hc : (p : P)⁻¹ * s ∈ centralizer ({t} : Set P) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun a : P => (p : P)⁻¹ * a * s) hp
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh.symm
  refine ⟨⟨(p : P)⁻¹ * s, hc⟩, ?_⟩
  change q ((p : P)⁻¹ * s) = q s
  have hpq : q p = 1 := (QuotientGroup.eq_one_iff _).mpr p.property
  rw [map_mul, map_inv, hpq, inv_one, one_mul]

/-- The involution centralizer supplements the normal subgroup. -/
public theorem centralizer_sup_eq_top_of_involution_orbit
    (H : Subgroup P) [H.Normal] [IsMulCommutative (P ⧸ H)]
    (t : P) (ht : t ^ 2 = 1)
    (horbit : ∀ v : P, v ^ 2 = 1 → v * t⁻¹ ∈ H →
      ∃ p : H, (p : P) * t * (p : P)⁻¹ = v) :
    centralizer ({t} : Set P) ⊔ H = ⊤ := by
  let q := QuotientGroup.mk' H
  have hs := centralizer_quotient_surjective_of_involution_orbit H t ht horbit
  have hm : (centralizer ({t} : Set P)).map q = ⊤ := by
    have hh := MonoidHom.range_eq_top.mpr hs
    rwa [MonoidHom.range_comp, range_subtype] at hh
  have hh := congrArg (Subgroup.comap q) hm
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
end Subgroup
