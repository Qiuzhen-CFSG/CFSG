module

public import Theory.FieldTheory.QuadraticUnitAction
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Quadratic actions on complements of a field-unit quotient

Suppose a group maps onto the units of a field of characteristic two, and an
endomorphism induces a field automorphism on this quotient. A preserved
complement of the kernel maps onto the full unit group. Quadratic action on
the complement therefore kills the field automorphism, and disjointness from
the kernel kills every displacement in the original complement.

Application: the literal Borel quotients in Aschbacher–Smith F.1.3(5), p.260.
-/

public section
namespace MonoidHom
open Subgroup

theorem fixes_of_quadratic_field_quotient {G F : Type*} [Group G] [Field F]
    [CharP F 2] (q : G →* Fˣ) (hq : Function.Surjective q)
    (D : Subgroup G) (hd : Disjoint q.ker D) (hs : q.ker ⊔ D = ⊤)
    (a : G →* G) (σ : F ≃+* F)
    (ha : ∀ x, q (a x) = Units.map σ.toMonoidHom (q x))
    (hD : ∀ x ∈ D, a x ∈ D)
    (hquad : ∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) :
    ∀ x ∈ D, a x = x := by
  have hmap : D.map q = ⊤ := by
    have he := congrArg (Subgroup.map q) hs
    simpa only [Subgroup.map_sup, map_ker_self, bot_sup_eq,
      Subgroup.map_top_of_surjective q hq] using he
  have hσ : σ = 1 := by
    apply σ.eq_one_of_quadratic_units
    intro u
    obtain ⟨x, hx, rfl⟩ := hmap ▸ (show u ∈ (⊤ : Subgroup Fˣ) from trivial)
    have he := congrArg q (hquad x hx)
    simpa only [ha, map_mul, map_inv] using he
  intro x hx
  apply mul_inv_eq_one.mp
  apply disjoint_iff_inf_le.mp hd
  refine ⟨?_, D.mul_mem (hD x hx) (D.inv_mem hx)⟩
  change q (a x * x⁻¹) = 1
  rw [map_mul, map_inv, ha, hσ]
  change q x * (q x)⁻¹ = 1
  exact mul_inv_cancel _

/-- Ambient-subgroup form, keeping the given complement and endomorphism. -/
theorem fixes_complement_of_quadratic_field_quotient
    {G F : Type*} [Group G] [Field F] [CharP F 2]
    (U B D : Subgroup G) (hUB : U ≤ B) (hDB : D ≤ B)
    (hd : Disjoint U D) (hs : U ⊔ D = B)
    (q : B →* Fˣ) (hq : Function.Surjective q)
    (hker : q.ker = U.subgroupOf B)
    (a : G →* G) (b : B →* B) (hb : ∀ x : B, (b x : G) = a x)
    (σ : F ≃+* F) (ha : ∀ x, q (b x) = Units.map σ.toMonoidHom (q x))
    (hD : ∀ x ∈ D, a x ∈ D)
    (hquad : ∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) :
    ∀ x ∈ D, a x = x := by
  have hd' : Disjoint q.ker (D.subgroupOf B) := by
    rw [hker]
    exact disjoint_iff_inf_le.mpr (fun x hx =>
      Subtype.ext (disjoint_iff_inf_le.mp hd hx))
  have hs' : q.ker ⊔ D.subgroupOf B = ⊤ := by
    rw [hker, ← subgroupOf_sup hUB hDB, hs, subgroupOf_self]
  have hf := fixes_of_quadratic_field_quotient q hq (D.subgroupOf B) hd' hs'
    b σ ha (fun x hx => by change (b x : G) ∈ D; rw [hb]; exact hD x hx)
    (fun x hx => Subtype.ext (by
      simpa only [hb, Subgroup.coe_mul, Subgroup.coe_inv] using hquad x hx))
  intro x hx
  simpa only [hb] using congrArg Subtype.val (hf ⟨x, hDB hx⟩ hx)

end MonoidHom
