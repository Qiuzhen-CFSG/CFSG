module

public import Theory.GroupAction.Invariant
public import Theory.GroupAction.FourthPowerFixed

/-!
# Central displacement of an equivariant automorphism

If the orbit of an element generates a group, an automorphism commuting
with the action has central displacement everywhere as soon as it does on
that element. The displacement then defines a homomorphism to the center,
whose kernel is the fixed subgroup. Its index is at most the center order.

These elementary observations give the central-displacement obstruction
used in Thompson VI, printed p.630, to exclude involutions in the second
half of a residual involutory coset.
-/
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
/-- Central displacement propagates from an equivariant orbit generator. -/
public theorem central_displacement_of_commuting_orbit_generator
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (b : V) (hgen : closure (Set.range (fun a : A => a • b)) = ⊤)
    (e : MulAut V) (hcomm : ∀ a : A, ∀ x : V, e (a • x) = a • e x)
    (hb : e b / b ∈ center V) :
    ∀ x : V, e x / x ∈ center V := by
  let q := QuotientGroup.mk' (center V)
  have heq : q.comp e.toMonoidHom = q := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    rintro _ ⟨a, rfl⟩
    change q (e (a • b)) = q (a • b)
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [hcomm, ← smul_div']
    exact (isInvariant_of_characteristic (center V)).invariant a _ |>.mp hb
  intro x
  exact QuotientGroup.eq_iff_div_mem.mp (DFunLike.congr_fun heq x)

/-- A central-displacement automorphism has fixed-subgroup index at most the center order. -/
public theorem index_fixed_le_card_center_of_central_displacement
    {V : Type*} [Group V] [Finite V]
    (e : MulAut V) (hcentral : ∀ x : V, e x / x ∈ center V) :
    (FixedPoints.subgroup (zpowers e) V).index ≤ Nat.card (center V) := by
  let d : V →* center V := {
    toFun := fun x => ⟨e x / x, hcentral x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro x y
      apply Subtype.ext
      change e (x*y) / (x*y) = (e x / x) * (e y / y)
      rw [map_mul]
      have hc := mem_center_iff.mp (hcentral y) x⁻¹
      simp only [div_eq_mul_inv] at hc ⊢
      calc
        _ = e x * (e y * y⁻¹) * x⁻¹ := by group
        _ = (e x * x⁻¹) * (e y * y⁻¹) := by
          rw [mul_assoc, ← hc, ← mul_assoc] }
  have hk : d.ker = FixedPoints.subgroup (zpowers e) V := by
    ext x
    change (⟨e x / x, hcentral x⟩ : center V) = 1 ↔ _
    rw [Subtype.ext_iff]
    change e x / x = 1 ↔ _
    simp only [div_eq_mul_inv, mul_inv_eq_one]
    exact (MulAut.mem_fixed_zpowers_iff e x).symm
  rw [← hk, index_ker]
  exact (card_le_card_group d.range)
end Theory.GroupAction
