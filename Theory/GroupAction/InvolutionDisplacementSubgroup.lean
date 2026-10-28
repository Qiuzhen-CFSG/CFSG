module

public import Theory.GroupAction.FourthPowerFixed
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Recognizing a subgroup as involution displacement

Let an involution act on a finite elementary binary group. A subgroup
containing every displacement and having the displacement order is fixed
pointwise. Rank-nullity determines the order of the displacement homomorphism;
quadraticity puts its image in the fixed subgroup.
-/

namespace MulAut
open Subgroup
open scoped IsMulCommutative

/-- A subgroup containing all displacements, with the rank-nullity order,
is fixed by the involution. The identity automorphism is allowed. -/
public theorem subgroup_le_fixed_of_displacement_le
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (a : MulAut V) (ha : a ^ 2 = 1) (A : Subgroup V)
    (hcard : Nat.card V = Nat.card A * Nat.card (FixedPoints.subgroup (zpowers a) V))
    (hdisp : ∀ v : V, v⁻¹ * a v ∈ A) :
    A ≤ FixedPoints.subgroup (zpowers a) V := by
  let δ : V →* V := {
    toFun := fun v => v⁻¹ * a v
    map_one' := by simp
    map_mul' := by
      intro v w
      simp only [mul_inv_rev, map_mul]
      ac_rfl }
  have hker : δ.ker = FixedPoints.subgroup (zpowers a) V := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixed_zpowers_iff]
    change v⁻¹ * a v = 1 ↔ a v = v
    rw [inv_mul_eq_one, eq_comm]
  have hrange : δ.range ≤ A := by
    rintro v ⟨w, rfl⟩
    exact hdisp w
  have hrangeCard : Nat.card δ.range = Nat.card A := by
    have hc := δ.ker.card_mul_index
    rw [index_ker, hker, hcard] at hc
    have hpos : 0 < Nat.card (FixedPoints.subgroup (zpowers a) V) := Nat.card_pos
    nlinarith
  have hquadratic : δ.range ≤ FixedPoints.subgroup (zpowers a) V := by
    rintro v ⟨w, rfl⟩
    apply (mem_fixed_zpowers_iff a _).mpr
    have haa : a (a w) = w := by
      have hh := congrArg (fun b : MulAut V => b w) ha
      exact hh
    have hi (v : V) : v⁻¹ = v := by
      apply inv_eq_of_mul_eq_one_left
      have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) v
      simpa only [pow_two] using hh
    change a (w⁻¹ * a w) = w⁻¹ * a w
    rw [map_mul, map_inv, haa, hi, hi, mul_comm]
  exact (eq_of_le_of_card_ge hrange hrangeCard.ge).symm.le.trans hquadratic

end MulAut
