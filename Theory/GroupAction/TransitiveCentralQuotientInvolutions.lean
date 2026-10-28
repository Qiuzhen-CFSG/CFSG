module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Involutions above a transitive central quotient

Squares are constant on cosets of a central elementary two-subgroup. If
automorphisms are transitive on the nonidentity cosets, one involution outside
the kernel therefore makes every element an involution. This proves that the
whole group is elementary abelian, without choosing coordinates for the
quotient action or assuming that the extension splits.

Source application: the original nonsolvable centralizer in
Aschbacher--Smith 13.2.8(1), printed p.880.
-/

/-- A transitive action on the nonidentity central cosets transports one
involutory lift to every coset. The displacement condition is the literal
quotient action, expressed without selecting quotient instances. -/
public theorem IsElementaryAbelian.of_transitive_central_quotient_involution
    {A Q : Type*} [Group A] [Group Q] [MulDistribMulAction A Q]
    (U : Subgroup Q) (hcentral : U ≤ Subgroup.center Q)
    (hexp : ∀ u ∈ U, u ^ 2 = 1)
    (htrans : ∀ x : Q, x ∉ U → ∀ y : Q, y ∉ U →
      ∃ a : A, (a • x) / y ∈ U)
    (hlift : ∃ x : Q, x ∉ U ∧ x ^ 2 = 1) :
    IsElementaryAbelian 2 Q := by
  obtain ⟨x,hx,hx2⟩ := hlift
  have hs (y : Q) : y ^ 2 = 1 := by
    by_cases hy : y ∈ U
    · exact hexp y hy
    obtain ⟨a,ha⟩ := htrans x hx y hy
    have hc : Commute ((a • x) / y) y :=
      (Subgroup.mem_center_iff.mp (hcentral ha) y).symm
    have hh := hc.mul_pow 2
    rw [div_mul_cancel,←smul_pow',hx2,smul_one,hexp _ ha,one_mul] at hh
    exact hh.symm
  have hi (y : Q) : y⁻¹ = y :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs y)
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro y z
  calc
    y * z = (y * z)⁻¹ := (hi _).symm
    _ = z * y := by rw [mul_inv_rev,hi,hi]
