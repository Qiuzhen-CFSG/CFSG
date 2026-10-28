module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Nilpotent

/-!
# Squares modulo the center over an elementary second-center subgroup

If an elementary abelian two-subgroup D lies in Z₂(V), lifts of the same
V/D coset have the same square modulo Z(V). Indeed their ratio has order
at most two and becomes central modulo Z(V), so it does not affect the square.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674, the core-coset calculation used again before equation (4), p.678.
-/

namespace Subgroup

/-- Changing a lift by an elementary abelian subgroup of the second center
does not change its square modulo the center. -/
public theorem sq_eq_mod_center_of_eq_mod_elementary
    {V : Type*} [Group V] (D : Subgroup V) [D.Normal]
    [IsElementaryAbelian 2 D] (hD : D ≤ Subgroup.upperCentralSeries V 2)
    (a b : V) (hab : QuotientGroup.mk' D a = QuotientGroup.mk' D b) :
    QuotientGroup.mk' (center V) (a ^ 2) =
      QuotientGroup.mk' (center V) (b ^ 2) := by
  let p := QuotientGroup.mk' (center V)
  let d := a / b
  have hd : d ∈ D := QuotientGroup.eq_iff_div_mem.mp hab
  have hdc : p d ∈ center (V ⧸ center V) := by
    have hh := hD hd
    rw [← Subgroup.comap_upperCentralSeries_quotient_center 1, Subgroup.upperCentralSeries_one] at hh
    exact hh
  have hc : Commute (p d) (p b) := (mem_center_iff.mp hdc (p b)).symm
  have hd2 : d ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d hd
  have hsplit : a = d * b := by simp [d]
  change p (a ^ 2) = p (b ^ 2)
  rw [map_pow, hsplit, map_mul, hc.mul_pow, ← map_pow, hd2, map_one, one_mul, map_pow]

end Subgroup
