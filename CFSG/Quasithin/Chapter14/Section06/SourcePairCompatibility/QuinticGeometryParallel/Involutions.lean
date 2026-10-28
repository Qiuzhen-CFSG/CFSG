module
public import Theory.GroupTheory.DihedralPairNormalizer

/-!
# Preserving involutions of a quintic factor pair

The outer D10 rotation exponents two and three cannot be induced by an
element of square one: squaring conjugation would give exponents four and
nine on an element of order five. Hence preserving involutions act innerly
on each factor. Self-centralization then absorbs them into the factor join.

Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032; this supplies
the no-index correction needed before applying the rank-eight argument.
The actual ratio-action application is in `QuinticGeometryParallel.Source`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G]

private theorem rotation_action_square
    (g r : G) (hg : g ^ 2 = 1) (n : ℕ)
    (hr : g * r * g⁻¹ = r ^ n) : r = r ^ (n*n) := by
  have hleft : g * (g * r * g⁻¹) * g⁻¹ = r := by
    calc
      g * (g * r * g⁻¹) * g⁻¹ = g^2 * r * (g^2)⁻¹ := by simp only [pow_two]; group
      _ = r := by rw [hg]; simp
  calc
    r = (MulAut.conj g) ((MulAut.conj g) r) := hleft.symm
    _ = (MulAut.conj g) (r^n) := congrArg (MulAut.conj g) hr
    _ = r^(n*n) := by rw [map_pow]; change (g*r*g⁻¹)^n = _; rw [hr,←pow_mul]

/-- A preserving element of square one acts innerly on a marked D10 factor.
The outer rotation exponents two and three have order four modulo five. -/
theorem quintic_involution_inner (A : Subgroup G) (e : A ≃* DihedralGroup 5)
    (g : G) (hg : g ∈ normalizer (A : Set G)) (hg2 : g ^ 2 = 1) :
    ∃ a : A, ∀ x : A, g * x * g⁻¹ = (a : G) * x * (a : G)⁻¹ := by
  by_contra ho
  have hor := outer_on_dihedral_five_rotation A e g hg ho
  let r : G := e.symm (DihedralGroup.r 1)
  have hr : orderOf r = 5 := by
    rw [show orderOf r = orderOf (e.symm (DihedralGroup.r 1)) from
      (orderOf_injective A.subtype A.subtype_injective _)]
    rw [e.symm.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  rcases hor with h | h
  · have hh := rotation_action_square g r hg2 2 h
    have he : r ^ 3 = 1 := by
      have he' : r^3 * r = 1 * r := by simpa only [←pow_succ,one_mul] using hh.symm
      exact mul_right_cancel he'
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hr] at hd
    norm_num at hd
  · have hh := rotation_action_square g r hg2 3 h
    have he : r ^ 8 = 1 := by
      have he' : r^8 * r = 1 * r := by simpa only [←pow_succ,one_mul] using hh.symm
      exact mul_right_cancel he'
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [hr] at hd
    norm_num at hd

/-- Self-centralization absorbs a preserving involution into the two actual
commuting D10 factors, without identifying their full normalizer. -/
theorem quintic_preserving_involution_mem_join (A B : Subgroup G)
    (eA : A ≃* DihedralGroup 5) (eB : B ≃* DihedralGroup 5)
    (hc : ∀ x ∈ A, ∀ y ∈ B, Commute x y)
    (hz : centralizer ((A ⊔ B : Subgroup G) : Set G) ≤ A ⊔ B)
    (g : G) (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) (hg : g^2=1) : g ∈ A ⊔ B :=
  mem_join_of_inner_on_commuting_factors A B hc hz g
    (quintic_involution_inner A eA g hA hg) (quintic_involution_inner B eB g hB hg)

end CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel
