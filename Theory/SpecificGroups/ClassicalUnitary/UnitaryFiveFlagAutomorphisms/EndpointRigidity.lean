module
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.ResidualAction

/-!
# Detection on the opposite perfect endpoint

An automorphism fixing a normal subgroup pointwise has displacement in its
centralizer. If that centralizer is central and the ambient local group is
perfect, uniqueness through the central quotient makes the automorphism
identity. The native U₅ consumer applies this to the entire line radical,
which is contained in the already fixed plane residual.

Source application: Aschbacher–Smith F.4.29(2), printed p.289 of
refs/quasithin.pdf. This is a general perfect-group argument.
-/

public noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
open Subgroup

/-- A perfect local group is detected on a normal subgroup whose centralizer is central. -/
theorem eq_one_of_fixes_normal {G : Type*} [Group G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hC : centralizer (N : Set G) ≤ center G)
    (a : MulAut G) (ha : ∀ n ∈ N, a n = n) : a = 1 := by
  have hd (g : G) : a g * g⁻¹ ∈ center G := by
    apply hC
    intro n hn
    have he : (a g)⁻¹ * n * a g = g⁻¹*n*g := by
      have hh := ha (g⁻¹*n*g) (by simpa only [inv_inv] using Subgroup.Normal.conj_mem (inferInstance : N.Normal) n hn g⁻¹)
      simpa only [map_mul,map_inv,ha n hn,inv_inv] using hh
    calc
      n * (a g * g⁻¹) = a g * ((a g)⁻¹*n*a g) * g⁻¹ := by group
      _ = (a g*g⁻¹)*n := by rw [he]; group
  apply MulEquiv.toMonoidHom_injective
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    (QuotientGroup.mk' (center G)) (by rw [QuotientGroup.ker_mk'])
  ext g
  change QuotientGroup.mk' (center G) (a g) = QuotientGroup.mk' (center G) g
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul]
  exact (QuotientGroup.eq_one_iff _).mpr (hd g)
end Theory.SpecificGroups.UnitaryFive.FlagAutomorphisms
