module
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# A normal cubic subgroup excludes binary transvections

A commutator with a rank-one actor has displacement at most two. If it is
nonidentity in the normal cubic subgroup, it generates that subgroup and
moves the entire module. In dimension greater than two this is impossible.
The actor therefore centralizes the cubic subgroup, which must fix its
binary displacement line, again contradicting the zero fixed space.

This applies to the external cubic in Aschbacher–Smith, 13.8.20(a),
printed p.954, without a classification of the component module.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A normal fixed-point-free cubic subgroup excludes binary transvections
in dimension greater than two. -/
theorem no_transvections_of_normal_cubic
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (hN : Nat.card N = 3) (hfix : fixedSpace ρ N = ⊥)
    (hdim : 2 < Module.finrank (ZMod 2) V) (a : G) :
    fixedCodim ρ (zpowers a) ≠ 1 := by
  intro hr
  have hc (n : N) : Commute a (n : G) := by
    have hm : a * (n : G) * a⁻¹ * (n : G)⁻¹ ∈ N :=
      N.mul_mem ((inferInstance : N.Normal).conj_mem _ n.property a) (N.inv_mem n.property)
    have he : a * (n : G) * a⁻¹ * (n : G)⁻¹ = 1 := by
      by_contra hn
      have hg := (cyclicThree_generator N hN _ hm hn).1
      have hh := fixedCodim_commutator_le_twice ρ a (n : G)
      rw [hg, hr] at hh
      have he := fixedCodim_add_finrank ρ N
      rw [hfix, finrank_bot] at he
      omega
    change a * (n : G) = (n : G) * a
    have hh := congrArg (fun x : G => x * (n : G) * a) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hh
  have hz (v : V) : ρ a v - v = 0 := by
    have hm : ρ a v - v ∈ fixedSpace ρ N := by
      intro n
      exact fixes_displacement_of_commute_rank_one ρ a n
        ((fixedCodim_zpowers_eq_displacement_rank ρ a).symm.trans hr) (hc n) v
    rwa [hfix, Submodule.mem_bot] at hm
  have he : ρ a - LinearMap.id = 0 := by
    ext v
    exact hz v
  rw [fixedCodim_zpowers_eq_displacement_rank, he, LinearMap.range_zero, finrank_bot] at hr
  omega
end Representation.BinaryOffender
