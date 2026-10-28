module

public import Theory.SpecificGroups.OrthogonalFourBinary.IndexTwoNormalizer.Geometry
public import Mathlib.GroupTheory.IndexNormal

/-!
# Normalizers of index-two subgroups in the binary orthogonal four-group

A Sylow two-subgroup fixes a point on the nine nonzero singular vectors.
The stabilizer of that point has order eight and is a two-group, so Sylow
maximality identifies it with the given Sylow subgroup. Its index-two
subgroup has order four and therefore cannot fix a second singular vector:
the common stabilizer of two distinct points has order at most two.
Consequently its normalizer fixes the unique point and lies in the Sylow
subgroup. Index-two normality gives the reverse inclusion.

This argument uses the actual quadratic-isometry action, and applies to
all index-two subgroups, including the one in Aschbacher–Smith 15.3.66.
Source: combined manuscript (1 March 2004), printed pp.1121–1122 and
1152–1154, especially the Sylow argument in the proof of 15.3.68(3).
-/

public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.IndexTwoNormalizer

private abbrev Point := {x : Space // x ≠ 0 ∧ form x = 0}

private instance : MulAction IsometryGroup Point where
  smul e x := ⟨e.val x, by
    constructor
    · intro h
      exact x.property.1 (e.val.injective (h.trans (map_zero e.val).symm))
    · exact ((mem_quadraticIsometrySubgroup form _).mp e.property x).trans x.property.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

private theorem point_card : Nat.card Point = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Every index-two subgroup of a Sylow two-subgroup has normalizer contained
in that Sylow subgroup. This holds for all three index-two subgroups. -/
theorem normalizer_le (P : Sylow 2 IsometryGroup) (H : Subgroup IsometryGroup)
    (hHP : H ≤ P) (hi : H.relIndex P = 2) : normalizer (H : Set IsometryGroup) ≤ P := by
  obtain ⟨x,hx⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card Point
    (by rw [point_card]; decide)
  have hP : (P : Subgroup IsometryGroup) ≤ MulAction.stabilizer IsometryGroup x.val := by
    intro g hg
    have h := hx ⟨g,hg⟩
    exact congrArg Subtype.val h
  have heP : MulAction.stabilizer IsometryGroup x.val = P :=
    P.is_maximal' (IsPGroup.of_card (n := 3)
      (singular_stabilizer_card x.val x.property.1 x.property.2)) hP
  have hcP : Nat.card P = 8 := by
    rw [← heP]
    exact singular_stabilizer_card x.val x.property.1 x.property.2
  have hcH : Nat.card H = 4 := by
    have hc := (H.subgroupOf (P : Subgroup IsometryGroup)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hHP).toEquiv] at hc
    change Nat.card H * H.relIndex P = Nat.card P at hc
    rw [hi,hcP] at hc
    omega
  intro g hg
  have hHg : H ≤ MulAction.stabilizer IsometryGroup (g • x.val) := by
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H :=
      (mem_normalizer_iff''.mp hg h).mp hh
    have hf := hP (hHP hh')
    change (g⁻¹ * h * g) • x.val = x.val at hf
    have he := congrArg (fun w : Space => g • w) hf
    change h • (g • x.val) = g • x.val
    simpa only [mul_smul, smul_inv_smul] using he
  have he : g • x.val = x.val := by
    by_contra hne
    have hle := card_le_of_le (le_inf (hHP.trans hP) hHg)
    have hb := two_singular_stabilizer_card x.val (g • x.val)
      x.property.1 x.property.2
      (by
        intro h
        exact x.property.1 (g.val.injective (h.trans (map_zero g.val).symm)))
      (((mem_quadraticIsometrySubgroup form _).mp g.property x.val).trans x.property.2) hne
    rw [hcH] at hle
    omega
  rw [← heP]
  exact he

/-- The normalizer equals the given Sylow two-subgroup. -/
theorem normalizer_eq (P : Sylow 2 IsometryGroup) (H : Subgroup IsometryGroup)
    (hHP : H ≤ P) (hi : H.relIndex P = 2) : normalizer (H : Set IsometryGroup) = P := by
  apply le_antisymm (normalizer_le P H hHP hi)
  exact (normal_subgroupOf_iff_le_normalizer hHP).mp (normal_of_index_eq_two hi)

end OrthogonalFourBinary.IndexTwoNormalizer
