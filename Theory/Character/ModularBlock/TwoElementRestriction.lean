module

public import Theory.Character.ModularBlock.TwoElementTrace
public import Theory.Character.ModularBlock.RestrictionProjectorTrace

/-!
# Principal-block restriction on cyclic roots of a two-element

Let `x` have two-power order and `C` its centralizer. On elements of `C` whose
cyclic subgroup contains `x`, the compatible local principal projection of
an ambient irreducible character equals that character if its ambient block
is principal, and vanishes otherwise. The modular place is arbitrary.

The integral regular-bimodule comparison in `TwoElementTrace`, followed
by extension to complex coefficients, identifies the local-left and
ambient-right mixed traces. Ordinary character orthogonality, as packaged in
`RestrictionProjectorTrace`, extracts each restricted character's projection.

Source: Alperin--Brauer--Gorenstein, Chapter III, Sections 5--6, associated-block
support and generalized decomposition expansion, especially III.6 preceding
equation (4); Fong (1967), printed pp.73--74.
-/

public section
noncomputable section

namespace ModularBlock.TwoElementRestriction

open scoped BigOperators
open PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- The compatible local principal projection of a restricted ambient row on
cyclic roots of a two-element, for any prescribed modular place. -/
theorem restriction_projection_on_twoElement_roots
    (d : PrincipalCongruenceBlockData G) (x : G) (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (i : d.I) (a : Subgroup.centralizer ({x} : Set G))
    (hxa : x ∈ Subgroup.zpowers (a : G)) :
    let C := Subgroup.centralizer ({x} : Set G)
    let b := CompatibleBrauerBlock.localData d C
    (∑ j ∈ b.block,
      scalarProduct C (fun c => d.chi i (ConjClasses.mk (c : G)))
        (fun c => b.chi j (ConjClasses.mk c)) * b.chi j (ConjClasses.mk a)) =
      if i ∈ d.block then d.chi i (ConjClasses.mk (a : G)) else 0 := by
  exact RestrictionProjectorTrace.restriction_projection_of_mixed_trace d
    (Subgroup.centralizer ({x} : Set G))
    (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({x} : Set G))) a
    (fun g => TwoElementTrace.complex_root_trace d x hx a hxa g) i

omit [Finite G] in
private theorem mem_zpowers_mul_odd (y v : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1) (hv : Odd (orderOf v))
    (hyv : Commute y v) : y ∈ Subgroup.zpowers (y * v) := by
  obtain ⟨n, hn⟩ := hy
  have hc : (orderOf v).Coprime (orderOf y) :=
    (hv.coprime_two_right.pow_right n).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := y) hc
  have he : (y * v) ^ orderOf v = y ^ orderOf v := by
    rw [hyv.mul_pow, pow_orderOf_eq_one, mul_one]
  have hm := pow_mem (pow_mem (Subgroup.mem_zpowers (y * v)) (orderOf v)) k
  rwa [he, hk] at hm

/-- Genuine local principal support on the two-section of `y`: for an ambient
principal-block row, its restriction agrees with its compatible local principal
projection at `y * v` for every odd-order `v` in `C(y)`. -/
theorem principal_restriction_on_twoElement_section
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1) (i : d.I) (hi : i ∈ d.block)
    (v : Subgroup.centralizer ({y} : Set G)) (hv : Odd (orderOf v)) :
    let C := Subgroup.centralizer ({y} : Set G)
    let l := CompatibleBrauerBlock.localData d C
    let yc : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)⟩
    d.chi i (ConjClasses.mk (y * (v : G))) =
      ∑ j ∈ l.block,
        scalarProduct C (fun c => d.chi i (ConjClasses.mk (c : G)))
          (fun c => l.chi j (ConjClasses.mk c)) * l.chi j (ConjClasses.mk (yc * v)) := by
  classical
  let C := Subgroup.centralizer ({y} : Set G)
  let yc : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)⟩
  have hvG : Odd (orderOf (v : G)) := by
    simpa only [Subgroup.orderOf_coe] using hv
  have hyv : Commute y (v : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp v.property).symm
  have hroot : y ∈ Subgroup.zpowers ((yc * v : C) : G) :=
    mem_zpowers_mul_odd y (v : G) hy hvG hyv
  have h := restriction_projection_on_twoElement_roots d y hy i (yc * v) hroot
  simpa only [if_pos hi, yc, Subgroup.coe_mul] using h.symm

end ModularBlock.TwoElementRestriction
