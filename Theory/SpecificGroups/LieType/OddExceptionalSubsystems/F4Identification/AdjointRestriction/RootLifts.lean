module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.Coordinates

/-!
# Lifting the concrete F4 roots through the E6 restriction

Every pair root, signed unit root, and half-sign root of the existing F4
coordinate model has a lift in the existing E6 root set. We check representatives
with positive first nonzero coordinate and obtain their negatives from the E6
root pairing. The witnesses are either pair roots supported on coordinates 3--7
or even-parity half-sign roots satisfying both E6 orthogonality equations.
The scalar checks use the literal projection from `Coordinates`.

Reading a lifted coordinate in each fibre then proves that the integral
fibre-incidence map is injective over every commutative ring. This supplies the
root-geometric input to the folded adjoint comparison.

Sources: GLS3, Definition 2.3.1 and Proposition 2.3.2, in
`refs/KGroup/GLS3/chapter2.tex`; the F4 inclusions in Aschbacher--Smith A.2.17,
printed p.39 of `refs/quasithin.pdf`.
-/

set_option linter.unusedSimpArgs false
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction

private def HasRootLift (x : Vec 4) : Prop :=
  ∃ r : typeE6Roots, rootProjection r.val = x

private theorem e6_mem_of_e8 {x : Vec 8} (hx : x ∈ typeE8Roots)
    (h01 : x 0 + x 1 = 0) (h12 : x 1 - x 2 = 0) : x ∈ typeE6Roots := by
  refine ⟨⟨hx, ?_⟩, ?_⟩
  · simpa [dot, basisVector, Pi.single_apply, mul_add, Finset.sum_add_distrib] using h01
  · simpa [dot, basisVector, Pi.single_apply, mul_sub, Finset.sum_sub_distrib] using h12

private theorem hasRootLift_neg {x : Vec 4} (h : HasRootLift x) : HasRootLift (-x) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨t, ht⟩ := typeE6RootPairing.neg_root_mem r
  have hv : t.val = -r.val := congrArg Subtype.val ht
  refine ⟨t, ?_⟩
  rw [hv, map_neg, hr]

private theorem pair_lift (i j : Fin 8) (a b : ℝ) (hij : i ≠ j)
    (hi : 3 ≤ i.val) (hj : 3 ≤ j.val)
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hb : b ∈ ({-1, 1} : Set ℝ)) :
    HasRootLift (rootProjection (a • basisVector i + b • basisVector j)) := by
  refine ⟨⟨_, e6_mem_of_e8 (Or.inl ⟨i, j, hij, a, b, ha, hb, rfl⟩) ?_ ?_⟩, rfl⟩
  all_goals
    have hi0 : (0 : Fin 8) ≠ i := by intro h; subst i; simp at hi
    have hi1 : (1 : Fin 8) ≠ i := by intro h; subst i; simp at hi
    have hi2 : (2 : Fin 8) ≠ i := by intro h; subst i; simp at hi
    have hj0 : (0 : Fin 8) ≠ j := by intro h; subst j; simp at hj
    have hj1 : (1 : Fin 8) ≠ j := by intro h; subst j; simp at hj
    have hj2 : (2 : Fin 8) ≠ j := by intro h; subst j; simp at hj
    simp [basisVector, Pi.single_apply, hi0, hi1, hi2, hj0, hj1, hj2]

private theorem half_lift (ε : Fin 8 → Bool) (heven : evenNegative ε)
    (h01 : halfSignVector ε 0 + halfSignVector ε 1 = 0)
    (h12 : halfSignVector ε 1 - halfSignVector ε 2 = 0) :
    HasRootLift (rootProjection (halfSignVector ε)) :=
  ⟨⟨_, e6_mem_of_e8 (Or.inr ⟨ε, heven, rfl⟩) h01 h12⟩, rfl⟩

-- Pairs involving coordinate 0 lift to half-sign roots; the others lift to pair roots.
private theorem ordered_pair_lift (i j : Fin 4) (hij : i < j) (b : Bool) :
    HasRootLift (basisVector i + if b then basisVector j else -basisVector j) := by
  fin_cases i <;> fin_cases j <;> cases b <;> norm_num [Fin.lt_def] at hij
  · convert half_lift ![true, false, false, true, false, false, false, false]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + (-0) : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + (-1) : ℝ) = (-(1 / 2) + -(1 / 2) + -(1 / 2) + -(1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) + -(1 / 2) - -(1 / 2) - -(1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) - -(1 / 2) + -(1 / 2) - -(1 / 2)) / 2
      norm_num
  · convert half_lift ![true, false, false, true, true, true, true, true]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + 0 : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + 1 : ℝ) = ((1 / 2) + (1 / 2) + (1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) + (1 / 2) - (1 / 2) - (1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) - (1 / 2) + (1 / 2) - (1 / 2)) / 2
      norm_num
  · convert half_lift ![true, false, false, true, false, false, true, true]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + (-0) : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) + -(1 / 2) + (1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + (-1) : ℝ) = (-(1 / 2) + -(1 / 2) - (1 / 2) - (1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) - -(1 / 2) + (1 / 2) - (1 / 2)) / 2
      norm_num
  · convert half_lift ![true, false, false, true, true, true, false, false]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + 0 : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) + (1 / 2) + -(1 / 2) + -(1 / 2)) / 2
      norm_num
    · change (0 + 1 : ℝ) = ((1 / 2) + (1 / 2) - -(1 / 2) - -(1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) - (1 / 2) + -(1 / 2) - -(1 / 2)) / 2
      norm_num
  · convert half_lift ![true, false, false, true, false, true, false, true]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + (-0) : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) + (1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + (-0) : ℝ) = (-(1 / 2) + (1 / 2) - -(1 / 2) - (1 / 2)) / 2
      norm_num
    · change (0 + (-1) : ℝ) = (-(1 / 2) - (1 / 2) + -(1 / 2) - (1 / 2)) / 2
      norm_num
  · convert half_lift ![true, false, false, true, true, false, true, false]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 + 0 : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) + -(1 / 2) + (1 / 2) + -(1 / 2)) / 2
      norm_num
    · change (0 + 0 : ℝ) = ((1 / 2) + -(1 / 2) - (1 / 2) - -(1 / 2)) / 2
      norm_num
    · change (0 + 1 : ℝ) = ((1 / 2) - -(1 / 2) + (1 / 2) - -(1 / 2)) / 2
      norm_num
  · convert pair_lift 6 7 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-1) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 4 5 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 5 7 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-1) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 4 6 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 5 6 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + (-0) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + (-1) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 4 7 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 + 0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 + 1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]

-- Coordinate 0 uses a half-sign root, and coordinates 1--3 use pair roots.
private theorem unit_lift (i : Fin 4) : HasRootLift (basisVector i) := by
  fin_cases i
  · convert half_lift ![true, false, false, true, false, true, true, false]
      (by unfold evenNegative; decide) (by change (1 / 2 : ℝ) + -(1 / 2) = 0; norm_num)
      (by change (-(1 / 2) : ℝ) - -(1 / 2) = 0; norm_num) using 1
    ext k
    fin_cases k
    · change (1 : ℝ) = (5 * (1 / 2) + -(1 / 2) + -(1 / 2) + (1 / 2)) / 2
      norm_num
    · change (0 : ℝ) = (-(1 / 2) + (1 / 2) + (1 / 2) + -(1 / 2)) / 2
      norm_num
    · change (0 : ℝ) = (-(1 / 2) + (1 / 2) - (1 / 2) - -(1 / 2)) / 2
      norm_num
    · change (0 : ℝ) = (-(1 / 2) - (1 / 2) + (1 / 2) - -(1 / 2)) / 2
      norm_num
  · convert pair_lift 4 7 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 4 6 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 4 5 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (0 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (1 : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]

-- The eight half-sign roots with positive coordinate 0; negation supplies the others.
private theorem positive_half_lift (a b c : Bool) :
    HasRootLift (halfSignVector ![true, a, b, c]) := by
  cases a <;> cases b <;> cases c
  · convert pair_lift 3 4 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 5 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 6 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 7 1 (-1) (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 7 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 6 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 5 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change (-(1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
  · convert pair_lift 3 4 1 1 (by decide) (by decide) (by decide)
      (by simp) (by simp) using 1
    ext k
    fin_cases k
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]
    · change ((1 / 2) : ℝ) = _
      norm_num [rootProjection, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem unordered_pair_lift (i j : Fin 4) (hij : i ≠ j) (b : Bool) :
    HasRootLift (basisVector i + if b then basisVector j else -basisVector j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ordered_pair_lift i j hlt b
  · cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, neg_add_rev, neg_neg] using
        hasRootLift_neg (ordered_pair_lift j i hgt false)
    · simpa only [↓reduceIte, add_comm] using ordered_pair_lift j i hgt true

private theorem all_pair_lift {x : Vec 4} (hx : x ∈ pairRoots 4) : HasRootLift x := by
  obtain ⟨i, j, hij, a, b, ha, hb, rfl⟩ := hx
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simpa [neg_add, add_comm] using hasRootLift_neg (unordered_pair_lift i j hij true)
  · simpa [neg_add, add_comm] using hasRootLift_neg (unordered_pair_lift i j hij false)
  · simpa using unordered_pair_lift i j hij false
  · simpa using unordered_pair_lift i j hij true

private theorem all_half_lift (ε : Fin 4 → Bool) : HasRootLift (halfSignVector ε) := by
  have pos (δ : Fin 4 → Bool) (hδ : δ 0 = true) : HasRootLift (halfSignVector δ) := by
    have he : δ = ![true, δ 1, δ 2, δ 3] := by
      funext i
      fin_cases i
      · exact hδ
      · rfl
      · rfl
      · rfl
    rw [he]
    exact positive_half_lift (δ 1) (δ 2) (δ 3)
  cases h : ε 0
  · have hn := hasRootLift_neg (pos (fun i => !(ε i)) (by simp [h]))
    have he : -(halfSignVector (fun i => !(ε i))) = halfSignVector ε := by
      ext i
      cases hi : ε i <;> norm_num [halfSignVector, hi]
    rwa [he] at hn
  · exact pos ε h

/-- Every root of the concrete F4 model lifts through the actual E6 restriction. -/
public theorem root_lifts (s : typeF4Roots) :
    ∃ r : typeE6Roots, rootProjection r.val = s.val := by
  rcases s.property with (hpair | hunit) | hhalf
  · exact all_pair_lift hpair
  · obtain ⟨i, hi | hi⟩ := hunit
    · rw [hi]
      exact unit_lift i
    · rw [hi]
      exact hasRootLift_neg (unit_lift i)
  · obtain ⟨ε, hε⟩ := hhalf
    rw [← hε]
    exact all_half_lift ε

/-- The integral fibre-incidence map is injective over every commutative ring. -/
public theorem linearMap_injective (R : Type*) [CommRing R] :
    Function.Injective (linearMap R) :=
  linearMap_injective_of_root_lifts R root_lifts

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction
