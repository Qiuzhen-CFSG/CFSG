module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.MonomialStabilizer.MarkedLifts

/-!
# Reduced octad signs in Omega

Every even sign pattern on the marked octad is a sum of two-coordinate
patterns. For three distinct coordinates `a`, `b`, `k`, a three-cycle moves
`{a, k}` to `{b, k}`. The difference of these two even patterns is `{a, b}`.
The existing Golay restriction and native alternating-image theorems lift
this calculation to an actual sign/permutation commutator in the integral
centralizer. The full orthogonal commutator bound puts its reduction in Omega.

Equality of sign restrictions gives equality of the literal reduced actions,
so summing these commutators proves the result for every Golay sign change.
All coordinates remain explicit; no constructor for `Coordinates` is used.
The final theorem applies the result to the actual signed-permutation lifts.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(4), 25.2 and the
axis-stabilizer argument in 25.5(7), pp.132–134.
-/

open Atlas.Codes Atlas.Lattices Atlas.Conway
open Sporadic.Mathieu.M24LocalGeometry
open scoped BigOperators commutatorElement
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel.MonomialStabilizer
attribute [local irreducible] golayBasis

private theorem signs_eq_of_restriction (C : Coordinates) (c d : golay)
    (h : signRestriction c = signRestriction d) :
    C.orthogonalAction (signs (Multiplicative.ofAdd c)) =
      C.orthogonalAction (signs (Multiplicative.ofAdd d)) := by
  have hc := signedAction_lift C c 1
  have hd := signedAction_lift C d 1
  simp only [lift, map_one, mul_one] at hc hd
  rw [h] at hc
  exact signedAction_unique C _ _ hc hd

private theorem signs_commutator (p : NativeStabilizer) (c : golay) :
    signs (Multiplicative.ofAdd
      (golayPermutationEquiv (SextetCore.groupEquiv p.val) c - c)) =
      ⁅permutations p, signs (Multiplicative.ofAdd c)⁆ := by
  apply Subtype.ext
  have h := congrArg (fun f : Multiplicative golay →* LeechIsometryGroup =>
    f (Multiplicative.ofAdd c))
    (sign_permutation_compatibility (SextetCore.groupEquiv p.val))
  change signEmbedding (Multiplicative.ofAdd
    (golayPermutationEquiv (SextetCore.groupEquiv p.val) c - c)) = _
  rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv]
  change signEmbedding ((golayPermutationAction (SextetCore.groupEquiv p.val))
    (Multiplicative.ofAdd c)) * (signEmbedding (Multiplicative.ofAdd c))⁻¹ = _
  change signEmbedding ((golayPermutationAction (SextetCore.groupEquiv p.val))
    (Multiplicative.ofAdd c)) = permutationEmbedding (SextetCore.groupEquiv p.val) *
      signEmbedding (Multiplicative.ofAdd c) *
        (permutationEmbedding (SextetCore.groupEquiv p.val))⁻¹ at h
  rw [h]
  rfl

private theorem restriction_permuted (p : NativeStabilizer) (c : golay) (i : Coordinate) :
    signRestriction (golayPermutationEquiv (SextetCore.groupEquiv p.val) c) i =
      signRestriction c ((coordinatePermutation p).symm i) := by
  change c.val ((SextetCore.groupEquiv p.val).val.symm i.val) =
    c.val (((coordinatePermutation p).symm i).val)
  rw [coordinatePermutation_symm_apply]

private theorem permute_single (p : Equiv.Perm Coordinate) (a i : Coordinate) :
    (Pi.single (M := fun _ : Coordinate => Bit) a (1 : Bit)) (p.symm i) =
      Pi.single (M := fun _ : Coordinate => Bit) (p a) (1 : Bit) i := by
  classical
  simp [Pi.single_apply, Equiv.symm_apply_eq]

private theorem pair_restriction_commutator (a b k : Coordinate)
    (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    ∃ p : NativeStabilizer, ∃ c : golay,
      signRestriction (golayPermutationEquiv (SextetCore.groupEquiv p.val) c - c) =
        Pi.single (M := fun _ : Coordinate => Bit) a (1 : Bit) +
          Pi.single (M := fun _ : Coordinate => Bit) b 1 := by
  classical
  let q : Equiv.Perm Coordinate := Equiv.swap a b * Equiv.swap k a
  have hq : q ∈ alternatingGroup Coordinate := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    simp [q, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hak.symm]
  obtain ⟨p, hp⟩ := (show q ∈ coordinatePermutation.range by
    rw [coordinatePermutation_range]; exact hq)
  have hs : (∑ i : Coordinate,
      (Pi.single (M := fun _ : Coordinate => Bit) a (1 : Bit) +
          Pi.single (M := fun _ : Coordinate => Bit) k 1) i) = 0 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single']
    decide
  obtain ⟨c, hc⟩ := signRestriction_surjective_even _ hs
  refine ⟨p, c, ?_⟩
  have ha : q a = k := by
    change (Equiv.swap a b) ((Equiv.swap k a) a) = k
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hak.symm hbk.symm]
  have hk : q k = b := by simp [q, Equiv.Perm.mul_apply]
  funext i
  rw [map_sub]
  simp only [Pi.sub_apply, restriction_permuted, hc, hp, Pi.add_apply,
    permute_single, ha, hk]
  rw [ZModModule.sub_eq_add]
  have ht : (Pi.single (M := fun _ : Coordinate => Bit) k (1 : Bit)) i +
      Pi.single (M := fun _ : Coordinate => Bit) k 1 i = 0 := ZModModule.add_self _
  linear_combination ht

private theorem pair_lift_mem_omega (C : Coordinates) (a b : Coordinate) :
    ∃ c : golay, signRestriction c =
      Pi.single (M := fun _ : Coordinate => Bit) a (1 : Bit) +
          Pi.single (M := fun _ : Coordinate => Bit) b 1 ∧
      C.orthogonalAction (signs (Multiplicative.ofAdd c)) ∈ SelectedGeometry.omega := by
  classical
  by_cases hab : a = b
  · subst b
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero]
      exact (ZModModule.add_self _).symm
    · simp
  · have hc : ({a, b} : Finset Coordinate).card <
        (Finset.univ : Finset Coordinate).card := by
      have := Finset.card_le_two (a := a) (b := b)
      rw [Finset.card_univ, coordinate_card]
      omega
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨p, c, he⟩ := pair_restriction_commutator a b k hab (Ne.symm hk.1) (Ne.symm hk.2)
    refine ⟨_, he, ?_⟩
    rw [signs_commutator, map_commutatorElement]
    exact ClassicalOrthogonal.BinaryEightObstruction.commutator_full_le_elementary
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

/-- Every literal Golay sign change on the octad belongs to the binary Omega
subgroup. Even sign patterns are sums of two-coordinate patterns, each of
which is the restriction of a sign/permutation commutator. -/
theorem signs_mem_omega (C : Coordinates) (c : golay) :
    C.orthogonalAction (signs (Multiplicative.ofAdd c)) ∈ SelectedGeometry.omega := by
  classical
  obtain ⟨a⟩ : Nonempty Coordinate := Fintype.card_pos_iff.mp (by rw [coordinate_card]; decide)
  have hp (i : Coordinate) : ∃ d : golay,
      signRestriction d =
        Pi.single (M := fun _ : Coordinate => Bit) i (signRestriction c i) +
          Pi.single (M := fun _ : Coordinate => Bit) a (signRestriction c i) ∧
      C.orthogonalAction (signs (Multiplicative.ofAdd d)) ∈ SelectedGeometry.omega := by
    rcases bit_cases (signRestriction c i) with hi | hi
    · refine ⟨0, ?_, ?_⟩
      · simp [hi]
      · simp
    · rw [hi]
      exact pair_lift_mem_omega C i a
  choose d hd hm using hp
  have he : signRestriction (∑ i, d i) = signRestriction c := by
    rw [map_sum]
    simp only [hd]
    funext j
    simp only [Finset.sum_apply, Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single]
    have hz : (∑ i, Pi.single (M := fun _ : Coordinate => Bit) a (signRestriction c i) j) = 0 := by
      by_cases hj : j = a
      · subst j
        simp only [Pi.single_eq_same]
        exact signRestriction_even c
      · simp [Pi.single_eq_of_ne hj]
    rw [hz, add_zero]
  have hsum (S : Finset Coordinate) :
      C.orthogonalAction (signs (Multiplicative.ofAdd (∑ i ∈ S, d i))) ∈
        SelectedGeometry.omega := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, ofAdd_add, map_mul, map_mul]
      exact SelectedGeometry.omega.mul_mem (hm i) ih
  rw [← signs_eq_of_restriction C _ _ he]
  exact hsum Finset.univ

/-- The literal monomial lift now satisfies the Omega premise used by the
axis-stabilizer assembly, without an additional sign-containment hypothesis. -/
theorem lift_mem_omega (C : Coordinates) (c : golay) (p : NativeStabilizer) :
    C.orthogonalAction (lift c p) ∈ SelectedGeometry.omega :=
  lift_mem_omega_of_signs C (signs_mem_omega C) c p

end Realization.OmegaImage.LatticeModel.MonomialStabilizer
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
