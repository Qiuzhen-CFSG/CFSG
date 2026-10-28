module
public import Theory.Representation.BinaryPermutation.PointStabilizerRank
public import Theory.Representation.BinaryPermutation.SevenParabolic.Residual

/-!
# The rank-one points in the seven-letter natural module

The unique even representative of a nonzero point has weight two, four, or
six. The existing weight-four parabolic calculation excludes weight four;
the alternating group on the six-point support excludes weight six. Thus a
point whose stabilizer has three-rank at most one is a pair vector, in the
same coordinates as the original action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.6(3),
printed pp.938–939.
-/

@[expose] public section
open Theory.GroupTheory BinaryNaturalDual.VectorStabilizers
namespace BinaryPermutation.PointStabilizerRank
open SevenParabolic

/-- The rank-one source point is represented by a pair of letters. -/
def IsPairVector (v : natural (Fin 7)) : Prop :=
  ∃ i j : Fin 7, i ≠ j ∧
    ((coreEquivNatural (Fin 7) (by decide)).symm v).val = Pi.single i 1 + Pi.single j 1

private theorem core_stabilizer_lower (v : Space) :
    Fintype.card {i : Fin 7 // v.val i = 0} / 3 + Fintype.card {i : Fin 7 // v.val i ≠ 0} / 3 ≤
      primeRank 3 (representationStabilizer (alternatingCoreRepresentation (Fin 7)) v) := by
  have he : representationStabilizer (alternatingRepresentation (Fin 7)) v.val =
      representationStabilizer (alternatingCoreRepresentation (Fin 7)) v := by
    ext g
    change representation (Fin 7) g.val v.val = v.val ↔
      coreRepresentation (Fin 7) g.val v = v
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← he]
  exact full_stabilizer_lower v.val

/-- Weight four is excluded by the existing literal weight-four parabolic calculation. -/
theorem two_le_weight_four_stabilizer (v : Space) (hv : weight v = 4) :
    2 ≤ primeRank 3 (representationStabilizer (alternatingCoreRepresentation (Fin 7)) v) := by
  have h := actor_point_threeRank_gt_one (alternatingGroup (Fin 7)).subtype
    Subtype.val_injective (by rw [Subgroup.range_subtype]) v hv
  exact h

/-- The six-point support contributes A₆ and its two independent cubics. -/
theorem two_le_weight_six_stabilizer (v : Space) (hv : weight v = 6) :
    2 ≤ primeRank 3 (representationStabilizer (alternatingCoreRepresentation (Fin 7)) v) := by
  have hw : Fintype.card {i : Fin 7 // v.val i ≠ 0} = 6 := by
    simpa only [Fintype.card_subtype, weight] using hv
  have h := core_stabilizer_lower v
  rw [hw] at h
  omega

private theorem weight_alternatives (v : Space) (hv : v ≠ 0) :
    weight v = 2 ∨ weight v = 4 ∨ weight v = 6 := by
  have hc : ∀ v : Fin 7 → ZMod 2, (∑ i, v i) = 0 → v ≠ 0 →
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 2 ∨
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 4 ∨
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 6 := by decide +kernel
  exact hc v.val v.property (fun h => hv (Subtype.ext h))

private theorem pair_of_weight_two (v : Space) (hv : weight v = 2) :
    ∃ i j : Fin 7, i ≠ j ∧ v.val = Pi.single i 1 + Pi.single j 1 := by
  have hc : ∀ v : Fin 7 → ZMod 2,
      (Finset.univ.filter (fun i => v i ≠ 0)).card = 2 →
      ∃ i j : Fin 7, i ≠ j ∧ v = Pi.single i 1 + Pi.single j 1 := by decide +kernel
  exact hc v.val hv

private theorem natural_rank_eq (v : Space) :
    primeRank 3 (representationStabilizer (alternatingCoreRepresentation (Fin 7)) v) =
      primeRank 3 (representationStabilizer (alternatingNaturalRepresentation (Fin 7))
        (coreEquivNatural (Fin 7) (by decide) v)) :=
  primeRank_equiv 3 (BinaryNaturalDual.Transport.stabilizerEquiv
    (alternatingCoreRepresentation (Fin 7)) (alternatingNaturalRepresentation (Fin 7))
    (MulEquiv.refl _) (coreEquivNatural (Fin 7) (by decide))
    (fun g w => coreEquivNatural_equivariant (Fin 7) (by decide) g.val w) v)

/-- Every nonzero point of the seven-letter natural module is a pair vector,
or its actual alternating stabilizer has three-rank at least two. -/
theorem pair_or_two_le_stabilizer (v : natural (Fin 7)) (hv : v ≠ 0) :
    IsPairVector v ∨ 2 ≤ primeRank 3 (representationStabilizer
      (alternatingNaturalRepresentation (Fin 7)) v) := by
  let e := coreEquivNatural (Fin 7) (by decide)
  let u := e.symm v
  have hu : u ≠ 0 := fun h => hv (e.symm.injective (h.trans (map_zero e.symm).symm))
  rcases weight_alternatives u hu with h | h | h
  · exact Or.inl (pair_of_weight_two u h)
  · right
    have hr := two_le_weight_four_stabilizer u h
    rw [natural_rank_eq, e.apply_symm_apply] at hr
    exact hr
  · right
    have hr := two_le_weight_six_stabilizer u h
    rw [natural_rank_eq, e.apply_symm_apply] at hr
    exact hr

/-- Rank at most one forces the source duad marking, in the unique even representative. -/
theorem pair_of_rank_le_one (v : natural (Fin 7)) (hv : v ≠ 0)
    (hr : primeRank 3 (representationStabilizer (alternatingNaturalRepresentation (Fin 7)) v) ≤ 1) :
    IsPairVector v := by
  rcases pair_or_two_le_stabilizer v hv with h | h
  · exact h
  · omega
end BinaryPermutation.PointStabilizerRank
