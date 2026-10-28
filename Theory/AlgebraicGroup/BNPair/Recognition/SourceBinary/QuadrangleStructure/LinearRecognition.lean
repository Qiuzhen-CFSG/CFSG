module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CrossedRootAlternative
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Commutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Counts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2RankThree.Markings
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates
public import Theory.GroupAction.SymplecticRankThree.Higman

/-!
# Full symplectic recognition from equal linear split factors

The crossed-root alternative selects a commuting side of the quadrangle.
Its canonical root fixes the closed neighboring orbit in the parabolic
coset action. The actual Bruhat counts and root order give Higman's
condition (i), so the proved rank-three theorem constructs a normal full
Sp₄ subgroup. Normal generation by U makes it the whole quotient.

If the opposite side commutes, reverse the two labels on the same marked
quotient. The longest Weyl element, Borel, unipotent group and quotient
carrier are unchanged. This proves recognition in both orientations,
including full Sp₄(2), with no assumed natural module or commutator row.
The CFSG LinearQuadrangleRecognition adapter supplies both local markings,
relative characteristic two and normal generation from original F.1.1.

Source: Fong--Seitz I (6A), p.37; II (7C), p.193 and (8A), p.197;
Higman (1964), Theorem 2(i), pp.154--155. This is the selected linear
quadrangle branch, not classification of an arbitrary Tits system.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.GroupAction.SymplecticRankThree
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private def reversedQuotient : MarkedQuotient (fun i => P i.rev) where
  D := Q.D
  disjoint i := Q.disjoint i.rev
  tits := Q.tits
  simple i := Q.simple i.rev
  simple_injective := Q.simple_injective.comp Fin.rev_injective
  simple_range := by
    rw [←Q.simple_range]
    ext s
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.rev,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.rev,by simp⟩
  parabolic_image i := Q.parabolic_image i.rev
  borel_image := by
    change (P 1 ⊓ P 0).map (QuotientGroup.mk' Q.D) = Q.tits.B
    rw [inf_comm]
    exact Q.borel_image

private theorem reversed_rotation : rotationOrder (reversedQuotient Q) = rotationOrder Q := by
  change orderOf (Q.simple 1 * Q.simple 0) = orderOf (Q.simple 0 * Q.simple 1)
  have hi (i : Fin 2) : (Q.simple i)⁻¹ = Q.simple i :=
    inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2)
  have he : (Q.simple 0 * Q.simple 1)⁻¹ = Q.simple 1 * Q.simple 0 := by
    rw [mul_inv_rev,hi,hi]
  rw [←he,orderOf_inv]

private theorem reversed_longest : longest (reversedQuotient Q) = longest Q := by
  apply eq_longest_of_wordLength_eq Q
  exact (wordLength_longest (reversedQuotient Q)).trans (reversed_rotation Q)

private theorem reversed_root (i : Fin 2) :
    simpleRoot (reversedQuotient Q) split i = simpleRoot Q split i.rev := by
  change rootIntersection split (longest (reversedQuotient Q)) (Q.simple i.rev) = _
  rw [reversed_longest]
  rfl

private theorem symplectic_equiv_of_commuting_root {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4)
    (hq : ∀ i, Nat.card (simpleRoot Q split i) = Nat.card F)
    (hV : ∀ i, split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)))
    (hc : ∀ i, centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hrow : ⁅simpleRoot Q split 1,C2RankThree.kernelRoot Q split⁆ = ⊥)
    (hgen : split.unipotentClosure = ⊤) : Nonempty ((X ⧸ Q.D) ≃* Sp F) := by
  let := C2RankThree.faithful Q split 1 (hc 1)
  let := C2RankThree.primitive Q 1
  let := Fintype.ofFinite (C2RankThree.Points Q 1)
  obtain ⟨K,hK,⟨E⟩⟩ := condition_i_recognition (F := F)
    (C2RankThree.rightCosetPoint Q 1 1) (C2RankThree.neighborPoint Q) (C2RankThree.oppositePoint Q)
    (C2RankThree.base_ne_neighbor Q) (representative (Q.simple 0) : X ⧸ Q.D)⁻¹
    (C2RankThree.neighbor_swap_base Q) (C2RankThree.neighbor_swap_neighbor Q)
    (C2RankThree.opposite_orbit_eq_compl Q hm)
    (C2RankThree.points_card Q split hm (hq 0) (hq 1) 1)
    (C2RankThree.neighbor_orbit_card Q split hm (hq 0) (hq 1))
    (C2RankThree.source_kernel_lower_bound Q split hm (hq 1) hV hrow)
  let := hK
  exact ⟨C2RankThree.wholeEquiv Q split hgen
    (C2RankThree.unipotent_card Q split hm (hq 0) (hq 1)) K E⟩

/-- Equal actual linear factors force full symplectic recognition in characteristic two. -/
theorem symplectic_equiv_of_equal_linear_factors {F : Type*}
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4)
    (hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
    (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
    (hc : ∀ i, centralizer (pCore 2 (Q.tits.standardParabolic {Q.simple i}) :
      Set (Q.tits.standardParabolic {Q.simple i})) ≤ pCore 2 (Q.tits.standardParabolic {Q.simple i}))
    (hgen : split.unipotentClosure = ⊤) : Nonempty ((X ⧸ Q.D) ≃* Sp F) := by
  have hq (i : Fin 2) := GTwoSource.simpleRoot_card Q split i (hV i) (μ i)
  have hn (i : Fin 2) : split.U ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split i (hV i)))
  rcases linear_cross_root_alternative Q split hm 0 1 (by decide) (hV 0) (hV 1)
    (μ 0) (μ 1) with hrow | hrow
  · exact symplectic_equiv_of_commuting_root Q split hm hq hn hc hrow hgen
  · apply symplectic_equiv_of_commuting_root (reversedQuotient Q) split
      ((reversed_rotation Q).trans hm) (fun i => by rw [reversed_root]; exact hq i.rev)
      (fun i => hn i.rev) (fun i => hc i.rev) _ hgen
    change ⁅simpleRoot (reversedQuotient Q) split 1,
      rightConjugate (simpleRoot (reversedQuotient Q) split 1)
        (representative (Q.simple 1) : X ⧸ Q.D)⁆ = ⊥
    rw [reversed_root]
    exact hrow
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
