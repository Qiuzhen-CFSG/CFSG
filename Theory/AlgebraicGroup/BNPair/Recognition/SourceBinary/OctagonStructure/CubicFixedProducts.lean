module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.FixedProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearPairCubic
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FourRootIntervals

/-!
# The seven-root fixed product for a cubic Cartan actor

The positive seven-root coordinates in an octagon alternate between the two
natural root families.  Combined with the cubic actor from `LinearPairCubic`,
the generic fixed-product lemma identifies its fixed part with the product of
the factorwise fixed subgroups.  The vanishing of the four even-family fixed
factors is kept as an explicit consumer premise so this module remains
independent of the later representation argument in (6G).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

def orderedRootFixedProduct {Y : Type*} [Group Y] (l : List (Subgroup Y))
    (c : Y) : Set Y :=
  ((l.map (fun A => (A ⊓ centralizer ({c} : Set Y) : Subgroup Y))).map
    (fun A => (A : Set Y))).prod

private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem right_simple (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl

private theorem fourth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [←right_rep]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)

private theorem longest_eight (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
  have h0 := alternatingWord_longest Q false
  have h1 := alternatingWord_longest Q true
  rw [hm] at h0 h1
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact (hij rfl).elim
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
  · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
  · exact (hij rfl).elim

private theorem fifth_root (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split j (Q.simple i*Q.simple j) := by
  have he : Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i =
      (longest Q*Q.simple j)*(Q.simple i*Q.simple j) := by
    rw [longest_eight Q hm i j hij]
    simp only [mul_assoc, ←mul_assoc (Q.simple i) (Q.simple i),
      ssq, one_mul, mul_one]
  rw [he, rootAt_longest_simple_mul Q split hm j i hij.symm]

/-- The seven positive roots, with the odd-family endpoint chosen as `i = 0`. -/
theorem octagon_ordered_seven_roots (hm : rotationOrder Q = 8) :
    orderedRoots Q split true 7 =
      [simpleRoot Q split 1, rootAt Q split 0 (Q.simple 1),
       rootAt Q split 1 (Q.simple 0*Q.simple 1),
       rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1),
       rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0),
       rootAt Q split 0 (Q.simple 1*Q.simple 0), rootAt Q split 1 (Q.simple 0)] := by
  have h0 := perpendicular_root_stable Q split hm 0 1 (by decide)
    (representative (Q.simple 0)) (representative_spec _)
  have h1 := perpendicular_root_stable Q split hm 1 0 (by decide)
    (representative (Q.simple 1)) (representative_spec _)
  rw [right_rep] at h0 h1
  have h5 := congrArg (fun A => rightConjugate A (representative (Q.simple 1) : X ⧸ Q.D)) h0
  have h6 := congrArg (fun A => rightConjugate A
    (representative (Q.simple 0*Q.simple 1) : X ⧸ Q.D)) h1
  simp only [right_rep, mul_assoc, ssq, mul_one] at h5 h6
  simp only [←mul_assoc] at h5 h6
  simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Bool.not_true, List.map_cons, List.map_nil, right_simple, right_rep]
  rw [h1, h5, h6]
  simp only [mul_assoc, ssq, mul_one]

/-- The cubic actor fixed subgroup on the seven-root radical as a product of
the seven factorwise fixed subgroups. -/
theorem cubic_seven_root_fixed_product
    (hm : rotationOrder Q = 8)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    (Set.range (rootProduct (orderedRoots Q split true 7))) ∩
        (centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      orderedRootFixedProduct (orderedRoots Q split true 7) (c : X ⧸ Q.D) := by
  change (Set.range (rootProduct (orderedRoots Q split true 7))) ∩
      (centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
    (((orderedRoots Q split true 7).map (fun A =>
      (A ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)))).map
      (fun A => (A : Set (X ⧸ Q.D)))).prod
  exact ordered_root_product_conj_fixed Q split true 7 (by omega) c

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
