module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.Inputs
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition

/-!
# Matching the concrete root blocks to the eight Ree root words

The published positive-root partition matches the Weyl-defined long roots
in `RootWords`: its pair rows have zero-based word indices `7, 1, 5, 3`,
and its quartet rows have indices `0, 4, 6, 2`. The Suzuki radical keeps
all pairs and omits the first quartet, the middle Levi block.

We compute the middle reflection and relative rotation on Euclidean root
coordinates to prove the long-root matches. The existing exceptional-duality
equations then give the short-root matches. Orthogonality fixes the two roots
of each pair, while the B₂ inner product and root-sum equations identify the
mixed and high roots of each quartet. Thus both layouts are constructed from
the actual `rootBlocks`, with no additional geometric or matrix hypotheses.

Source: GLS3 2.3.7 and Table 2.4, types V and VI, in
`refs/KGroup/GLS3/chapter2.tex`; the application is Aschbacher–Smith
F.1.12(II)(i), printed pp.263–264 of `refs/quasithin.pdf`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4 ReeF4.Parabolics
open RadicalCoordinates RadicalCoordinates.FixedCoordinates
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

private lemma reflection_val (r s : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm r s).val = s.val -
      (typeF4CorootScale r * dot s.val r.val) • r.val := by
  rw [← typeF4RootPairing_root, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root, typeF4RootPairing_pairing]
  rfl

private lemma simple_reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val = r.val -
      ((if i.val < 2 then 1 else 2) * dot r.val (typeF4SimpleRoot i)) •
        typeF4SimpleRoot i := by
  rw [reflection_val, typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val]

private def simpleVector (i : Fin 4) (v : Vec 4) : Vec 4 :=
  ![![v 0, v 2, v 1, v 3],
    ![v 0, v 1, v 3, v 2],
    ![v 0, v 1, v 2, -v 3],
    ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]] i

private lemma simple_reflection_coordinates (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      simpleVector i r.val := by
  rw [simple_reflection_val]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [simpleVector, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma endReflection_val (r : F4Chevalley.Root) :
    (endReflection r).val = simpleVector 0 (simpleVector 3 r.val) := by
  change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) r)).val = _
  rw [simple_reflection_coordinates, simple_reflection_coordinates]

private def middleVector (v : Vec 4) : Vec 4 := ![v 0, v 1, -v 2, -v 3]

private lemma middleReflection_val (r : F4Chevalley.Root) :
    (middleReflection r).val = middleVector r.val := by
  change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2) r)))).val = _
  rw [simple_reflection_coordinates, simple_reflection_coordinates,
    simple_reflection_coordinates, simple_reflection_coordinates]
  rfl

private def rotationVector (v : Vec 4) : Vec 4 :=
  ![(v 0 + v 1 + v 2 + v 3) / 2,
    (v 0 - v 1 + v 2 - v 3) / 2,
    (-v 0 - v 1 + v 2 + v 3) / 2,
    (-v 0 + v 1 + v 2 - v 3) / 2]

private lemma rotationVector_eq (v : Vec 4) :
    middleVector (simpleVector 0 (simpleVector 3 v)) = rotationVector v := by
  ext i
  fin_cases i <;>
    simp [middleVector, simpleVector, rotationVector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

-- Coordinate formulas compose with the corresponding root permutations.
private lemma composed_val
    (a b c : Equiv.Perm F4Chevalley.Root) (f g h : Vec 4 → Vec 4)
    (hc : c = a * b)
    (ha : ∀ r, (a r).val = f r.val) (hb : ∀ r, (b r).val = g r.val)
    (hab : ∀ v, f (g v) = h v) (r : F4Chevalley.Root) :
    (c r).val = h r.val := by
  rw [hc, Equiv.Perm.mul_apply, ha, hb, hab]

private lemma relativeRotation_val (r : F4Chevalley.Root) :
    (relativeRotation r).val = rotationVector r.val :=
  composed_val middleReflection endReflection relativeRotation
    middleVector (fun v => simpleVector 0 (simpleVector 3 v)) rotationVector
    rfl middleReflection_val endReflection_val rotationVector_eq r

private def squareVector (v : Vec 4) : Vec 4 := ![v 2, v 3, -v 0, -v 1]

private lemma rotationVector_sq (v : Vec 4) :
    rotationVector (rotationVector v) = squareVector v := by
  ext i
  fin_cases i <;>
    simp [rotationVector, squareVector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma relativeRotation_sq_val (r : F4Chevalley.Root) :
    ((relativeRotation ^ 2) r).val = squareVector r.val :=
  composed_val relativeRotation relativeRotation (relativeRotation ^ 2)
    rotationVector rotationVector squareVector (pow_two relativeRotation)
    relativeRotation_val relativeRotation_val rotationVector_sq r

private lemma relativeRotation_cube_val (r : F4Chevalley.Root) :
    ((relativeRotation ^ 3) r).val = squareVector (rotationVector r.val) :=
  composed_val (relativeRotation ^ 2) relativeRotation (relativeRotation ^ 3)
    squareVector rotationVector (fun v => squareVector (rotationVector v))
    (pow_succ relativeRotation 2) relativeRotation_sq_val relativeRotation_val (fun _ => rfl) r

-- Use the proved coordinate formulas instead of unfolding the Weyl permutations.
attribute [local irreducible] middleReflection relativeRotation

-- Take coordinates before the finite case split, so its kernel check does not
-- expand the membership proofs of the concrete reflected roots.
private lemma val_eight (r₀ r₁ r₂ r₃ r₄ r₅ r₆ r₇ : F4Chevalley.Root) (i : Fin 8) :
    (![r₀, r₁, r₂, r₃, r₄, r₅, r₆, r₇] i).val =
      ![r₀.val, r₁.val, r₂.val, r₃.val, r₄.val, r₅.val, r₆.val, r₇.val] i := by
  fin_cases i <;> rfl

private lemma longRoot_val (i : Fin 8) :
    (longRoot i).val = RootPartition.table
      ((![(8 : Fin 24), 2, 20, 6, 12, 4, 16, 0] : Fin 8 → Fin 24) i) := by
  rw [longRoot, val_eight]
  simp only [relativeRotation_sq_val, relativeRotation_cube_val,
    relativeRotation_val, middleReflection_val, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [RootPartition.table, typeF4SimpleRoot,
      middleVector, rotationVector, squareVector,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

private def pairWordIndex : Fin 4 → Fin 8 := ![7, 1, 5, 3]
private def quartetWordIndex : Fin 4 → Fin 8 := ![0, 4, 6, 2]

private lemma pair_long (k : Support) (j : Fin (pairCount k)) :
    ((rootBlocks k).roots (.inl (j, 0))).val = longRoot (pairWordIndex (RootPartition.pairRow k j)) := by
  have h (i : Fin 4) : RootPartition.table ⟨2 * i.val, by omega⟩ =
      (longRoot (pairWordIndex i)).val := by
    rw [longRoot_val]
    fin_cases i <;> rfl
  apply Subtype.ext
  rw [rootBlocks_roots_val]
  exact h (RootPartition.pairRow k j)

private lemma quartet_long (k : Support) (j : Fin (quartetCount k)) :
    ((rootBlocks k).roots (.inr (j, 0))).val = longRoot (quartetWordIndex (RootPartition.quartetRow k j)) := by
  have h (i : Fin 4) : RootPartition.table ⟨8 + 4 * i.val, by omega⟩ =
      (longRoot (quartetWordIndex i)).val := by
    rw [longRoot_val]
    fin_cases i <;> rfl
  apply Subtype.ext
  rw [rootBlocks_roots_val]
  exact h (RootPartition.quartetRow k j)

private def layoutOfLongRoots (k : Support) (B : RootBlocks k)
    (p : Fin (pairCount k) → Fin 8) (q : Fin (quartetCount k) → Fin 8)
    (hp : ∀ j, (p j).val % 2 ≠ 0) (hq : ∀ j, (q j).val % 2 = 0)
    (hlp : ∀ j, (B.roots (.inl (j, 0))).val = longRoot (p j))
    (hlq : ∀ j, (B.roots (.inr (j, 0))).val = longRoot (q j)) :
    RootWordLayout k := by
  have hsp (j) : (B.roots (.inl (j, 1))).val = shortRoot (p j) := by
    rw [shortRoot, ← hlp j, B.pair_dual]
  have hsq (j) : (B.roots (.inr (j, 1))).val = shortRoot (q j) := by
    rw [shortRoot, ← hlq j, B.quartet_dual_zero]
  refine
    { blocks := B
      pairIndex := p
      quartetIndex := q
      pair_odd := hp
      quartet_even := hq
      pair_long := hlp
      pair_short := hsp
      pair_mixed := ?_
      pair_high := ?_
      quartet_long := hlq
      quartet_short := hsq
      quartet_mixed := ?_
      quartet_high := ?_ }
  · intro j
    rw [mixedRoot, ← hlp j, ← hsp j]
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero'
    rw [typeF4RootPairing_pairing, B.pair_dot, mul_zero]
  · intro j
    rw [highRoot, ← hlp j, ← hsp j]
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero
    rw [typeF4RootPairing_pairing, B.pair_dot, mul_zero]
  · intro j
    rw [mixedRoot, ← hlq j, ← hsq j]
    apply Subtype.ext
    rw [reflection_val, typeF4CorootScale_of_pair _ (B.quartet_long j),
      dot_comm, B.quartet_dot, B.quartet_add]
    simp [add_comm]
  · intro j
    rw [highRoot, ← hlq j, ← hsq j]
    apply Subtype.ext
    have hs : IsShortRoot (B.roots (.inr (j, 1))).val := by
      rw [← B.quartet_dual_zero]
      exact (exceptionalRootPermutation_long_iff _).mp (B.quartet_long j)
    rw [reflection_val, typeF4CorootScale_of_not_pair _ hs,
      B.quartet_dot, B.quartet_add_two]
    simp

private def rootWordLayout (k : Support) : RootWordLayout k :=
  layoutOfLongRoots k (rootBlocks k)
    (fun j => pairWordIndex (RootPartition.pairRow k j))
    (fun j => quartetWordIndex (RootPartition.quartetRow k j))
    (by
      intro j
      generalize RootPartition.pairRow k j = i
      fin_cases i <;> decide)
    (by
      intro j
      generalize RootPartition.quartetRow k j = i
      fin_cases i <;> decide)
    (pair_long k) (quartet_long k)

/-- The eight named words match the four pairs and four quartets of all
positive F₄ roots, in the existing Weyl-defined numbering. -/
public def positiveRootWordLayout : RootWordLayout .positive :=
  rootWordLayout .positive

/-- The Suzuki radical retains all four pairs and the three quartets after
the middle Levi block. -/
public def radicalRootWordLayout : RootWordLayout (.radical .suzuki) :=
  rootWordLayout (.radical .suzuki)

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
