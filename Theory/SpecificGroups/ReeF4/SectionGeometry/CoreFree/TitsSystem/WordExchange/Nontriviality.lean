module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientCalculations
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.UniformWords
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.FixedSeparation

/-!
# Nontriviality of the concrete relative Ree reflections

The end-node word negates simple root 0, and the middle-node word negates
simple root 1. The existing fixed positive coordinate witnesses detect these
roots on Cartan columns. Comparing `(v x v) v = v x` shows that `v x v`
cannot be height triangular: its vanishing negative-root/Cartan row would
contradict the nonzero coordinate of `x`. Every element of the full fixed
Borel is height triangular, including its torus factor.

The calculation uses the actual fixed matrices and proves the BN
nontriviality witness without a quotient or any normalizer hypothesis.
Source: GLS3 2.3.4(b), 2.3.5 and 2.4.3,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def sideNode : Side → Fin 4 | .linear => 0 | .suzuki => 1

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) *
        dot r.val (typeF4SimpleRoot i)) • typeF4SimpleRoot i := by
  change typeF4RootPairing.root _ = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing]
  rfl

private theorem side_negates (s : Side) : typeF4RootPairing.weylGroupToPerm (rootWord (sideWord s))
    (typeF4SimpleRootIndex (sideNode s)) = -typeF4SimpleRootIndex (sideNode s) := by
  apply Subtype.ext
  change typeF4RootPairing.root _ = typeF4RootPairing.root _
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]
  cases s with
  | linear =>
    change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3)
        (typeF4SimpleRootIndex 0))).val = -(typeF4SimpleRootIndex 0).val
    ext i; fin_cases i <;>
      norm_num [reflection_val, typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
        Matrix.cons_val_two, Matrix.cons_val_three]
  | suzuki =>
    change (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 1)
          (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 2)
            (typeF4SimpleRootIndex 1))))).val = -(typeF4SimpleRootIndex 1).val
    ext i; fin_cases i <;>
      norm_num [reflection_val, typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, dot, Fin.sum_univ_four, basisVector,
        Matrix.cons_val_two, Matrix.cons_val_three]

private theorem negative_simple_degree (i : Fin 4) :
    basisDegree (.inr (-typeF4SimpleRootIndex i)) = -1 := by
  have hp (j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) = typeF4CartanMatrix i j :=
    typeF4RootPairing_base_cartan_apply i j
  simp only [basisDegree, chevalleyBasisWeight, RootPairing.indexNeg_neg,
    RootPairing.pairingIn_reflectionPerm_self_left, hp]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]

private theorem borel_triangular {m : ℕ} {x : Model m} (hx : x ∈ borel m) :
    Overlap.IsHeightTriangular (toSplitGroup m x) := by
  exact Overlap.inf_splitParabolic_heightTriangular m
    (le_of_eq (splitTorus_eq_diagonalTorus m))
    ⟨borel_le_parabolic m .suzuki hx, borel_le_parabolic m .linear hx⟩

private def matrix (m : ℕ) : Model m →* Matrix F4Chevalley.BasisIndex
    F4Chevalley.BasisIndex (CoefficientField m) :=
  (Units.coeHom _).comp ((Subgroup.subtype _).comp (toSplitGroup m))

/-- Each actual relative reflection conjugates a fixed positive element outside
the full fixed Borel, over every Ree coefficient field. -/
theorem weylLift_borel_conjugation_witness (m : ℕ) (s : Side) : ∃ b ∈ borel m,
    weylLift m s * b * weylLift m s ∉ borel m := by
  classical
  let n := weylLift m s
  let r := typeF4SimpleRootIndex (sideNode s)
  let e := typeF4RootPairing.weylGroupToPerm (rootWord (sideWord s))
  have hmono : RootMonomial (matrix m n) e (fun _ => 1) := by
    change RootMonomial (toSplitGroup m (weylLift m s)).val.val e (fun _ => 1)
    rw [toSplitGroup_weylLift]
    exact QuotientGeometry.simpleWord_rootMonomial m (sideWord s)
  have hn : n * n = 1 := by simpa only [pow_two] using weylLift_sq m s
  obtain ⟨x, hx, j, hj⟩ := Overlap.FixedWitnesses.exists_simple_coordinate m (sideNode s)
  refine ⟨x, unipotent_le_borel m hx, ?_⟩
  intro hB
  have hzero (q : typeF4RootPairing_base.support) :
      matrix m (n * x * n) (.inr (e r)) (.inl q) = 0 := by
    apply borel_triangular hB
    rw [show e r = -r from side_negates s, basisDegree_cartan]
    change basisDegree (.inr (-typeF4SimpleRootIndex (sideNode s))) < 0
    rw [negative_simple_degree]; decide
  have he : matrix m (n * x * n) * matrix m n = matrix m n * matrix m x := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc, mul_assoc, hn, mul_one]
  have hleft : (matrix m (n * x * n) * matrix m n) (.inr (e r)) (.inl j) = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    cases z with
    | inl q => rw [hzero q, zero_mul]
    | inr q => rw [hmono.2 q j, mul_zero]
  have hright : (matrix m n * matrix m x) (.inr (e r)) (.inl j) =
      matrix m x (.inr r) (.inl j) := by
    rw [Matrix.mul_apply]
    simp only [rootMonomial_row hmono, Equiv.symm_apply_apply, Units.val_one,
      ite_mul, one_mul, zero_mul]
    simp
  have he' := congrArg (fun A => A (.inr (e r)) (.inl j)) he
  rw [hleft, hright] at he'
  exact hj he'.symm

end ReeF4.SectionGeometry.BNPair
