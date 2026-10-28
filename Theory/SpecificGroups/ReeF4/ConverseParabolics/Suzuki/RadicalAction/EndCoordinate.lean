module
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.CentralizerReduction
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.RadicalAction.RootCurve
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation.Torus

/-!
# A degree-one character of the Suzuki Ree radical

The first-end-root row and adjacent Cartan column have degrees one and zero.
Products of two strictly raising matrices have zero in this entry. Thus the
entry is additive on the actual radical and vanishes on its own commutator
subgroup. On the fixed end-root curve the same entry is exactly its parameter.

The concrete full fixed torus with simple-root characters `(b,c)` scales this
curve by `b`. Consequently trivial action on the radical abelianization forces
`b = 1`; in particular it detects the complementary torus `torusElement b 1`.
This calculation does not assume faithful action or a centralizer conclusion.

Source: GLS3, Theorem 2.6.5(e,g) and §3.2, and the Suzuki local factor in
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open scoped commutatorElement
namespace ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
open Grading LargeLocalSeeds Parabolics.OuterLocal.SuzukiCommutators
open FullLeviRepresentation
variable {m : ℕ}

private abbrev rootRow : F4Chevalley.BasisIndex := .inr (typeF4SimpleRootIndex 0)
private abbrev cartanColumn : F4Chevalley.BasisIndex := .inl (typeF4RootPairing_baseEquiv 1)

/-- The Cartan-to-first-end-root entry of the actual Ree matrix. -/
def endCoordinate (m : ℕ) (x : Model m) : CoefficientField m :=
  modelMatrix m x rootRow cartanColumn

@[simp] theorem endCoordinate_one (m : ℕ) : endCoordinate m 1 = 0 := by
  simp [endCoordinate, rootRow, cartanColumn]

private theorem raises_mul_entry {A B : MatrixCarrier m}
    (hA : Raises A) (hB : Raises B) : (A * B) rootRow cartanColumn = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hi : basisDegree rootRow = 1 := by simp [rootRow, rootDegree_simple]
  have hj : basisDegree cartanColumn = 0 := by simp [cartanColumn]
  by_cases hk : basisDegree rootRow ≤ basisDegree k
  · rw [hA _ _ hk, zero_mul]
  · rw [hB _ _ (by omega), mul_zero]

/-- Degree one turns multiplication in the radical into addition of this entry. -/
theorem endCoordinate_mul {x y : Model m}
    (hx : x ∈ radical m .suzuki) (hy : y ∈ radical m .suzuki) :
    endCoordinate m (x * y) = endCoordinate m x + endCoordinate m y := by
  have hx' : x ∈ Parabolics.radical m .suzuki := by rwa [← suzuki_radical_eq_rootRadical]
  have hy' : y ∈ Parabolics.radical m .suzuki := by rwa [← suzuki_radical_eq_rootRadical]
  have he := raises_mul_entry (radical_raises x hx') (radical_raises y hy')
  rw [sub_mul, mul_sub, one_mul, mul_one] at he
  simp only [Matrix.sub_apply, Matrix.one_apply, rootRow, cartanColumn,
    reduceCtorEq, ↓reduceIte] at he
  change modelMatrix m (x * y) _ _ = _
  rw [modelMatrix_mul]
  dsimp [endCoordinate]
  linear_combination he

/-- The first end-root coordinate as an additive character of the radical. -/
def endCoordinateHom (m : ℕ) : radical m .suzuki →* Multiplicative (CoefficientField m) where
  toFun x := Multiplicative.ofAdd (endCoordinate m x.val)
  map_one' := endCoordinate_one m
  map_mul' x y := endCoordinate_mul x.property y.property


/-- Every commutator of radical elements has zero first end-root coordinate. -/
theorem endCoordinate_commutator {x : Model m}
    (hx : x ∈ ⁅radical m .suzuki, radical m .suzuki⁆) : endCoordinate m x = 0 := by
  rw [← Subgroup.map_subtype_commutator] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hh := Abelianization.commutator_subset_ker (endCoordinateHom m)
  exact hh hy

/-- The fixed end-root curve, in the ambient Ree model. -/
@[expose] def endCurve (m : ℕ) (t : CoefficientField m) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (endRootElement (canonicalLocalBlockInput m) t).val

theorem endCurve_mem (m : ℕ) (t : CoefficientField m) :
    endCurve m t ∈ radical m .suzuki := by
  change (endCurve m t).val ∈ splitRadical m .suzuki
  rw [endCurve, LocalBlockInput.modelEquiv_coe]
  exact endRootWord_mem_radical m t

@[simp] theorem endCoordinate_endCurve (m : ℕ) (t : CoefficientField m) :
    endCoordinate m (endCurve m t) = t := by
  unfold endCoordinate modelMatrix endCurve
  rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
  exact SuzukiRadicalAction.endRootWord_entry m t

@[simp] theorem endCurve_add (m : ℕ) (s t : CoefficientField m) :
    endCurve m (s + t) = endCurve m s * endCurve m t := by
  simp only [endCurve, endRootElement_add, Subgroup.coe_mul, map_mul]

@[simp] theorem endCurve_neg (m : ℕ) (t : CoefficientField m) :
    endCurve m (-t) = (endCurve m t)⁻¹ := by
  simp only [endCurve, endRootElement_neg, Subgroup.coe_inv, map_inv]

/-- An actor trivial on the radical abelianization cannot scale this curve nontrivially. -/
theorem scalar_eq_one_of_actsTrivially (g : Model m) (a : CoefficientField m)
    (hg : ActsTriviallyOnRadicalAbelianization m g)
    (hscale : ∀ t, g * endCurve m t * g⁻¹ = endCurve m (a * t)) : a = 1 := by
  have hc := endCoordinate_commutator (hg (endCurve m 1) (endCurve_mem m 1))
  have he : ⁅g, endCurve m 1⁆ = endCurve m (a - 1) := by
    rw [commutatorElement_def, hscale, mul_one, ← endCurve_neg, ← endCurve_add, sub_eq_add_neg]
  rw [he, endCoordinate_endCurve] at hc
  exact sub_eq_zero.mp hc


open LocalBlockInput.PairRigidity BlockParameters BlockParameters.FieldRecovery

private def matrixHom (m : ℕ) : Model m →* MatrixUnits m :=
  (SplitGroup m).subtype.comp (toSplitGroup m)

private theorem matrixHom_injective (m : ℕ) : Function.Injective (matrixHom m) :=
  Subtype.val_injective.comp (toSplitGroup_injective m)

private theorem matrixHom_endCurve (t : CoefficientField m) :
    matrixHom m (endCurve m t) = (endRootWord m t).val := by
  change (toSplitGroup m (endCurve m t)).val = _
  rw [toSplitGroup_apply, endCurve, LocalBlockInput.modelEquiv_coe]
  rfl

private theorem matrixHom_torus (b c : (CoefficientField m)ˣ) :
    matrixHom m (torusElement b c) = (torusMatrix (blockTorus b c))⁻¹ :=
  torusElement_matrix b c

/-- The first long-root character is the scalar on the fixed end-root curve. -/
theorem torusElement_endCurve_scaling (b c : (CoefficientField m)ˣ)
    (t : CoefficientField m) :
    torusElement b c * endCurve m t * (torusElement b c)⁻¹ =
      endCurve m ((b : CoefficientField m) * t) := by
  apply matrixHom_injective m
  simp only [map_mul, map_inv, matrixHom_torus, matrixHom_endCurve, inv_inv]
  simp only [endRootWord, Subgroup.coe_mul, rootGeneratorInGroup_coe]
  calc
    _ = ((torusMatrix (blockTorus b c))⁻¹ *
        F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t * torusMatrix (blockTorus b c)) *
      ((torusMatrix (blockTorus b c))⁻¹ *
        F4Chevalley.rootCurve (typeF4SimpleRootIndex 3)
          (Parabolics.rootFieldEnd m (typeF4SimpleRootIndex 0) t) * torusMatrix (blockTorus b c)) := by group
    _ = _ := by
      rw [torusMatrix_conjugation, torusMatrix_conjugation]
      simp only [blockTorus_simple, Matrix.cons_val_zero, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
        Units.coe_map, MonoidHom.coe_coe, rootFieldEnd_simple_zero_eq_theta, map_mul]

/-- Trivial action on the radical abelianization detects the first torus character. -/
theorem torus_first_character_eq_one (b c : (CoefficientField m)ˣ)
    (h : ActsTriviallyOnRadicalAbelianization m (torusElement b c)) : b = 1 := by
  apply Units.ext
  exact scalar_eq_one_of_actsTrivially _ _ h (torusElement_endCurve_scaling b c)

/-- In particular the actual complementary torus is detected faithfully. -/
theorem complement_eq_one_of_actsTrivially (b : (CoefficientField m)ˣ)
    (h : ActsTriviallyOnRadicalAbelianization m (torusElement b 1)) :
    torusElement b 1 = 1 := by
  rw [torus_first_character_eq_one b 1 h]
  exact (torusHom m).map_one

end ReeF4.ConverseParabolics.SuzukiLevi.RadicalAction
