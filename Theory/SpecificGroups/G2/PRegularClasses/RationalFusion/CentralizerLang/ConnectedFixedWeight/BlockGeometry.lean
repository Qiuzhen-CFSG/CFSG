module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedFixedWeight.Coordinates
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.AlgebraicGroup.Instance.SLConnected
public import Theory.AlgebraicGroup.Irreducible.Product
/-!
# Connected geometry of the normalized fixed-weight centralizer

Assuming that every invertible two-by-two block realizes the published octonion
formula, the centralizer of `torus 1 s`, for every `s ≠ 1`, is a regular
surjective image of `SL₂ × Gₘ`. The source is the genuine affine variety product;
its connectedness follows from irreducibility of connected algebraic groups.
Every invertible matrix is `diag(det A, 1) * B` with `det B = 1`, and the
coordinate reconstruction theorem supplies surjectivity onto the centralizer.

The block formula is polynomial in the entries and inverse determinant. Its
composition identity constructs a polynomial inverse matrix. The determinant
of this inverse matrix supplies the extra GL₈ coordinate, without expanding
an eight-by-eight determinant or assuming determinant one. The realization
assertion is the only additional hypothesis; its construction belongs to the
separate block-action development.

Source: Steinberg 8.1/8.5 and 12.5 (`refs/KGroup/GLS3/Chapter2St2.tex`),
GLS III, Sections 2.1 and 2.8 (`refs/KGroup/GLS3/chapter2.tex`). The octonion
coordinates follow the licensed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

open Theory.AlgebraicGroup Atlas.SplitOctonion
open scoped CharTwo
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
open FixedWeight
noncomputable section
set_option linter.unusedSectionVars false
namespace FixedWeight.BlockGeometry
variable {K : Type*} [Field K] [CharP K 2]

-- The same formula over a ring allows polynomial coefficients.
private def formula {R : Type*} [CommRing R] (a b c d t : R) (x : Fin 8 → R) : Fin 8 → R :=
  ![t*(a^2*x 0+a*b*(x 3+x 4)+b^2*x 7),
    a*x 1+b*x 5,
    t*(a*x 2+b*x 6),
    t*(a*c*x 0+a*d*x 3+b*c*x 4+b*d*x 7),
    t*(a*c*x 0+b*c*x 3+a*d*x 4+b*d*x 7),
    c*x 1+d*x 5,
    t*(c*x 2+d*x 6),
    t*(c^2*x 0+c*d*(x 3+x 4)+d^2*x 7)]

private def blockMatrix {R : Type*} [CommRing R] (a b c d t : R) :
    Matrix (Fin 8) (Fin 8) R := fun i j => formula a b c d t (Pi.single j 1) i

private theorem map_formula {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c d t : R) (x : Fin 8 → R) (i : Fin 8) :
    f (formula a b c d t x i) =
      formula (f a) (f b) (f c) (f d) (f t) (fun j => f (x j)) i := by
  fin_cases i <;> simp [formula]

private theorem map_blockMatrix {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c d t : R) :
    (blockMatrix a b c d t).map f = blockMatrix (f a) (f b) (f c) (f d) (f t) := by
  ext i j
  change f (formula a b c d t (Pi.single j 1) i) =
    formula (f a) (f b) (f c) (f d) (f t) (Pi.single j 1) i
  rw [map_formula]
  congr 1
  funext k
  by_cases h : j = k <;> simp [h]

private theorem blockMatrix_eq (a b c d t : K) :
    blockMatrix a b c d t = LinearMap.toMatrix' (blockLinear a b c d t) := rfl

private theorem action_comp (a b c d t e f g h u : K) (x : Carrier K) :
    blockApply a b c d t (blockApply e f g h u x) =
      blockApply (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h) (t*u) x := by
  ext i
  fin_cases i <;> simp [blockApply] <;> ring

private theorem inverse_action (a b c d t : K) (ht : (a*d+b*c)*t = 1)
    (x : Carrier K) :
    blockApply (d*t) (b*t) (c*t) (a*t) (a*d+b*c) (blockApply a b c d t x) = x := by
  rw [action_comp]
  have h₁ : d*t*a+b*t*c = 1 := by linear_combination ht
  have h₂ : d*t*b+b*t*d = 0 := by
    calc
      d*t*b+b*t*d = (d*t*b)+(d*t*b) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have h₃ : c*t*a+a*t*c = 0 := by
    calc
      c*t*a+a*t*c = (c*t*a)+(c*t*a) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have h₄ : c*t*b+a*t*d = 1 := by linear_combination ht
  rw [h₁, h₂, h₃, h₄, ht]
  ext i
  fin_cases i <;> simp [blockApply]

-- Transport the inverse action through the matrix/linear-map equivalence.
private theorem inverse_matrix (a b c d t : K) (ht : (a*d+b*c)*t = 1) :
    blockMatrix (d*t) (b*t) (c*t) (a*t) (a*d+b*c) * blockMatrix a b c d t = 1 := by
  simp only [blockMatrix_eq, ← LinearMap.toMatrix'_mul, ← LinearMap.toMatrix'_one]
  congr 1
  apply LinearMap.ext
  intro x
  exact inverse_action a b c d t ht x

variable [IsAlgClosed K]

private abbrev parameterVariety (K : Type*) [Field K] [IsAlgClosed K] :=
  Variety.prod (slVariety K 2) (dVariety K 1)

private theorem parameters_connected : Variety.IsConnected (parameterVariety K) := by
  have h := prodSet_irreducible_of_irreducible
    (connectedAlgebraicGroup_irreducible _ (slVariety_isConnected (k := K) 2))
    (connectedAlgebraicGroup_irreducible _ (dVariety_isConnected (k := K) 1))
  have he : Variety.prodSet
      (Set.univ : Set (Variety.Point (slVariety K 2)))
      (Set.univ : Set (Variety.Point (dVariety K 1))) = Set.univ := by
    ext z
    simp [Variety.prodSet]
  rw [he] at h
  exact h.isConnected

private def entryPoly (i j : Fin 2) : MvPolynomial (parameterVariety K).Coordinates K :=
  MvPolynomial.X (Sum.inl (ULift.up (i,j)))

private def unitPoly : MvPolynomial (parameterVariety K).Coordinates K :=
  MvPolynomial.X (Sum.inr (Sum.inl (ULift.up (0 : Fin 1))))

private def invPoly : MvPolynomial (parameterVariety K).Coordinates K :=
  MvPolynomial.X (Sum.inr (Sum.inr (ULift.up (0 : Fin 1))))

private def parameterPolynomials : Matrix (Fin 2) (Fin 2)
    (MvPolynomial (parameterVariety K).Coordinates K) :=
  !![unitPoly * entryPoly 0 0, unitPoly * entryPoly 0 1;
    entryPoly 1 0, entryPoly 1 1]

private def parameterMatrix (z : Variety.Point (parameterVariety K)) :
    Matrix (Fin 2) (Fin 2) K :=
  (parameterPolynomials (K := K)).map (MvPolynomial.eval z.val)

private theorem parameter_det (z : Variety.Point (parameterVariety K)) :
    (parameterMatrix z).det = evalPolynomial z.val unitPoly := by
  let B := slPointMatrix 2 (Variety.prodPointEquiv _ _ z).1
  have hB : B.det = 1 := slPoint_det_eq_one 2 _
  have h : (parameterMatrix z).det = evalPolynomial z.val unitPoly * B.det := by
    simp [Matrix.det_fin_two, parameterMatrix, parameterPolynomials, entryPoly,
      unitPoly, evalPolynomial, B, slPointMatrix, Variety.prodPointEquiv]
    ring
  rw [h, hB, mul_one]

private theorem parameter_det_ne (z : Variety.Point (parameterVariety K)) :
    (parameterMatrix z).det ≠ 0 := by
  rw [parameter_det]
  simpa [unitPoly, evalPolynomial, dPointEntry, Variety.prodPointEquiv] using
    (dPoint_entry_isUnit 1 (Variety.prodPointEquiv _ _ z).2 0).ne_zero

private theorem parameter_det_inv (z : Variety.Point (parameterVariety K)) :
    (parameterMatrix z).det⁻¹ = evalPolynomial z.val invPoly := by
  rw [parameter_det]
  simpa [unitPoly, invPoly, evalPolynomial, dPointEntry, dPointEntryInv,
    Variety.prodPointEquiv] using dPoint_entry_inv 1 (Variety.prodPointEquiv _ _ z).2 0

private theorem parameterMatrix_surjective (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A.det ≠ 0) : ∃ z : Variety.Point (parameterVariety K), parameterMatrix z = A := by
  let B : Matrix (Fin 2) (Fin 2) K := !![A.det⁻¹*A 0 0, A.det⁻¹*A 0 1; A 1 0, A 1 1]
  have hB : B.det = 1 := by
    calc
      B.det = A.det⁻¹ * A.det := by simp [B, Matrix.det_fin_two]; ring
      _ = 1 := inv_mul_cancel₀ hA
  let z := (Variety.prodPointEquiv (slVariety K 2) (dVariety K 1)).symm
    ((slPointEquiv 2).symm ⟨B,hB⟩, (dPointEquiv 1).symm (fun _ => Units.mk0 A.det hA))
  refine ⟨z, ?_⟩
  have hentry (i j : Fin 2) :
      ((slPointEquiv (k := K) 2).symm ⟨B,hB⟩).val (ULift.up (i,j)) = B i j := by
    exact congrArg (fun C : Matrix.SpecialLinearGroup (Fin 2) K => C.val i j)
      ((slPointEquiv (k := K) 2).apply_symm_apply ⟨B,hB⟩)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parameterMatrix, parameterPolynomials, unitPoly, entryPoly,
      z, Variety.prodPointEquiv, dPointEquiv, hentry, B, hA]


private def chosenPoint
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) (z : Variety.Point (parameterVariety K)) :
    Variety.Point (centralizerVariety (torus 1 s)) :=
  (centralizerPointEquiv (torus 1 s)).symm
    ⟨(hrealize (parameterMatrix z) (parameter_det_ne z)).choose,
      mem_centralizer_of_blockApply s
        (hrealize (parameterMatrix z) (parameter_det_ne z)).choose_spec⟩

private theorem chosenPoint_action
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) (z : Variety.Point (parameterVariety K)) (x : Carrier K) :
    (centralizerPointEquiv (torus 1 s) (chosenPoint hrealize s z)).val.val x =
      blockApply (parameterMatrix z 0 0) (parameterMatrix z 0 1)
        (parameterMatrix z 1 0) (parameterMatrix z 1 1)
        (evalPolynomial z.val invPoly) x := by
  simp only [chosenPoint, MulEquiv.apply_symm_apply]
  rw [← parameter_det_inv]
  exact (hrealize (parameterMatrix z) (parameter_det_ne z)).choose_spec x

private theorem chosenPoint_matrix
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) (z : Variety.Point (parameterVariety K)) :
    (FieldExtension.coordinateMatrix
      (centralizerPointEquiv (torus 1 s) (chosenPoint hrealize s z)).val :
      Matrix (Fin 8) (Fin 8) K) =
      blockMatrix (parameterMatrix z 0 0) (parameterMatrix z 0 1)
        (parameterMatrix z 1 0) (parameterMatrix z 1 1)
        (evalPolynomial z.val invPoly) := by
  ext i j
  rw [coordinateMatrix_entry, chosenPoint_action]
  rfl

private def actionPolynomials : Matrix (Fin 8) (Fin 8)
    (MvPolynomial (parameterVariety K).Coordinates K) :=
  blockMatrix (parameterPolynomials 0 0) (parameterPolynomials 0 1)
    (parameterPolynomials 1 0) (parameterPolynomials 1 1) invPoly

-- Their determinant is the inverse-determinant coordinate of the image.
private def inversePolynomials : Matrix (Fin 8) (Fin 8)
    (MvPolynomial (parameterVariety K).Coordinates K) :=
  let A := parameterPolynomials (K := K)
  blockMatrix (A 1 1 * invPoly) (A 0 1 * invPoly)
    (A 1 0 * invPoly) (A 0 0 * invPoly) (A 0 0 * A 1 1 + A 0 1 * A 1 0)

private theorem eval_actionPolynomials (z : Variety.Point (parameterVariety K)) :
    (actionPolynomials (K := K)).map (MvPolynomial.eval z.val) =
      blockMatrix (parameterMatrix z 0 0) (parameterMatrix z 0 1)
        (parameterMatrix z 1 0) (parameterMatrix z 1 1)
        (evalPolynomial z.val invPoly) := by
  exact map_blockMatrix (MvPolynomial.eval z.val) _ _ _ _ _

private theorem eval_inversePolynomials (z : Variety.Point (parameterVariety K)) :
    (inversePolynomials (K := K)).map (MvPolynomial.eval z.val) *
      (actionPolynomials (K := K)).map (MvPolynomial.eval z.val) = 1 := by
  rw [eval_actionPolynomials]
  unfold inversePolynomials
  rw [map_blockMatrix]
  simp only [map_mul, map_add]
  apply inverse_matrix
  change ((parameterMatrix z 0 0 * parameterMatrix z 1 1 +
    parameterMatrix z 0 1 * parameterMatrix z 1 0) * evalPolynomial z.val invPoly) = 1
  rw [← CharTwo.sub_eq_add, ← Matrix.det_fin_two, ← parameter_det_inv]
  exact mul_inv_cancel₀ (parameter_det_ne z)

private def blockMorphism
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) : Variety.Morphism (parameterVariety K)
      (centralizerVariety (torus 1 s)) where
  toFun := chosenPoint hrealize s
  regular := by
    rintro (⟨i,j⟩ | ⟨⟩)
    · refine ⟨actionPolynomials i j, fun z => ?_⟩
      rw [← centralizerPointEquiv_entry, chosenPoint_matrix, ← eval_actionPolynomials]
      rfl
    · refine ⟨inversePolynomials.det, fun z => ?_⟩
      rw [centralizerPointEquiv_scalar, chosenPoint_matrix, ← eval_actionPolynomials]
      have hd := congrArg Matrix.det (eval_inversePolynomials z)
      rw [Matrix.det_mul, Matrix.det_one] at hd
      rw [← eq_inv_of_mul_eq_one_left hd]
      exact (RingHom.map_det (MvPolynomial.eval z.val) inversePolynomials).symm

private theorem blockMorphism_surjective
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) (hs : s ≠ 1) : Function.Surjective (blockMorphism hrealize s).toFun := by
  intro p
  let g := (centralizerPointEquiv (torus 1 s) p).val
  obtain ⟨hdet,hg⟩ := block_coordinates s hs (centralizerPointEquiv (torus 1 s) p).property
  obtain ⟨z,hz⟩ := parameterMatrix_surjective (positiveBlock g) hdet
  refine ⟨z, ?_⟩
  apply (centralizerPointEquiv (torus 1 s)).injective
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (centralizerPointEquiv (torus 1 s) (chosenPoint hrealize s z)).val.val x = g.val x
  rw [chosenPoint_action, ← parameter_det_inv, hz]
  exact (hg x).symm

end FixedWeight.BlockGeometry

/-- The normalized nonidentity torus centralizer is connected whenever every
invertible two-dimensional block has the explicit octonion realization. -/
public theorem centralizer_connected_normalized_of_block_action
    {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]
    (hrealize : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det ≠ 0 →
      ∃ g : Model K, ∀ x : Carrier K,
        g.val x = blockApply (A 0 0) (A 0 1) (A 1 0) (A 1 1) A.det⁻¹ x)
    (s : Kˣ) (hs : s ≠ 1) : Variety.IsConnected (centralizerVariety (torus 1 s)) := by
  have h := (FixedWeight.BlockGeometry.parameters_connected (K := K)).image
    (FixedWeight.BlockGeometry.blockMorphism hrealize s).toFun
    (FixedWeight.BlockGeometry.blockMorphism hrealize s).continuous.continuousOn
  change _root_.IsConnected (Set.univ : Set (Variety.Point (centralizerVariety (torus 1 s))))
  rw [Set.image_univ,
    Set.range_eq_univ.mpr (FixedWeight.BlockGeometry.blockMorphism_surjective hrealize s hs)] at h
  exact h

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang
