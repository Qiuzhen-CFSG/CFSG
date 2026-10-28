module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Descent

/-!
# Invariance of the unitary exterior-square descent space

The actual antidiagonal SU₄ action commutes with the semilinear involution
which conjugates all six bivector coordinates and exchanges 03 with 12.
Its fixed space is exactly the norm-model descent space.

The proof compares two pairings on the exterior square. Determinant one
preserves the polarization of the Pfaffian. The unitary equation preserves
the exterior Hermitian pairing. Composing the first pairing with the
semilinear involution gives the second; nondegeneracy therefore forces
commutation. This proves invariance for every positive exponent, including
the field of order four, and supplies the previously conditional faithful
orthogonal action without any group-image or order premise.

Sources: GLS3 §2.7 (the actual special unitary matrix convention);
Aschbacher–Smith A.2.18, printed p.40, and Theorem D, pp.1078–1079,
for the minus-six/unitary-four comparison's classification consumers.
The compound action and its Pfaffian identity are the existing attributed
ATLAS port; no additional ATLAS source is copied here.
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors

private theorem exterior_transpose {F : Type*} [CommRing F]
    (A : Matrix (Fin 4) (Fin 4) F) (w z : Six F) :
    dotProduct (exteriorMap A w) z = dotProduct w (exteriorMap A.transpose z) := by
  have ht : compound A.transpose = (compound A).transpose := by
    ext i j
    simp [compound, Matrix.transpose_apply, mul_comm]
  simp only [exteriorMap, Matrix.toLin'_apply, ht]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem exterior_conjugate {F : Type*} [CommRing F]
    (σ : F ≃+* F) (A : Matrix (Fin 4) (Fin 4) F) (w : Six F) :
    (fun i => σ (exteriorMap A w i)) = exteriorMap (A.map σ) (fun i => σ (w i)) := by
  ext i
  simp [exteriorMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, compound]

private def pairing {F : Type*} [CommRing F] (w z : Six F) : F :=
  w 0 * z 5 + w 1 * z 4 + w 2 * z 3 + w 3 * z 2 + w 4 * z 1 + w 5 * z 0

private theorem pairing_polar {F : Type*} [CommRing F] [CharP F 2] (w z : Six F) :
    pairing w z = pfaffian (w + z) - pfaffian w - pfaffian z := by
  simp only [pairing, pfaffian_apply, Pi.add_apply, CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem pairing_ext {F : Type*} [CommRing F] {w z : Six F}
    (h : ∀ t, pairing w t = pairing z t) : w = z := by
  ext i
  fin_cases i
  · simpa [pairing] using h (Pi.single 5 1)
  · simpa [pairing] using h (Pi.single 4 1)
  · simpa [pairing] using h (Pi.single 3 1)
  · simpa [pairing] using h (Pi.single 2 1)
  · simpa [pairing] using h (Pi.single 1 1)
  · simpa [pairing] using h (Pi.single 0 1)

variable (n : ℕ) [NeZero n]

private def twist (w : Six (Field n)) : Six (Field n) :=
  ![conjugation n (w 0), conjugation n (w 1), conjugation n (w 3),
    conjugation n (w 2), conjugation n (w 4), conjugation n (w 5)]

omit [NeZero n] in
private theorem exterior_gram (w : Six (Field n)) :
    exteriorMap (UnitaryFourFlag.gram (Field n)) w =
      ![w 5, w 4, w 2, w 3, w 1, w 0] := by
  ext i
  fin_cases i <;>
    simp [exteriorMap, compound, first, second, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryFourFlag.gram,
      CharTwo.neg_eq]

omit [NeZero n] in
private theorem pairing_twist (w z : Six (Field n)) :
    pairing (twist n w) z = dotProduct (fun i => conjugation n (w i))
      (exteriorMap (UnitaryFourFlag.gram (Field n)) z) := by
  rw [exterior_gram]
  simp [pairing, twist, dotProduct, Fin.sum_univ_succ]
  ring

private theorem exterior_pairing (g : SU n) (w z : Six (Field n)) :
    pairing (exterior n g w) (exterior n g z) = pairing w z := by
  rw [pairing_polar, ← map_add, exterior_pfaffian, exterior_pfaffian,
    exterior_pfaffian, ← pairing_polar]

private theorem exterior_hermitian (g : SU n) (w z : Six (Field n)) :
    pairing (twist n (exterior n g w)) (exterior n g z) = pairing (twist n w) z := by
  rw [pairing_twist, pairing_twist, exterior_apply, exterior_apply, exterior_conjugate,
    exterior_transpose]
  have hu : (g.val.val.map (conjugation n)).transpose * UnitaryFourFlag.gram (Field n) *
      g.val.val = UnitaryFourFlag.gram (Field n) := g.property.1
  have he := congrArg (fun A => exteriorMap A z) hu
  simp only [exteriorMap_mul, LinearMap.comp_apply] at he
  rw [he]

private theorem twist_exterior (g : SU n) (w : Six (Field n)) :
    twist n (exterior n g w) = exterior n g (twist n w) := by
  apply pairing_ext
  intro z
  obtain ⟨t, rfl⟩ := (exterior n g).surjective z
  rw [exterior_hermitian, exterior_pairing]

private theorem mem_descentSpace_iff_twist (w : Six (Field n)) :
    w ∈ descentSpace n ↔ twist n w = w := by
  rw [mem_descentSpace]
  constructor
  · rintro ⟨h0, h1, h4, h5, h23⟩
    have h32 : conjugation n (w 3) = w 2 := by
      rw [← h23, Representation.OrthogonalFourMinus.FiniteModel.conjugation_involutive]
    ext i
    fin_cases i <;> simp [twist, h0, h1, h4, h5, h23, h32]
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 4, congrFun h 5, congrFun h 3⟩

/-- Every special unitary matrix preserves the actual fixed-field descent space. -/
theorem exterior_mem_descentSpace (g : SU n) {w : Six (Field n)}
    (hw : w ∈ descentSpace n) : exterior n g w ∈ descentSpace n := by
  apply (mem_descentSpace_iff_twist n _).mpr
  rw [twist_exterior, (mem_descentSpace_iff_twist n _).mp hw]

/-- The concrete unitary exterior square descends for every positive exponent. -/
theorem descends : Descends n := by
  intro g v
  exact exterior_mem_descentSpace n g ⟨v, rfl⟩

/-- The unconditional orthogonal action on the six-dimensional norm model. -/
def exteriorOrthogonalAction : SU n →* FullOrthogonal n :=
  orthogonalAction n (descends n)

/-- Its action is literally the restriction of the second compound matrices. -/
theorem exteriorOrthogonalAction_intertwines (g : SU n) (v : Space n) :
    toBivector n ((exteriorOrthogonalAction n g).val v) =
      exterior n g (toBivector n v) :=
  orthogonalAction_intertwines n (descends n) g v

/-- The descended action is faithful, with no additional group-theoretic premise. -/
theorem exteriorOrthogonalAction_injective : Function.Injective (exteriorOrthogonalAction n) :=
  orthogonalAction_injective n (descends n)

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
