module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.FieldModel
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Realization

/-!
# The signed Frobenius involution on the exterior square

The six-minor action of the actual antidiagonal SU₄ commutes with
(σw₀, −σw₁, σw₃, σw₂, −σw₄, σw₅). To prove this, compare the
nondegenerate polarization of the Pfaffian with the exterior Hermitian
pairing. Determinant one preserves the former, and the unitary equation
preserves the latter. Their relation includes a minus sign, retained here
in every characteristic.

This is the invariant-space input to the minus-six realization in GLS3
§2.7 and the orthogonal reduction in Aschbacher–Smith A.2.17, pp.38–39.
It reuses the attributed ATLAS compound matrices and Pfaffian identity;
no faithfulness or model simplicity is assumed.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Geometry
open Matrix BenderSuzuki.MatrixGroups Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors

private theorem exterior_transpose {E : Type} [Field E]
    (A : Matrix (Fin 4) (Fin 4) E) (w z : Six E) :
    dotProduct (exteriorMap A w) z = dotProduct w (exteriorMap A.transpose z) := by
  have ht : compound A.transpose = (compound A).transpose := by
    ext i j
    simp [compound, Matrix.transpose_apply, mul_comm]
  simp only [exteriorMap, Matrix.toLin'_apply, ht]
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem exterior_conjugate {E : Type} [Field E]
    (σ : E ≃+* E) (A : Matrix (Fin 4) (Fin 4) E) (w : Six E) :
    (fun i => σ (exteriorMap A w i)) = exteriorMap (A.map σ) (fun i => σ (w i)) := by
  ext i
  simp [exteriorMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, compound]

private def pairing {E : Type} [Field E] (w z : Six E) : E :=
  w 0 * z 5 - w 1 * z 4 + w 2 * z 3 + w 3 * z 2 - w 4 * z 1 + w 5 * z 0

private theorem pairing_polar {E : Type} [Field E] (w z : Six E) :
    pairing w z = pfaffian (w + z) - pfaffian w - pfaffian z := by
  simp only [pairing, pfaffian_apply, Pi.add_apply]
  ring

private theorem pairing_ext {E : Type} [Field E] {w z : Six E}
    (h : ∀ t, pairing w t = pairing z t) : w = z := by
  ext i
  fin_cases i
  · simpa [pairing] using h (Pi.single 5 1)
  · simpa [pairing] using h (Pi.single 4 1)
  · simpa [pairing] using h (Pi.single 3 1)
  · simpa [pairing] using h (Pi.single 2 1)
  · simpa [pairing] using h (Pi.single 1 1)
  · simpa [pairing] using h (Pi.single 0 1)

variable (p n : ℕ) [Fact p.Prime] [NeZero n]

abbrev SU := (unitaryForm p n).specialSubgroup

def exterior : SU p n →* (Six (Extension p n) ≃ₗ[Extension p n] Six (Extension p n)) where
  toFun g := Atlas.Order20160A8.Exterior.exteriorAction
    ⟨g.val.val, congrArg Units.val g.property.2⟩
  map_one' := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six (Extension p n) →ₗ[Extension p n] Six (Extension p n) => f w)
      exteriorMap_one
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : Six (Extension p n) →ₗ[Extension p n] Six (Extension p n) => f w)
      (exteriorMap_mul g.val.val h.val.val)

@[simp] theorem exterior_apply (g : SU p n) (w : Six (Extension p n)) :
    exterior p n g w = exteriorMap g.val.val w := rfl

theorem exterior_pfaffian (g : SU p n) (w : Six (Extension p n)) :
    pfaffian (exterior p n g w) = pfaffian w := by
  have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
  rw [exterior_apply, pfaffian_exteriorMap, hd, one_mul]

def signedTwist (w : Six (Extension p n)) : Six (Extension p n) :=
  ![conjugation p n (w 0), -conjugation p n (w 1), conjugation p n (w 3),
    conjugation p n (w 2), -conjugation p n (w 4), conjugation p n (w 5)]

omit [NeZero n] in
private theorem exterior_gram (w : Six (Extension p n)) :
    exteriorMap (UnitaryFourFlag.gram (Extension p n)) w =
      ![-w 5, -w 4, -w 2, -w 3, -w 1, -w 0] := by
  ext i
  fin_cases i <;>
    simp [exteriorMap, compound, first, second, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryFourFlag.gram]

omit [NeZero n] in
private theorem pairing_twist (w z : Six (Extension p n)) :
    pairing (signedTwist p n w) z = -dotProduct (fun i => conjugation p n (w i))
      (exteriorMap (UnitaryFourFlag.gram (Extension p n)) z) := by
  rw [exterior_gram]
  simp [pairing, signedTwist, dotProduct, Fin.sum_univ_succ]
  ring

private theorem exterior_pairing (g : SU p n) (w z : Six (Extension p n)) :
    pairing (exterior p n g w) (exterior p n g z) = pairing w z := by
  rw [pairing_polar, ← map_add, exterior_pfaffian, exterior_pfaffian,
    exterior_pfaffian, ← pairing_polar]

private theorem exterior_hermitian (g : SU p n) (w z : Six (Extension p n)) :
    pairing (signedTwist p n (exterior p n g w)) (exterior p n g z) =
      pairing (signedTwist p n w) z := by
  rw [pairing_twist, pairing_twist, exterior_apply, exterior_apply, exterior_conjugate,
    exterior_transpose]
  have hu : (g.val.val.map (conjugation p n)).transpose * UnitaryFourFlag.gram (Extension p n) *
      g.val.val = UnitaryFourFlag.gram (Extension p n) := g.property.1
  have he := congrArg (fun A => exteriorMap A z) hu
  simp only [exteriorMap_mul, LinearMap.comp_apply] at he
  rw [he]

theorem signedTwist_exterior (g : SU p n) (w : Six (Extension p n)) :
    signedTwist p n (exterior p n g w) = exterior p n g (signedTwist p n w) := by
  apply pairing_ext
  intro z
  obtain ⟨t, rfl⟩ := (exterior p n g).surjective z
  rw [exterior_hermitian, exterior_pairing]

end ClassicalOrthogonal.Minus.OddSixComparison.Geometry
