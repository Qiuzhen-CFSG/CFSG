module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.Model
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
import all Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence

/-!
# Field transport preserving the actual SU₃ Borel

An isomorphism of order-25 matrix fields commutes with fifth-power
conjugation. Entrywise transport preserves the antidiagonal Gram matrix,
the determinant-one condition, each root matrix, and each torus matrix.
It therefore identifies the literal pairs `(SU₃,B)` in both directions.
The representation's coefficient field is never changed.

The implementation import of `FiniteFieldEquivalence` is deliberate: this
extension proves matrix formulas for its existing coefficient equivalence
without changing that shared module. No private name occurs in the public
statements. This supplies the model comparison in the trivial principal-series
approach to Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3.
-/

@[expose] public section

open scoped MonoidAlgebra
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
open BenderSuzuki.External BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open Matrix
section Coefficients
variable {E F : Type*} [Field E] [Field F]

private theorem coefficient_borel_le (e : E ≃+* F)
    (J : HermitianForm 3 E) (L : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hL : L.form = !![0,0,1;0,1,0;1,0,0])
    (hc : ∀ x, e (J.conj x) = L.conj (e x)) (hf : J.form.map e = L.form) :
    specialBorel J hJ ≤ (specialBorel L hL).comap
      (coefficientSpecialEquiv e J L hc hf).toMonoidHom := by
  apply sup_le
  · rintro x ⟨z, rfl⟩
    let z' : hermitianUnipotentCoord L := ⟨(e z.val.1, e z.val.2), by
      change e z.val.2 + L.conj (e z.val.2) + e z.val.1 * L.conj (e z.val.1) = 0
      rw [← hc, ← hc, ← map_mul, ← map_add, ← map_add, z.property, map_zero]⟩
    change coefficientSpecialEquiv e J L hc hf (hermitianUnipotentSU J hJ z) ∈ specialBorel L hL
    apply (show specialRoot L hL ≤ specialBorel L hL from le_sup_left)
    refine ⟨z', ?_⟩
    apply Subtype.ext
    apply Units.ext
    change hermitianUnipotentMatrix L z' = (hermitianUnipotentMatrix J z).map e
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix, z', hc]
  · rintro x ⟨k, rfl⟩
    change coefficientSpecialEquiv e J L hc hf (hermitianTorusSU J hJ k) ∈ specialBorel L hL
    apply (show specialTorus L hL ≤ specialBorel L hL from le_sup_right)
    refine ⟨Units.map e.toMonoidHom k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change hermitianTorusMatrix L (Units.map e.toMonoidHom k) = (hermitianTorusMatrix J k).map e
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianTorusMatrix, hc]

/-- Entrywise field transport preserves the actual root-and-torus Borel. -/
theorem coefficient_borel_iff (e : E ≃+* F)
    (J : HermitianForm 3 E) (L : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hL : L.form = !![0,0,1;0,1,0;1,0,0])
    (hc : ∀ x, e (J.conj x) = L.conj (e x)) (hf : J.form.map e = L.form)
    (g : J.specialSubgroup) :
    coefficientSpecialEquiv e J L hc hf g ∈ specialBorel L hL ↔ g ∈ specialBorel J hJ := by
  have hc' (x : F) : e.symm (L.conj x) = J.conj (e.symm x) := by
    apply e.injective
    simpa only [e.apply_symm_apply] using (hc (e.symm x)).symm
  have hf' : L.form.map e.symm = J.form := by
    rw [← hf]
    ext i j
    exact e.symm_apply_apply _
  constructor
  · intro hg
    have hm := coefficient_borel_le e.symm L J hL hJ hc' hf' hg
    have hi : coefficientSpecialEquiv e.symm L J hc' hf'
        (coefficientSpecialEquiv e J L hc hf g) = g := by
      ext i j
      exact e.symm_apply_apply _
    change coefficientSpecialEquiv e.symm L J hc' hf' _ ∈ specialBorel J hJ at hm
    rwa [hi] at hm
  · intro hg
    exact coefficient_borel_le e J L hJ hL hc hf hg
end Coefficients

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every order-25 matrix field gives the same marked pair `(SU₃,B)`.
The original coefficient field of the representation is not changed. -/
theorem borel_field_transport : BorelFieldTransport := by
  intro F _ _ J hF hconj
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (GaloisField 5 (2 * 1)) := Fintype.ofFinite _
  let e : F ≃+* GaloisField 5 (2 * 1) := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact (GaloisField.card 5 (2 * 1) (by decide)).symm)
  have hc (x : F) : e ((FormTransport.standardForm J).conj x) =
      (FormTransport.standardForm canonicalInputForm).conj (e x) := by
    change e (J.conj x) = canonicalInputForm.conj (e x)
    rw [hconj, map_pow]
    simp only [canonicalInputForm, ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
  have hf : (FormTransport.standardForm J).form.map e =
      (FormTransport.standardForm canonicalInputForm).form := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [FormTransport.standardForm]
  exact ⟨coefficientSpecialEquiv e _ _ hc hf,
    coefficient_borel_iff e _ _ rfl rfl hc hf⟩
end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation
