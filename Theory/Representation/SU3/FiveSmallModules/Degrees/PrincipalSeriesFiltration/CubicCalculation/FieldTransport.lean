module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
import all Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence

/-!
# Entrywise field transport preserving the actual standard Borel

A field isomorphism compatible with the stored involutions transports the
antidiagonal special-unitary groups entrywise. On the Borel generators it
maps root coordinates entrywise and torus parameters by the units map.
Applying the inverse field map proves equality with the target Borel.
The original Hermitian Gram matrices are unrestricted.

The implementation import deliberately accesses the existing coefficient
map's body to prove its entry formula, without changing that shared module.
Only the public group and Borel equivalences occur in exported types.

Source: Huppert II.10.12 root-and-torus coordinates; the principal-series
approach to Guralnick–Malle, Proposition 4.3, p.10.
-/

public noncomputable section

open BenderSuzuki.MatrixGroups BenderSuzuki.External Matrix
open HermitianForm.OddPrimeSylow.NormalizedOuter HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
variable {F E : Type*} [Field F] [Field E]

noncomputable def standardFieldEquiv (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x)) :
    standardGroup J ≃* standardGroup L :=
  HermitianForm.coefficientSpecialEquiv e
    (FormTransport.standardForm J) (FormTransport.standardForm L) hc (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [FormTransport.standardForm])

theorem standardFieldEquiv_entry (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))
    (g : standardGroup J) (i j : Fin 3) :
    (standardFieldEquiv J L e hc g).val.val i j = e (g.val.val i j) := by
  exact (Eq.refl _).trans (Eq.refl _)

private def rootFieldMap (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    hermitianUnipotentCoord (FormTransport.standardForm L) :=
  ⟨(e z.val.1, e z.val.2), by
    change e z.val.2 + L.conj (e z.val.2) + e z.val.1 * L.conj (e z.val.1) = 0
    rw [← hc, ← hc, ← map_mul, ← map_add, ← map_add, ← map_zero e]
    exact congrArg e z.property⟩

private theorem standardFieldEquiv_root (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    standardFieldEquiv J L e hc (hermitianUnipotentSU _ rfl z) =
      hermitianUnipotentSU _ rfl (rootFieldMap J L e hc z) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change e ((hermitianUnipotentMatrix _ z) i j) =
    (hermitianUnipotentMatrix _ (rootFieldMap J L e hc z)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, rootFieldMap, FormTransport.standardForm_conj, hc]

private theorem standardFieldEquiv_torus (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x)) (k : Fˣ) :
    standardFieldEquiv J L e hc (hermitianTorusSU _ rfl k) =
      hermitianTorusSU _ rfl (Units.map e.toMonoidHom k) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change e ((hermitianTorusMatrix _ k) i j) =
    (hermitianTorusMatrix _ (Units.map e.toMonoidHom k)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, FormTransport.standardForm_conj, hc]

private theorem standardFieldEquiv_borel_le (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x)) :
    standardBorel J ≤ (standardBorel L).comap (standardFieldEquiv J L e hc).toMonoidHom := by
  apply sup_le
  · rintro _ ⟨z, rfl⟩
    change standardFieldEquiv J L e hc (hermitianUnipotentSU _ rfl z) ∈ standardBorel L
    rw [standardFieldEquiv_root]
    exact (show specialRoot _ _ ≤ standardBorel L from le_sup_left) ⟨_, rfl⟩
  · rintro _ ⟨k, rfl⟩
    change standardFieldEquiv J L e hc (hermitianTorusSU _ rfl k) ∈ standardBorel L
    rw [standardFieldEquiv_torus]
    exact (show specialTorus _ _ ≤ standardBorel L from le_sup_right) ⟨_, rfl⟩


/-- Entrywise field transport carries precisely the literal root-and-torus Borels. -/
theorem standardFieldEquiv_borel_iff (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))
    (g : standardGroup J) :
    standardFieldEquiv J L e hc g ∈ standardBorel L ↔ g ∈ standardBorel J := by
  constructor
  · intro hg
    have hc' (x : E) : e.symm (L.conj x) = J.conj (e.symm x) := by
      apply e.injective
      simpa only [e.apply_symm_apply] using (hc (e.symm x)).symm
    have hinv : standardFieldEquiv L J e.symm hc' (standardFieldEquiv J L e hc g) = g := by
      apply Subtype.ext
      apply Units.ext
      ext i j
      exact e.symm_apply_apply _
    have hh := standardFieldEquiv_borel_le L J e.symm hc' hg
    change standardFieldEquiv L J e.symm hc' (standardFieldEquiv J L e hc g) ∈
      standardBorel J at hh
    rwa [hinv] at hh
  · intro hg
    exact standardFieldEquiv_borel_le J L e hc hg

/-- Restriction of the entrywise map to the actual Borel subgroups. -/
noncomputable def standardBorelFieldEquiv (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x)) :
    standardBorel J ≃* standardBorel L where
  toFun b := ⟨standardFieldEquiv J L e hc b,
    (standardFieldEquiv_borel_iff J L e hc b).mpr b.property⟩
  invFun b := ⟨(standardFieldEquiv J L e hc).symm b, by
    apply (standardFieldEquiv_borel_iff J L e hc _).mp
    rw [MulEquiv.apply_symm_apply]
    exact b.property⟩
  left_inv b := Subtype.ext ((standardFieldEquiv J L e hc).symm_apply_apply b)
  right_inv b := Subtype.ext ((standardFieldEquiv J L e hc).apply_symm_apply b)
  map_mul' b c := Subtype.ext (map_mul (standardFieldEquiv J L e hc) b.val c.val)

theorem standardBorelFieldEquiv_coe (J : HermitianForm 3 F) (L : HermitianForm 3 E)
    (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x)) (b : standardBorel J) :
    (standardBorelFieldEquiv J L e hc b : standardGroup L) =
      standardFieldEquiv J L e hc b := by
  exact (Eq.refl _).trans (Eq.refl _)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation
