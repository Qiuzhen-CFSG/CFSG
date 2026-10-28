module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots
public import Mathlib.GroupTheory.PGroup

/-!
# A fixed-field root line in odd projective SU₃

For the antidiagonal Hermitian form the matrices with rows
`[1,t,-t²/2]`, `[0,1,-t]`, `[0,0,1]`, with t in the Hermitian fixed field,
form an injective image of its additive group in the genuine projective SU₃.
The diagonal involution `diag(-1,1,-1)` sends t to -t. Thus the root line
has order p and is inverted by that involution when the fixed field has
prime order p. Projective root injectivity handles the scalar quotient.

This is a defining-characteristic witness for the outer four-actor branch
of Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.11. The matrix
coordinates are those of Huppert II.10.12. Actor placement remains separate.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- The fixed-field additive line inside the Hermitian root coordinates. -/
@[expose] def fixedRootCoord (h2 : (2 : F) ≠ 0) :
    Multiplicative (FixedBy.subfield F J.conj) →* hermitianUnipotentCoord J where
  toFun t := ⟨((t.toAdd : F), -(t.toAdd : F) ^ 2 / 2), by
    have ht : J.conj (t.toAdd : F) = t.toAdd := t.toAdd.property
    simp only [map_div₀, map_neg, map_pow, map_ofNat, ht]
    field_simp
    ring⟩
  map_one' := by
    apply Subtype.ext
    change ((0 : F), -(0 : F) ^ 2 / 2) = (0, 0)
    simp
  map_mul' s t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -((s.toAdd : F) + (t.toAdd : F)) ^ 2 / 2 =
        -(s.toAdd : F) ^ 2 / 2 + -(t.toAdd : F) ^ 2 / 2 -
          (s.toAdd : F) * J.conj (t.toAdd : F)
      have ht : J.conj (t.toAdd : F) = t.toAdd := t.toAdd.property
      rw [ht]
      field_simp
      ring

/-- The actual projective root-line map, with the original field involution. -/
@[expose] def fixedRoot (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2 : F) ≠ 0) :
    Multiplicative (FixedBy.subfield F J.conj) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (root J hJ).comp (fixedRootCoord J h2)

/-- Scalar projection does not identify distinct fixed-field root parameters. -/
theorem fixedRoot_injective (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2 : F) ≠ 0) : Function.Injective (fixedRoot J hJ h2) := by
  intro s t h
  have he := root_injective J hJ h
  have hv := congrArg (fun u : hermitianUnipotentCoord J => u.val.1) he
  exact congrArg Multiplicative.ofAdd (Subtype.ext hv)

/-- The projective root line has the order of the Hermitian fixed field. -/
theorem fixedRoot_card [Finite F] (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2 : F) ≠ 0) {p : ℕ}
    (hf : Nat.card (FixedBy.subfield F J.conj) = p) :
    Nat.card (fixedRoot J hJ h2).range = p := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (fixedRoot_injective J hJ h2)).toEquiv]
  exact hf

/-- The indicated diagonal involution inverts the root line. -/
theorem fixedRoot_inverted (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (h2 : (2 : F) ≠ 0) (t : Multiplicative (FixedBy.subfield F J.conj)) :
    hermitianTorusPSU J hJ (-1) * fixedRoot J hJ h2 t *
      (hermitianTorusPSU J hJ (-1))⁻¹ = (fixedRoot J hJ h2 t)⁻¹ := by
  have he : hermitianTorusAction J (-1) (fixedRootCoord J h2 t) =
      fixedRootCoord J h2 t⁻¹ := by
    apply Subtype.ext
    apply Prod.ext
    · simp [hermitianTorusAction_fst, fixedRootCoord]
    · simp [hermitianTorusAction_snd, fixedRootCoord]
  change hermitianTorusPSU J hJ (-1) *
    hermitianUnipotentPSU J hJ (fixedRootCoord J h2 t) * _ = _
  rw [hermitianTorusPSU_mul_unipotent, he, mul_inv_cancel_right]
  exact (map_inv (fixedRoot J hJ h2) t)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
