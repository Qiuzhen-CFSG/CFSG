module

public import Theory.SpecificGroups.SU3.OddRootFixers.FixedBlock
public import Theory.Representation.SU3.CubicDegree.InnerActors.RootGeometry

/-!
# Three marked unitary transvection groups

The first group is the fixed field in the upper-right root coordinate.
The Weyl element gives the opposite group. If `b + conj b = 1`, the
upper root `(1,b)` carries the opposite center to the isotropic vector
`(b,1,1)`. The fixed-field SL₂ block and its action on isotropic lines
provide two independent inputs for proving generation by these groups.

All matrices live in SU₃ itself. Source: Huppert II.10.12, with the
characteristic-two transvection convention used in K.3.3, printed p.456.
-/

@[expose] public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.BorelTorus.EvenCenterAction
variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [CharP F 2] in
/-- The original binary field-order hypothesis supplies characteristic two. -/
theorem charTwo_of_card [Finite F] {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2) :
    CharP F 2 := by
  let := Fintype.ofFinite F
  apply charP_of_card_eq_prime_pow (p := 2) (f := s * 2)
  simpa [Nat.card_eq_fintype_card, pow_mul] using hcard

/-- The whole additive fixed field, embedded in SU₃. -/
def central : Subgroup J.specialSubgroup :=
  ((hermitianUnipotentSU J hJ).comp (centralCoord J)).range

/-- The existing fixed-field SL₂ block, with its literal SU embedding. -/
noncomputable def block : SpecialLinearGroup (Fin 2) (fixedField J) →* J.specialSubgroup :=
  (J.specialGraphAut hJ).fixedSubgroup.subtype.comp
    (J.specialGraphFixedEquivSL2 hJ).symm.toMonoidHom

theorem block_val (A : SpecialLinearGroup (Fin 2) (fixedField J)) :
    (block J hJ A).val.val =
      !![(A 0 0 : F),0,(A 0 1 : F);0,1,0;(A 1 0 : F),0,(A 1 1 : F)] :=
  HermitianForm.OddRootFixers.fixedBlock_val J hJ A

/-- An upper root carrying the third coordinate vector to `(b,1,1)`. -/
def seed (b : F) (hb : b + J.conj b = 1) : J.specialSubgroup :=
  hermitianUnipotentSU J hJ ⟨(1,b), by
    simp only [map_one, mul_one, hb, CharTwo.add_self_eq_zero]⟩

theorem seed_val (b : F) (hb : b + J.conj b = 1) :
    (seed J hJ b hb).val.val = !![1,1,b;0,1,1;0,0,1] := by
  change hermitianUnipotentMatrix J _ = _
  simp [hermitianUnipotentMatrix, CharTwo.neg_eq]

/-- The conjugating element whose first column is `(b,1,1)`. -/
def thirdConjugator (b : F) (hb : b + J.conj b = 1) : J.specialSubgroup :=
  seed J hJ b hb * hermitianWeylSU J hJ

/-- The three candidate centers in the same SU₃ carrier. -/
def triple (b : F) (hb : b + J.conj b = 1) : Subgroup J.specialSubgroup :=
  central J hJ ⊔ (central J hJ).map (MulAut.conj (hermitianWeylSU J hJ)).toMonoidHom ⊔
    (central J hJ).map (MulAut.conj (thirdConjugator J hJ b hb)).toMonoidHom

/-- Matrix formulation of transitivity on all isotropic one-dimensional spaces. -/
def IsotropicLineTransitive (H : Subgroup J.specialSubgroup) : Prop :=
  ∀ v : Fin 3 → F, v ≠ 0 →
    dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0 →
      ∃ g ∈ H, ∃ a : F, a ≠ 0 ∧ ∀ i, g.val.val i 0 = a * v i

/-- The two block orbits, stated as explicit vector equations. The second
representative is isotropic when `b + conj b = 1`. -/
def BlockOrbitDecomposition (b : F) : Prop :=
  ∀ v : Fin 3 → F, v ≠ 0 →
    dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0 →
      (∃ A : SpecialLinearGroup (Fin 2) (fixedField J), ∃ a : F,
        a ≠ 0 ∧ ∀ i, (block J hJ A).val.val i 0 = a * v i) ∨
      (∃ A : SpecialLinearGroup (Fin 2) (fixedField J), ∃ a : F,
        a ≠ 0 ∧ ∀ i, ((block J hJ A).val.val.mulVec ![b,1,1]) i = a * v i)

end Representation.SU3.CubicDegree.InnerActors.ThreeRoots
