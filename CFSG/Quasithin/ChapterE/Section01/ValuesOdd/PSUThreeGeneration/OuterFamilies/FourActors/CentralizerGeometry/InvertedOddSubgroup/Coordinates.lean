module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.RootLine
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.Model
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Coordinate alternatives for the conjugate outer four-actor

The root alternative marks the inner involution as `diag(-1,1,-1)` in
antidiagonal coordinates and specifies scalar action on the fixed-field
root parameter. The rotation alternative marks it as `diag(-1,-1,1)` in
identity coordinates and specifies identity or inverse action on the
norm-one rotation parameter. Both retain an actual projective group
isomorphism, the original ambient conjugation, field order p² and the
Frobenius involution. Neither specifies an abstract odd subgroup.

These are sufficient coordinate alternatives for the construction in
Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher (1982),
Lemma 4.11. Their existence for a conjugate of the whole outer actor is
an independent, still unproved geometry assertion. In particular a
fixed-group isomorphism alone does not establish these action formulas.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus
variable {G : Type*} [Group G]

/-- Concrete root-scaling or norm-one-rotation coordinates for the full ambient action. -/
@[expose] def HasInvertedCoordinates (L R : Subgroup G) [L.Normal] (z : L) (p : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm 3 F),
    Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
      ((∃ (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : F) ≠ 0)
          (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J),
        e z = hermitianTorusPSU J hJ (-1) ∧
        ∀ s ∈ R, ∃ c : (FixedBy.subfield F J.conj)ˣ,
          ∀ t : FixedBy.subfield F J.conj,
            MulAut.congr e (MulAut.conjNormal s) (fixedRoot J hJ h2 (Multiplicative.ofAdd t)) =
              fixedRoot J hJ h2 (Multiplicative.ofAdd ((c : FixedBy.subfield F J.conj) * t))) ∨
      (∃ (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
          (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J),
        e z = J.specialToProjective (Matrix.SU3.standardInvolution J hJ) ∧
        ∀ s ∈ R, ∃ ε : Bool, ∀ k : HermitianForm.EvenInner.normOne J,
          MulAut.congr e (MulAut.conjNormal s) (projectiveRotation J hJ h2 k) =
            projectiveRotation J hJ h2 (if ε then k⁻¹ else k)))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
