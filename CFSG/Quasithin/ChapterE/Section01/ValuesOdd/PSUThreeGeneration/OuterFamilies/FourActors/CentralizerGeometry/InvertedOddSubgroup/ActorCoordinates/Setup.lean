module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.Coordinates

/-!
# The intrinsic abelian outer-action coordinate problem

After normalizing one outer involution to entrywise conjugation, the image
of an abelian ambient two-subgroup is an abelian two-subgroup of the actual
projective automorphism group. It contains that entrywise involution and
conjugation by the marked inner involution. The remaining matrix problem
asks for simultaneous root-scaling or rotation-parameter coordinates.

This interface retains the original matrix field and its involution and
an actual projective equivalence. It neither asserts that such coordinates
exist nor asks for an abstract odd subgroup. Its ambient consumer is
`hasInvertedCoordinates_of_abelian_action` in the parent `ActorCoordinates`.

Source: Aschbacher--Smith E.1.14(7), printed p.214, citing Aschbacher,
GF(2)-representations of finite groups (1982), Lemma 4.11. This is an
intermediate coordinate contract, not the statement of that source theorem.
-/

public section
open Matrix Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus

/-- Intrinsic coordinate calculation for an abelian two-group containing the
normalized outer involution and conjugation by the marked inner involution. -/
@[expose] def AbelianOuterCoordinateGeometry {F : Type} [Field F] (J : HermitianForm 3 F) : Prop :=
  ∀ (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))),
    IsPGroup 2 U → IsMulCommutative U →
    ∀ (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      J.IsEntrywiseConjugation γ → γ ∈ U →
    ∀ (w : ProjectiveSpecialUnitaryMatrixGroup J), orderOf w = 2 → MulAut.conj w ∈ U →
    ∃ J' : HermitianForm 3 F, J'.conj = J.conj ∧
      ((∃ (hJ' : J'.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : F) ≠ 0)
          (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup J'),
        e w = hermitianTorusPSU J' hJ' (-1) ∧
        ∀ a ∈ U, ∃ c : (FixedBy.subfield F J'.conj)ˣ,
          ∀ t : FixedBy.subfield F J'.conj,
            MulAut.congr e a (fixedRoot J' hJ' h2 (Multiplicative.ofAdd t)) =
              fixedRoot J' hJ' h2 (Multiplicative.ofAdd ((c : FixedBy.subfield F J'.conj) * t))) ∨
      (∃ (hJ' : J'.form = 1) (h2 : (2 : F) ≠ 0)
          (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup J'),
        e w = J'.specialToProjective (Matrix.SU3.standardInvolution J' hJ') ∧
        ∀ a ∈ U, ∃ ε : Bool, ∀ k : HermitianForm.EvenInner.normOne J',
          MulAut.congr e a (projectiveRotation J' hJ' h2 k) =
            projectiveRotation J' hJ' h2 (if ε then k⁻¹ else k)))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
