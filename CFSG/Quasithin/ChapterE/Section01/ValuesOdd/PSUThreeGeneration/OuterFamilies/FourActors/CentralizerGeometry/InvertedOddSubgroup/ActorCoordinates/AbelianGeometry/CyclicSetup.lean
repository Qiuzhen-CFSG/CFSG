module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.Setup
public import Theory.ElementaryAbelian.Basic

/-!
# The cyclic inner-preimage branch of outer actor placement

The inner preimage of an abelian automorphism two-group is the literal
preimage under `MulAut.conj`. In a centerless group it is an abelian
two-group fixed pointwise by the entire actor. If it is not cyclic, two
distinct involutions give a marked four-group in that pointwise fixer.

The remaining cyclic branch may supply root coordinates directly, or a
marked four-group fixed by the actor. The latter four-group need not lie
in the inner preimage. Its separate placement and fixer theorems then
give rotation coordinates. This predicate is an unproved intermediate
contract; it does not assert the existence of either alternative.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; the cited Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
variable {F : Type} [Field F]

/-- A single projective equivalence marks the involution and gives scalar
action on the literal fixed-field root for the whole actor. -/
@[expose] def RootActionCoordinates (J : HermitianForm 3 F)
    (U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (w : ProjectiveSpecialUnitaryMatrixGroup J) : Prop :=
  ∃ J' : HermitianForm 3 F, J'.conj = J.conj ∧
    ∃ (hJ' : J'.form = !![0,0,1;0,1,0;1,0,0]) (h2 : (2 : F) ≠ 0)
      (e : ProjectiveSpecialUnitaryMatrixGroup J ≃* ProjectiveSpecialUnitaryMatrixGroup J'),
      e w = hermitianTorusPSU J' hJ' (-1) ∧
      ∀ a ∈ U, ∃ c : (FixedBy.subfield F J'.conj)ˣ,
        ∀ t : FixedBy.subfield F J'.conj,
          MulAut.congr e a (fixedRoot J' hJ' h2 (Multiplicative.ofAdd t)) =
            fixedRoot J' hJ' h2 (Multiplicative.ofAdd ((c : FixedBy.subfield F J'.conj) * t))

/-- Only the cyclic inner-preimage case remains after the elementary
noncyclic reduction. The four-group alternative specifies actual pointwise
fixation, not preservation of an unspecified odd subgroup. -/
@[expose] def CyclicInnerPlacement (J : HermitianForm 3 F) : Prop :=
  ∀ U : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
    IsPGroup 2 U → IsMulCommutative U → IsCyclic (U.comap MulAut.conj) →
    ∀ γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      J.IsEntrywiseConjugation γ → γ ∈ U →
    ∀ w : ProjectiveSpecialUnitaryMatrixGroup J,
      orderOf w = 2 → MulAut.conj w ∈ U →
      RootActionCoordinates J U w ∨
        ∃ B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
          IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ w ∈ B ∧
            ∀ a ∈ U, ∀ x ∈ B, a x = x

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianGeometry
