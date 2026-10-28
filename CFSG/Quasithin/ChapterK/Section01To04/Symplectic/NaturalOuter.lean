module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders.Symplectic.NaturalNormalizer
public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent

/-!
# Natural-module outer offenders in K.3.4.1

The literal binary normalizer of the natural symplectic image is semilinear.
Symplectic field-cocycle descent supplies the native centralizer-rank bound.
The semilinear displacement argument, including its equality case over F₄,
then places every FF-offender in the actual natural symplectic image.

Source: Aschbacher–Smith, K.3.4.1, printed p.456. The existing B.5.1
normalizer calculation has precisely this representation as its target;
no covering-module hypothesis or conclusion of B.5.1 is used here.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Natural
open Subgroup Representation.BinaryOffender
open SymplecticConjugatePair.Ambient.Normalizer
open CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch.Symplectic
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The sharp outer-involution bound, with its field-descent premise discharged. -/
theorem outer_involution_centralizer_bound {r : ℕ}
    (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (t : naturalNormalizer (F := F)) (ht : orderOf t = 2)
    (hout : t.val ∉ naturalDerivedImage) :
    Even r ∧ primeRank 2 (centralizer ({t} : Set (naturalNormalizer (F := F)))) ≤
      3 * (r / 2) + 1 :=
  SymplecticNaturalNormalizer.outer_centralizer_rank_sharp_of_descent hF hr
    (half_frobenius_cocycle_coboundary hF hr) t ht hout

/-- Outer field involutions lie in no FF-offender, including at r=2. -/
theorem offender_le_natural_image {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    {A : Subgroup (naturalNormalizer (F := F))}
    (hA : IsOffender naturalNormalizerAction A) :
    A ≤ naturalDerivedImage.subgroupOf _ := by
  apply naturalNormalizer_offender_le_of_centralizer_bound hF hr ?_ hA
  intro t ht hout
  have h := (outer_involution_centralizer_bound hF hr t ht hout).2
  omega

end CFSG.Quasithin.ChapterK.Symplectic.Natural
