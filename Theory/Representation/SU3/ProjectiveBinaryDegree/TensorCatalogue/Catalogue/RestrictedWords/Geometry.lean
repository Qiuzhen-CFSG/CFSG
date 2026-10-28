module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.TensorWords
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.PolynomialModel
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FixedLine

/-!
# The literal upper-unitary action and the highest-line criterion

Hermitian root coordinates embed into the upper-unitriangular SL₃ coordinates.
Consequently the already constructed tensor seed is fixed by the actual upper
unitary group. In characteristic two this coordinate group has exponent at
most four. The finite two-group fixed-vector theorem therefore reduces
irreducibility to two substantive geometric assertions: its fixed vectors lie
on the seed line, and the full unitary orbit of the seed spans the word.

These two assertions are explicit premises here; the SL₃ interpolation theorem
is not being restricted to SU₃. Sources: Huppert II.10.12 and GLS III, 2.8.2,
2.8.6(a), and 2.8.10(c).
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/Catalogue/RestrictedWords/Geometry.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open scoped MatrixGroups
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords
variable {F K : Type*} [Field F] [Field K]

/-- The same upper matrix in the ambient unitriangular coordinate group. -/
def upperCoordinates (J : HermitianForm 3 F) : hermitianUnipotentCoord J →* U F where
  toFun z := ⟨z.val.1, -J.conj z.val.1, z.val.2⟩
  map_one' := by
    apply U.ext
    · rfl
    · change -J.conj 0 = 0
      simp
    · rfl
  map_mul' z t := by
    apply U.ext
    · rfl
    · change -J.conj (z.val.1 + t.val.1) = -J.conj z.val.1 + -J.conj t.val.1
      rw [map_add, neg_add]
    · change z.val.2 + t.val.2 - z.val.1 * J.conj t.val.1 =
        z.val.2 + t.val.2 + z.val.1 * -J.conj t.val.1
      rw [mul_neg, sub_eq_add_neg]

/-- The first and last coordinates recover the Hermitian root element. -/
theorem upperCoordinates_injective (J : HermitianForm 3 F) :
    Function.Injective (upperCoordinates J) := by
  intro z t h
  exact Subtype.ext (Prod.ext (congrArg U.x h) (congrArg U.c h))

/-- The literal special-linear inclusion agrees with the upper-coordinate embedding. -/
theorem upper_inclusion (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (z : hermitianUnipotentCoord J) :
    specialLinearInclusion J (hermitianUnipotentSU J hJ z) =
      specialLinear F (upperCoordinates J z) := by
  apply Subtype.ext
  rfl

/-- The upper Hermitian coordinate group is a two-group in characteristic two. -/
theorem upper_isTwoGroup [CharP F 2] (J : HermitianForm 3 F) :
    IsPGroup 2 (hermitianUnipotentCoord J) := by
  have hp : IsPGroup 2 (U F) := by
    intro u
    refine ⟨2, ?_⟩
    change u ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    apply (square_eq_one_iff F _).mpr
    left
    simp [pow_two, CharTwo.add_self_eq_zero]
  exact hp.of_injective (upperCoordinates J) (upperCoordinates_injective J)

/-- The concrete highest tensor is fixed by every actual upper-unitary element. -/
theorem word_seed_fixed [CharP K 2] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (ι : F →+* K)
    (w : List Factor) (z : hermitianUnipotentCoord J) :
    word J ι w (hermitianUnipotentSU J hJ z) (wordSeed K w) = wordSeed K w := by
  change wordRep ι w (specialLinearInclusion J _) _ = _
  rw [upper_inclusion]
  exact FixedLine.wordSeed_fixed ι w (upperCoordinates J z)

/-- The unitary fixed-line and orbit-span assertions imply irreducibility. -/
theorem word_isIrreducible_of_fixedLine_and_span [Finite F] [CharP F 2] [CharP K 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (ι : F →+* K) (w : List Factor)
    (hfixed : ∀ v : WordSpace K w,
      (∀ z : hermitianUnipotentCoord J, word J ι w (hermitianUnipotentSU J hJ z) v = v) →
      v ∈ Submodule.span K {wordSeed K w})
    (hspan : Submodule.span K (Set.range fun g : J.specialSubgroup =>
      word J ι w g (wordSeed K w)) = ⊤) : IsIrreducible (word J ι w) := by
  let : Nontrivial (WordSpace K w) := ⟨⟨wordSeed K w, 0, wordSeed_ne_zero K w⟩⟩
  let U₀ := (hermitianUnipotentSU J hJ).range
  apply Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.irreducible_of_fixedLine_of_orbitSpan
    (word J ι w) U₀ (IsPGroup.of_surjective (upper_isTwoGroup J)
      (hermitianUnipotentSU J hJ).rangeRestrict (MonoidHom.rangeRestrict_surjective _))
      (wordSeed K w) _ hspan
  intro v hv
  exact hfixed v (fun z => hv ⟨hermitianUnipotentSU J hJ z, ⟨z, rfl⟩⟩)

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords
