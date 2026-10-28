module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.Assembly
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords.FormTransport
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords.Geometry
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords.StandardGeometry
public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.Catalogue.RestrictedWords.TorusSeparation

/-!
# Simplicity and separation of restricted binary unitary words

The arbitrary Hermitian form is transported to the antidiagonal form through
actual matrix conjugation and compatible equivalences of every concrete word.
On the standard form, unitary interpolation proves a one-dimensional upper
fixed space and a cyclic highest tensor, hence simplicity. The actual torus
action on that line separates the words; their dimensions distinguish the
trivial/Steinberg endpoint collision. These results give simplicity and
pairwise separation for every length-s word on every Hermitian form.

The earlier conditional reductions are retained. The final three theorems
discharge their geometry and separation premises and apply the finite
simple-family catalogue assembly, retaining only its independent odd-order
class bound in the catalogue conclusion.

Sources: GLS III, 2.8.2, 2.8.6(a), and 2.8.10(c); Guralnick--Malle, §3.1
and Theorem 4.10. The remaining class bound has independent owner
`qt-k03-unitary-pregular-classes`; unconditional catalogue assembly remains
with `qt-k03-unitary-word-catalogue`.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/Catalogue/RestrictedWords.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

public section
noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords

variable {F K : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Field K] [IsAlgClosed K] [CharP K 2]

/-- The standard-form finite geometry suffices for simplicity of an arbitrary
Hermitian-form word, with its literal representation unchanged. -/
theorem word_isIrreducible_of_standard_geometry
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (w : List Factor)
    (hfixed : ∀ v : WordSpace K w,
      (∀ z : hermitianUnipotentCoord (standardForm J),
        word (standardForm J) ι w (hermitianUnipotentSU (standardForm J) rfl z) v = v) →
      v ∈ Submodule.span K {wordSeed K w})
    (hspan : Submodule.span K (Set.range fun g : (standardForm J).specialSubgroup =>
      word (standardForm J) ι w g (wordSeed K w)) = ⊤) :
    IsIrreducible (word J ι w) := by
  let : CharP F 2 := ι.charP ι.injective 2
  apply (word_standard_irreducible_iff J s (by omega) hcard hconj ι w).mpr
  exact word_isIrreducible_of_fixedLine_and_span (standardForm J) rfl ι w hfixed hspan

/-- Separation for the standard form transfers to every Hermitian form.
The converse implication is the actual identity intertwiner. -/
theorem word_equiv_iff_of_standard_separation
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hseparate : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word (standardForm J) ι v).Equiv (word (standardForm J) ι w)) → v = w)
    (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w := by
  constructor
  · intro h
    exact hseparate v w hv hw
      ((word_standard_equiv_iff J s (by omega) hcard hconj ι v w).mp h)
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

/-- Concrete application to the finite-family catalogue. Simplicity is derived
from unitary geometry, and both simplicity and separation are transported
from the standard form. The class bound remains an independent premise. -/
theorem existsUnique_word_equiv_of_standard_geometry_and_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ w : List Factor, w.length = s → ∀ v : WordSpace K w,
      (∀ z : hermitianUnipotentCoord (standardForm J),
        word (standardForm J) ι w (hermitianUnipotentSU (standardForm J) rfl z) v = v) →
      v ∈ Submodule.span K {wordSeed K w})
    (hspan : ∀ w : List Factor, w.length = s →
      Submodule.span K (Set.range fun g : (standardForm J).specialSubgroup =>
        word (standardForm J) ι w g (wordSeed K w)) = ⊤)
    (hseparate : ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word (standardForm J) ι v).Equiv (word (standardForm J) ι w)) → v = w)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  apply existsUnique_word_equiv_of_simple_family_and_class_bound J s ι hcard
    (fun w hw => word_isIrreducible_of_standard_geometry J s hs hcard hconj ι w
      (hfixed w hw) (hspan w hw))
    (fun v w hv hw he =>
      (word_equiv_iff_of_standard_separation J s hs hcard hconj ι hseparate v w hv hw).mp he)
    hclasses ρ

/-- Every length-s concrete binary word remains irreducible on the full special
unitary group, for an arbitrary Hermitian form. The fixed-line and orbit-span
premises are discharged by interpolation on the standard unitary group. -/
theorem word_isIrreducible
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (w : List Factor) (hw : w.length = s) :
    IsIrreducible (word J ι w) := by
  apply (word_standard_irreducible_iff J s (by omega) hcard hconj ι w).mpr
  exact word_isIrreducible_standard (standardForm J) rfl s hs hcard hconj ι w hw

/-- Two length-s words on the full special unitary group are equivalent
precisely when all their factor labels agree. No faithfulness, degree bound,
class count, or extension of arbitrary representations is required. -/
theorem word_equiv_iff
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K) (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w := by
  exact word_equiv_iff_of_standard_fixedLine J s hs hcard hconj ι
    (word_fixed_mem_span_standard (standardForm J) rfl s hs hcard hconj ι) v w hv hw

/-- The literal restricted words exhaust the irreducibles once the independent
unitary odd-order class bound is supplied. Both the simplicity and separation
premises of `existsUnique_word_equiv_of_simple_family_and_class_bound` are
proved here; the class bound remains with `qt-k03-unitary-pregular-classes`. -/
theorem existsUnique_word_equiv_of_class_bound
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  exact existsUnique_word_equiv_of_simple_family_and_class_bound J s ι hcard
    (word_isIrreducible J s hs hcard hconj ι)
    (fun v w hv hw he => (word_equiv_iff J s hs hcard hconj ι v w hv hw).mp he)
    hclasses ρ

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.RestrictedWords
