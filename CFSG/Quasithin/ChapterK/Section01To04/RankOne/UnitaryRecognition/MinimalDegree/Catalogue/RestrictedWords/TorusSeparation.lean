module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.RestrictedWords.TorusSeparation.Action
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.RestrictedWords.FormTransport
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue.Assembly
/-!
# Separation of concrete unitary tensor words from their upper fixed lines

An intertwiner sends the nonzero upper-fixed highest tensor to a nonzero
multiple of the target highest tensor. The literal unitary torus then gives
equal characters with exponents -(qA+B). Binary weight arithmetic recovers
the word except for the trivial/all-adjoint endpoint collision, which the
intertwiner's equality of actual carrier dimensions excludes.

The only geometric premise is that upper-fixed vectors lie on the seed line.
No irreducibility, class bound, faithfulness, or extension of arbitrary unitary
representations is assumed in the separation theorem. Its standard-form
version supplies exactly the separation premise of
`existsUnique_word_equiv_of_standard_geometry_and_class_bound`. We also
transport it to arbitrary Hermitian forms and apply it to the existing finite
simple-family assembly, retaining that assembly's independent geometry and
class-bound premises.

Sources: GLS III, 2.8.2, 2.8.6(a), 2.8.10(c); Guralnick--Malle, §3.1.
The fixed-line premise is to be discharged by `qt-k03-unitary-word-geometry`
in the owning `qt-k03-unitary-word-restriction` task.
-/

public section
noncomputable section
open Matrix BenderSuzuki.MatrixGroups BenderSuzuki.External Representation
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity
open Representation.SU3.BinaryDefiningWords.WeightSeparation
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords
variable {F K : Type*} [Field F] [Finite F] [Field K] [CharP K 2]

/-- Upper fixed-line geometry suffices for separation of the actual standard-form words. -/
theorem word_equiv_iff_of_fixedLine
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ u : List Factor, u.length = s → ∀ x : WordSpace K u,
      (∀ z : hermitianUnipotentCoord J,
        word J ι u (hermitianUnipotentSU J hJ z) x = x) →
      x ∈ Submodule.span K {wordSeed K u})
    (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w := by
  constructor
  · rintro ⟨e⟩
    have commute (g : J.specialSubgroup) (x : WordSpace K v) :
        e (word J ι v g x) = word J ι w g (e x) :=
      LinearMap.congr_fun (e.isIntertwining' g) x
    have hmem := hfixed w hw (e (wordSeed K v)) (fun z => by
      rw [← commute, word_seed_fixed])
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_smul] at hc
      exact wordSeed_ne_zero K v (e.toLinearEquiv.map_eq_zero_iff.mp hc.symm)
    have hchars (k : Fˣ) :
        (ι (k : F)) ^ exponent (2 ^ s) v = (ι (k : F)) ^ exponent (2 ^ s) w := by
      have h := commute (hermitianTorusSU J hJ k⁻¹) (wordSeed K v)
      rw [TorusSeparation.wordSeed_torus J hJ ι (2 ^ s) hconj,
        map_smul, ← hc, map_smul,
        TorusSeparation.wordSeed_torus J hJ ι (2 ^ s) hconj] at h
      simp only [Units.val_inv_eq_inv_val, inv_inv, smul_smul] at h
      have hh := smul_left_injective K (wordSeed_ne_zero K w) h
      apply mul_right_cancel₀ hc0
      simpa only [mul_comm c] using hh
    have hd : wordDegree v = wordDegree w := by
      simpa only [finrank_wordSpace] using e.toLinearEquiv.finrank_eq
    apply eq_of_unit_powers_and_degree s (by omega) hcard v w hv hw _ hd
    intro k
    apply Units.ext
    apply ι.injective
    simpa only [Units.val_pow_eq_pow_val, map_pow] using hchars k
  · rintro rfl
    exact ⟨Representation.Equiv.refl _⟩

/-- The separation premise of the standard-geometry catalogue consumer follows
from its existing fixed-line premise. -/
theorem standard_word_separation_of_fixedLine
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ u : List Factor, u.length = s → ∀ x : WordSpace K u,
      (∀ z : hermitianUnipotentCoord (standardForm J),
        word (standardForm J) ι u
          (hermitianUnipotentSU _ rfl z) x = x) →
      x ∈ Submodule.span K {wordSeed K u}) :
    ∀ v w : List Factor, v.length = s → w.length = s →
      Nonempty ((word (standardForm J) ι v).Equiv
        (word (standardForm J) ι w)) → v = w := by
  intro v w hv hw h
  exact (word_equiv_iff_of_fixedLine (standardForm J) rfl s hs hcard hconj ι hfixed v w hv hw).mp h

/-- Standard-form fixed-line geometry separates words on any Hermitian form,
via the actual form-transport intertwiners. -/
theorem word_equiv_iff_of_standard_fixedLine [Algebra (ZMod 2) F] [IsAlgClosed K]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ u : List Factor, u.length = s → ∀ x : WordSpace K u,
      (∀ z : hermitianUnipotentCoord (standardForm J),
        word (standardForm J) ι u (hermitianUnipotentSU _ rfl z) x = x) →
      x ∈ Submodule.span K {wordSeed K u})
    (v w : List Factor) (hv : v.length = s) (hw : w.length = s) :
    Nonempty ((word J ι v).Equiv (word J ι w)) ↔ v = w :=
  (word_standard_equiv_iff J s (by omega) hcard hconj ι v w).trans
    (word_equiv_iff_of_fixedLine (standardForm J) rfl s hs hcard hconj ι hfixed v w hv hw)

/-- Catalogue application with the separation premise discharged. Fixed-line
and orbit-span geometry remain with `qt-k03-unitary-word-geometry`; the class
bound remains with `qt-k03-unitary-pregular-classes`. Final unconditional
assembly belongs to `qt-k03-unitary-word-restriction` and its catalogue consumer. -/
theorem existsUnique_word_equiv_of_fixedLine_span_and_class_bound
    [Algebra (ZMod 2) F] [IsAlgClosed K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (ι : F →+* K)
    (hfixed : ∀ u : List Factor, u.length = s → ∀ x : WordSpace K u,
      (∀ z : hermitianUnipotentCoord (standardForm J),
        word (standardForm J) ι u (hermitianUnipotentSU _ rfl z) x = x) →
      x ∈ Submodule.span K {wordSeed K u})
    (hspan : ∀ u : List Factor, u.length = s →
      Submodule.span K (Set.range fun g : (standardForm J).specialSubgroup =>
        word (standardForm J) ι u g (wordSeed K u)) = ⊤)
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : J.specialSubgroup | ¬ 2 ∣ orderOf g}) ≤ Nat.card F)
    (ρ : Representation K J.specialSubgroup W) [IsIrreducible ρ] :
    ∃! w : List Factor, w.length = s ∧ Nonempty (ρ.Equiv (word J ι w)) := by
  apply existsUnique_word_equiv_of_simple_family_and_class_bound J s ι hcard _ _ hclasses ρ
  · intro w hw
    let : CharP F 2 := ι.charP ι.injective 2
    apply (word_standard_irreducible_iff J s (by omega) hcard hconj ι w).mpr
    exact word_isIrreducible_of_fixedLine_and_span _ rfl ι w (hfixed w hw) (hspan w hw)
  · intro v w hv hw he
    exact (word_equiv_iff_of_standard_fixedLine J s hs hcard hconj ι hfixed v w hv hw).mp he

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree.RestrictedWords
