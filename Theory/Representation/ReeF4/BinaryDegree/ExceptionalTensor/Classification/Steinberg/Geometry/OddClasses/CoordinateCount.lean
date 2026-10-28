module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Restriction
public import Theory.Representation.SL3.BinaryFieldDescent.Fields
/-!
# Counting the two Frobenius-compatible coordinate pairs

The equations x^(2^(m+1))=y and y^(2^m)=x identify a pair with one
point of the actual embedded coefficient field. Two independent pairs
therefore have q² points, precisely the number of restricted Ree weights.
The proof uses the original field embedding and the cardinality polynomial;
it assumes no conjugacy-class bound or orbit-coordinate separation.

Source: Steinberg (1963), §12.2, final coordinate count after §3.9.
-/

open ReeF4
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
public noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.CoordinateCount
variable {F : Type*} [Field F]

@[expose] def TwistedPair (m : ℕ) (F : Type*) [Field F] :=
  {v : F × F // v.1 ^ (2 ^ (m + 1)) = v.2 ∧ v.2 ^ (2 ^ m) = v.1}

lemma twistedPair_first_pow (m : ℕ) (v : TwistedPair m F) :
    v.val.1 ^ (2 ^ (2 * m + 1)) = v.val.1 := by
  rcases v with ⟨⟨a, b⟩, hab, hba⟩
  change a ^ (2 ^ (2 * m + 1)) = a
  have he : 2 * m + 1 = (m + 1) + m := by omega
  rw [he, pow_add, pow_mul, hab, hba]

@[expose] noncomputable def pairOfField (m : ℕ) (f : CoefficientField m →+* F)
    (a : CoefficientField m) : TwistedPair m F :=
  ⟨(f a, (f a) ^ (2 ^ (m + 1))), rfl, by
    have he : (m + 1) + m = 2 * m + 1 := by omega
    rw [← pow_mul, ← pow_add, he, ← map_pow, field_pow]⟩

lemma pairOfField_bijective (m : ℕ) (f : CoefficientField m →+* F) :
    Function.Bijective (pairOfField m f) := by
  constructor
  · intro a b h
    apply f.injective
    exact congrArg (fun v : TwistedPair m F => v.val.1) h
  · intro v
    have hv : v.val.1 ∈ Set.range f := by
      rw [FiniteField.mem_range_iff_pow_natCard, field_card]
      exact twistedPair_first_pow m v
    obtain ⟨a, ha⟩ := hv
    refine ⟨a, Subtype.ext (Prod.ext ha ?_)⟩
    change (f a) ^ (2 ^ (m + 1)) = v.val.2
    rw [ha]
    exact v.property.1

lemma finite_twistedPair (m : ℕ) (f : CoefficientField m →+* F) :
    Finite (TwistedPair m F) :=
  Finite.of_surjective (pairOfField m f) (pairOfField_bijective m f).surjective

lemma card_twistedPair (m : ℕ) (f : CoefficientField m →+* F) :
    Nat.card (TwistedPair m F) = 2 ^ (2 * m + 1) := by
  rw [← Nat.card_congr (Equiv.ofBijective (pairOfField m f) (pairOfField_bijective m f)), field_card]

lemma card_coordinate_pairs (m : ℕ) (f : CoefficientField m →+* F) :
    Nat.card (TwistedPair m F × TwistedPair m F) = Nat.card (RestrictedWeight m) := by
  rw [Nat.card_prod, card_twistedPair m f, card_restrictedWeight, ← mul_pow]
  norm_num
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.CoordinateCount
