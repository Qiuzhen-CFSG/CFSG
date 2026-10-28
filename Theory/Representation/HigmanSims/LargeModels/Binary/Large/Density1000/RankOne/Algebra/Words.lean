module
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Setup

/-!
# Simplifying the four literal ATLAS density words

Once the original first generator is certified involutory, the four words
sum to `((AB)^2 + BA)BB + BA + AB`. This is a noncommutative identity in
the exact left-to-right convention of `Setup.wordMatrix`; no relation for B
is used. The involution premise is discharged by `Algebra.Products.AA`.
Source: `Binary/source/density1000.json`, ATLAS HSG1-f2r1000B0.
-/

public section
namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra

theorem literal_words_factor
    (haa : generator false * generator false = 1) :
    algebraMatrix =
      ((generator false * generator true) * (generator false * generator true) +
        generator true * generator false) * generator true * generator true +
          generator true * generator false + generator false * generator true := by
  have cancel (x : Square) : generator false * (generator false * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  change wordMatrix [false,true,false,true,false,false,true,true] +
    wordMatrix [true,false] + wordMatrix [false,false,true,false,true,true] +
      wordMatrix [false,false,false,true] = _
  simp only [wordMatrix, mul_one, cancel, add_mul, mul_assoc]
  abel

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000.RankOne.Algebra
