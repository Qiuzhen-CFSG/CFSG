module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.Evaluation

/-!
# Fixed points for the first two proposed stabilizers

The stage-one generators fix 508, and the stage-two generators fix 509.
Long nested words are evaluated in stages: leaf computations concern only
word5 and word8; ordinary permutation equalities compose their point images.
This avoids unfolding the entire straight-line program in the kernel at once.
These facts discharge `next_fixes` in the actual Schreier certificate, but do
not assert that the proposed subgroups contain the full point stabilizers.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the exact words retained
in `Fi23InFi24Prime/source/faithfulness/nodes.json`.
Reproduce with `StagesZeroTwo/source/fixed_points.py`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo

private theorem eval5_508 : Word.word5 aPerm bPerm (508 : Fin 306936) = 508 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 508 = 508 from by decide +kernel)

private theorem eval8_508 : Word.word8 aPerm bPerm (508 : Fin 306936) = 508 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 508 = 508 from by decide +kernel)

private theorem eval8_304138 : Word.word8 aPerm bPerm (304138 : Fin 306936) = 71333 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 304138 = 71333 from by decide +kernel)

private theorem eval5_71333 : Word.word5 aPerm bPerm (71333 : Fin 306936) = 76168 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 71333 = 76168 from by decide +kernel)

private theorem eval8_76168 : Word.word8 aPerm bPerm (76168 : Fin 306936) = 305650 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 76168 = 305650 from by decide +kernel)

private theorem eval8_305650 : Word.word8 aPerm bPerm (305650 : Fin 306936) = 69501 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 305650 = 69501 from by decide +kernel)

private theorem eval5_69501 : Word.word5 aPerm bPerm (69501 : Fin 306936) = 108440 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 69501 = 108440 from by decide +kernel)

private theorem eval8_108440 : Word.word8 aPerm bPerm (108440 : Fin 306936) = 75619 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 108440 = 75619 from by decide +kernel)

private theorem eval8_75619 : Word.word8 aPerm bPerm (75619 : Fin 306936) = 23136 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 75619 = 23136 from by decide +kernel)

private theorem eval5_23136 : Word.word5 aPerm bPerm (23136 : Fin 306936) = 23846 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 23136 = 23846 from by decide +kernel)

private theorem eval5_23846 : Word.word5 aPerm bPerm (23846 : Fin 306936) = 116748 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 23846 = 116748 from by decide +kernel)

private theorem eval5_116748 : Word.word5 aPerm bPerm (116748 : Fin 306936) = 303158 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 116748 = 303158 from by decide +kernel)

private theorem eval5_303158 : Word.word5 aPerm bPerm (303158 : Fin 306936) = 38618 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 303158 = 38618 from by decide +kernel)

private theorem eval5_38618 : Word.word5 aPerm bPerm (38618 : Fin 306936) = 69901 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 38618 = 69901 from by decide +kernel)

private theorem eval5_69901 : Word.word5 aPerm bPerm (69901 : Fin 306936) = 65657 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 69901 = 65657 from by decide +kernel)

private theorem eval5_65657 : Word.word5 aPerm bPerm (65657 : Fin 306936) = 180650 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 65657 = 180650 from by decide +kernel)

private theorem eval8_180650 : Word.word8 aPerm bPerm (180650 : Fin 306936) = 509 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 180650 = 509 from by decide +kernel)

private theorem eval10_304138 : Word.word10 aPerm bPerm (304138 : Fin 306936) = 509 := by
  simp only [Word.word10, Equiv.Perm.mul_apply, eval8_304138, eval5_71333, eval8_76168, eval8_305650, eval5_69501, eval8_108440, eval8_75619, eval5_23136, eval5_23846, eval5_116748, eval5_303158, eval5_38618, eval5_69901, eval5_65657, eval8_180650]

private theorem eval5_304138 : Word.word5 aPerm bPerm (304138 : Fin 306936) = 70959 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 304138 = 70959 from by decide +kernel)

private theorem eval5_70959 : Word.word5 aPerm bPerm (70959 : Fin 306936) = 76965 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 70959 = 76965 from by decide +kernel)

private theorem eval8_76965 : Word.word8 aPerm bPerm (76965 : Fin 306936) = 304053 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 76965 = 304053 from by decide +kernel)

private theorem eval5_304053 : Word.word5 aPerm bPerm (304053 : Fin 306936) = 304285 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 304053 = 304285 from by decide +kernel)

private theorem eval8_304285 : Word.word8 aPerm bPerm (304285 : Fin 306936) = 66297 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 304285 = 66297 from by decide +kernel)

private theorem eval5_66297 : Word.word5 aPerm bPerm (66297 : Fin 306936) = 198969 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 66297 = 198969 from by decide +kernel)

private theorem eval8_198969 : Word.word8 aPerm bPerm (198969 : Fin 306936) = 235726 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 198969 = 235726 from by decide +kernel)

private theorem eval5_235726 : Word.word5 aPerm bPerm (235726 : Fin 306936) = 71287 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 235726 = 71287 from by decide +kernel)

private theorem eval5_71287 : Word.word5 aPerm bPerm (71287 : Fin 306936) = 70694 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 71287 = 70694 from by decide +kernel)

private theorem eval8_70694 : Word.word8 aPerm bPerm (70694 : Fin 306936) = 235873 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 70694 = 235873 from by decide +kernel)

private theorem eval5_235873 : Word.word5 aPerm bPerm (235873 : Fin 306936) = 306862 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 235873 = 306862 from by decide +kernel)

private theorem eval8_306862 : Word.word8 aPerm bPerm (306862 : Fin 306936) = 72131 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 306862 = 72131 from by decide +kernel)

private theorem eval8_72131 : Word.word8 aPerm bPerm (72131 : Fin 306936) = 69901 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 72131 = 69901 from by decide +kernel)

private theorem eval9_70959 : Word.word9 aPerm bPerm (70959 : Fin 306936) = 509 := by
  simp only [Word.word9, Equiv.Perm.mul_apply, eval5_70959, eval8_76965, eval5_304053, eval8_304285, eval5_66297, eval8_198969, eval5_235726, eval5_71287, eval8_70694, eval5_235873, eval8_306862, eval8_72131, eval5_69901, eval5_65657, eval8_180650]

private theorem eval11_509 : Word.word11 aPerm bPerm (509 : Fin 306936) = 509 := by
  have hinv0 : (Word.word10 aPerm bPerm)⁻¹ (509 : Fin 306936) = 304138 := by
    exact (Word.word10 aPerm bPerm).symm_apply_eq.mpr eval10_304138.symm
  simp only [Word.word11, Equiv.Perm.mul_apply, hinv0, eval5_304138, eval9_70959]

private theorem eval5_65901 : Word.word5 aPerm bPerm (65901 : Fin 306936) = 74948 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 65901 = 74948 from by decide +kernel)

private theorem eval8_74948 : Word.word8 aPerm bPerm (74948 : Fin 306936) = 65208 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 74948 = 65208 from by decide +kernel)

private theorem eval8_65208 : Word.word8 aPerm bPerm (65208 : Fin 306936) = 75616 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 65208 = 75616 from by decide +kernel)

private theorem eval5_75616 : Word.word5 aPerm bPerm (75616 : Fin 306936) = 74032 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 75616 = 74032 from by decide +kernel)

private theorem eval8_74032 : Word.word8 aPerm bPerm (74032 : Fin 306936) = 306378 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 74032 = 306378 from by decide +kernel)

private theorem eval5_306378 : Word.word5 aPerm bPerm (306378 : Fin 306936) = 67996 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 306378 = 67996 from by decide +kernel)

private theorem eval5_67996 : Word.word5 aPerm bPerm (67996 : Fin 306936) = 117845 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 67996 = 117845 from by decide +kernel)

private theorem eval8_117845 : Word.word8 aPerm bPerm (117845 : Fin 306936) = 76157 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 117845 = 76157 from by decide +kernel)

private theorem eval8_76157 : Word.word8 aPerm bPerm (76157 : Fin 306936) = 117807 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 76157 = 117807 from by decide +kernel)

private theorem eval8_117807 : Word.word8 aPerm bPerm (117807 : Fin 306936) = 72735 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 117807 = 72735 from by decide +kernel)

private theorem eval8_72735 : Word.word8 aPerm bPerm (72735 : Fin 306936) = 108733 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 72735 = 108733 from by decide +kernel)

private theorem eval8_108733 : Word.word8 aPerm bPerm (108733 : Fin 306936) = 79060 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 108733 = 79060 from by decide +kernel)

private theorem eval5_79060 : Word.word5 aPerm bPerm (79060 : Fin 306936) = 509 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 79060 = 509 from by decide +kernel)

private theorem eval13_65901 : Word.word13 aPerm bPerm (65901 : Fin 306936) = 509 := by
  simp only [Word.word13, Equiv.Perm.mul_apply, eval5_65901, eval8_74948, eval8_65208, eval5_75616, eval8_74032, eval5_306378, eval5_67996, eval8_117845, eval8_76157, eval8_117807, eval8_72735, eval8_108733, eval5_79060]

private theorem eval8_65901 : Word.word8 aPerm bPerm (65901 : Fin 306936) = 38177 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 65901 = 38177 from by decide +kernel)

private theorem eval5_38177 : Word.word5 aPerm bPerm (38177 : Fin 306936) = 118714 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 38177 = 118714 from by decide +kernel)

private theorem eval5_118714 : Word.word5 aPerm bPerm (118714 : Fin 306936) = 66510 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 118714 = 66510 from by decide +kernel)

private theorem eval5_66510 : Word.word5 aPerm bPerm (66510 : Fin 306936) = 72740 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 66510 = 72740 from by decide +kernel)

private theorem eval8_72740 : Word.word8 aPerm bPerm (72740 : Fin 306936) = 179534 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 72740 = 179534 from by decide +kernel)

private theorem eval8_179534 : Word.word8 aPerm bPerm (179534 : Fin 306936) = 69015 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 179534 = 69015 from by decide +kernel)

private theorem eval5_69015 : Word.word5 aPerm bPerm (69015 : Fin 306936) = 73266 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 69015 = 73266 from by decide +kernel)

private theorem eval5_73266 : Word.word5 aPerm bPerm (73266 : Fin 306936) = 116297 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 73266 = 116297 from by decide +kernel)

private theorem eval5_116297 : Word.word5 aPerm bPerm (116297 : Fin 306936) = 70979 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 116297 = 70979 from by decide +kernel)

private theorem eval8_70979 : Word.word8 aPerm bPerm (70979 : Fin 306936) = 108361 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 70979 = 108361 from by decide +kernel)

private theorem eval5_108361 : Word.word5 aPerm bPerm (108361 : Fin 306936) = 179641 := by
  apply Fin.ext
  rw [val_word5]
  exact (show rawWord5 108361 = 179641 from by decide +kernel)

private theorem eval8_179641 : Word.word8 aPerm bPerm (179641 : Fin 306936) = 180650 := by
  apply Fin.ext
  rw [val_word8]
  exact (show rawWord8 179641 = 180650 from by decide +kernel)

private theorem eval12_38177 : Word.word12 aPerm bPerm (38177 : Fin 306936) = 509 := by
  simp only [Word.word12, Equiv.Perm.mul_apply, eval5_38177, eval5_118714, eval5_66510, eval8_72740, eval8_179534, eval5_69015, eval5_73266, eval5_116297, eval8_70979, eval5_108361, eval8_179641, eval8_180650]

private theorem eval14_509 : Word.word14 aPerm bPerm (509 : Fin 306936) = 509 := by
  have hinv0 : (Word.word13 aPerm bPerm)⁻¹ (509 : Fin 306936) = 65901 := by
    exact (Word.word13 aPerm bPerm).symm_apply_eq.mpr eval13_65901.symm
  simp only [Word.word14, Equiv.Perm.mul_apply, hinv0, eval8_65901, eval12_38177]

/-- The literal stage generator fixes the preceding base label. -/
theorem word5_fixes_508 : Word.word5 aPerm bPerm (508 : Fin 306936) = 508 :=
  eval5_508

/-- The literal stage generator fixes the preceding base label. -/
theorem word8_fixes_508 : Word.word8 aPerm bPerm (508 : Fin 306936) = 508 :=
  eval8_508

/-- The literal stage generator fixes the preceding base label. -/
theorem word11_fixes_509 : Word.word11 aPerm bPerm (509 : Fin 306936) = 509 :=
  eval11_509

/-- The literal stage generator fixes the preceding base label. -/
theorem word14_fixes_509 : Word.word14 aPerm bPerm (509 : Fin 306936) = 509 :=
  eval14_509

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
