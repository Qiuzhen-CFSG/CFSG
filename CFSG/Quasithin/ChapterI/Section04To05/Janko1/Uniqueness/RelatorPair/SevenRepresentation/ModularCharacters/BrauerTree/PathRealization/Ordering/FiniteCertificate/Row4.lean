module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Engine

/-!
# Finite path certificates with second ordinary row 4

The three possible following rows are 11, 12 and 13. Each branch is checked
in chunks of at most 48 paths. The exhaustive search and arithmetic soundness
are proved in `Engine`; these lists only propose witnesses. See
`source/README.md` for provenance and regeneration.
-/

-- Keep the measured arithmetic chunks sequential within this module.
set_option Elab.async false

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate

private def witnesses_4_11 : List Witness := [
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120), some (2,3,2,351120),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560),
  some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560), some (2,3,5,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (2,3,8,175560), some (2,3,8,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (2,3,8,175560), some (2,3,8,175560)]

private theorem checked_4_11_0 :
    verify [0,4,11] ((branch 4 11).take 48)
      ((witnesses_4_11).take 48) = true := by
  decide +kernel

private theorem checked_4_11_1 :
    verify [0,4,11] ((branch 4 11).drop 48 |>.take 48)
      ((witnesses_4_11).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_4_11_2 :
    verify [0,4,11] ((branch 4 11).drop 48 |>.drop 48)
      ((witnesses_4_11).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_4_11 :
    ∀ p ∈ branch 4 11, Good (rowOf ([0,4,11] ++ p)) :=
  cover_split (verify_sound checked_4_11_0)
    (cover_split (verify_sound checked_4_11_1) (verify_sound checked_4_11_2))

private def witnesses_4_12 : List Witness := [
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (5,8,9,175560), some (6,7,0,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (5,8,9,175560), some (6,7,0,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (5,8,9,175560), some (6,7,0,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (5,8,9,175560), some (6,7,0,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (5,8,9,175560), some (6,7,0,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (5,8,9,175560), some (6,7,0,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560)]

private theorem checked_4_12_0 :
    verify [0,4,12] ((branch 4 12).take 48)
      ((witnesses_4_12).take 48) = true := by
  decide +kernel

private theorem checked_4_12_1 :
    verify [0,4,12] ((branch 4 12).drop 48 |>.take 48)
      ((witnesses_4_12).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_4_12_2 :
    verify [0,4,12] ((branch 4 12).drop 48 |>.drop 48)
      ((witnesses_4_12).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_4_12 :
    ∀ p ∈ branch 4 12, Good (rowOf ([0,4,12] ++ p)) :=
  cover_split (verify_sound checked_4_12_0)
    (cover_split (verify_sound checked_4_12_1) (verify_sound checked_4_12_2))

private def witnesses_4_13 : List Witness := [
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (6,7,0,175560), some (5,8,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (6,7,0,175560), some (5,8,9,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (6,7,0,175560), some (5,8,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (6,7,0,175560), some (5,8,9,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (6,7,0,175560), some (5,8,9,175560), some (1,6,6,175560), some (1,6,9,175560),
  some (1,6,6,175560), some (1,6,9,175560), some (6,7,0,175560), some (5,8,9,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560)]

private theorem checked_4_13_0 :
    verify [0,4,13] ((branch 4 13).take 48)
      ((witnesses_4_13).take 48) = true := by
  decide +kernel

private theorem checked_4_13_1 :
    verify [0,4,13] ((branch 4 13).drop 48 |>.take 48)
      ((witnesses_4_13).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_4_13_2 :
    verify [0,4,13] ((branch 4 13).drop 48 |>.drop 48)
      ((witnesses_4_13).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_4_13 :
    ∀ p ∈ branch 4 13, Good (rowOf ([0,4,13] ++ p)) :=
  cover_split (verify_sound checked_4_13_0)
    (cover_split (verify_sound checked_4_13_1) (verify_sound checked_4_13_2))

/-- All three branches following the ordinary row 4 are certified. -/
public theorem row4_good (b : Row) (hb : b = 11 ∨ b = 12 ∨ b = 13) :
    ∀ p ∈ branch 4 b, Good (rowOf ([0,4,b] ++ p)) := by
  rcases hb with rfl | rfl | rfl
  · exact complete_4_11
  · exact complete_4_12
  · exact complete_4_13

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate
