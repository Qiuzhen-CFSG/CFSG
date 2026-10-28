module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Engine

/-!
# Finite path certificates with second ordinary row 3

The three possible following rows are 11, 12 and 13. Each branch is checked
in chunks of at most 48 paths. The exhaustive search and arithmetic soundness
are proved in `Engine`; these lists only propose witnesses. See
`source/README.md` for provenance and regeneration.
-/

-- Keep the measured arithmetic chunks sequential within this module.
set_option Elab.async false

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate

private def witnesses_3_11 : List Witness := [
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560), some (1,3,1,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (4,5,0,175560), some (4,5,0,175560),
  some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560), some (1,5,1,175560),
  some (3,6,0,175560), some (3,6,0,175560), some (2,6,5,175560), some (2,6,5,175560),
  some (4,5,0,175560), some (4,5,0,175560), some (3,6,0,175560), some (3,6,0,175560),
  some (2,6,5,175560), some (2,6,5,175560), some (4,5,0,175560), some (4,5,0,175560)]

private theorem checked_3_11_0 :
    verify [0,3,11] ((branch 3 11).take 48)
      ((witnesses_3_11).take 48) = true := by
  decide +kernel

private theorem checked_3_11_1 :
    verify [0,3,11] ((branch 3 11).drop 48 |>.take 48)
      ((witnesses_3_11).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_3_11_2 :
    verify [0,3,11] ((branch 3 11).drop 48 |>.drop 48)
      ((witnesses_3_11).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_3_11 :
    ∀ p ∈ branch 3 11, Good (rowOf ([0,3,11] ++ p)) :=
  cover_split (verify_sound checked_3_11_0)
    (cover_split (verify_sound checked_3_11_1) (verify_sound checked_3_11_2))

private def witnesses_3_12 : List Witness := [
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560)]

private theorem checked_3_12_0 :
    verify [0,3,12] ((branch 3 12).take 48)
      ((witnesses_3_12).take 48) = true := by
  decide +kernel

private theorem checked_3_12_1 :
    verify [0,3,12] ((branch 3 12).drop 48 |>.take 48)
      ((witnesses_3_12).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_3_12_2 :
    verify [0,3,12] ((branch 3 12).drop 48 |>.drop 48)
      ((witnesses_3_12).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_3_12 :
    ∀ p ∈ branch 3 12, Good (rowOf ([0,3,12] ++ p)) :=
  cover_split (verify_sound checked_3_12_0)
    (cover_split (verify_sound checked_3_12_1) (verify_sound checked_3_12_2))

private def witnesses_3_13 : List Witness := [
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560), some (1,5,2,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560), some (2,3,0,175560),
  some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560), some (1,5,4,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (2,3,0,175560), some (2,3,0,175560), some (1,6,0,175560), some (1,6,0,175560),
  some (1,6,0,175560), some (1,6,0,175560), some (2,3,0,175560), some (2,3,0,175560)]

private theorem checked_3_13_0 :
    verify [0,3,13] ((branch 3 13).take 48)
      ((witnesses_3_13).take 48) = true := by
  decide +kernel

private theorem checked_3_13_1 :
    verify [0,3,13] ((branch 3 13).drop 48 |>.take 48)
      ((witnesses_3_13).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_3_13_2 :
    verify [0,3,13] ((branch 3 13).drop 48 |>.drop 48)
      ((witnesses_3_13).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_3_13 :
    ∀ p ∈ branch 3 13, Good (rowOf ([0,3,13] ++ p)) :=
  cover_split (verify_sound checked_3_13_0)
    (cover_split (verify_sound checked_3_13_1) (verify_sound checked_3_13_2))

/-- All three branches following the ordinary row 3 are certified. -/
public theorem row3_good (b : Row) (hb : b = 11 ∨ b = 12 ∨ b = 13) :
    ∀ p ∈ branch 3 b, Good (rowOf ([0,3,b] ++ p)) := by
  rcases hb with rfl | rfl | rfl
  · exact complete_3_11
  · exact complete_3_12
  · exact complete_3_13

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate
