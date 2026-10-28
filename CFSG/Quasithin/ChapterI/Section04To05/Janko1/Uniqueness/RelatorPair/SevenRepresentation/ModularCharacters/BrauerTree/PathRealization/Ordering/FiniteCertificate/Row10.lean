module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.FiniteCertificate.Engine

/-!
# Finite path certificates with second ordinary row 10

The three possible following rows are 11, 12 and 13. Each branch is checked
in chunks of at most 48 paths. The exhaustive search and arithmetic soundness
are proved in `Engine`; these lists only propose witnesses. See
`source/README.md` for provenance and regeneration.
-/

-- Keep the measured arithmetic chunks sequential within this module.
set_option Elab.async false

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate

private def witnesses_10_11 : List Witness := [
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560)]

private theorem checked_10_11_0 :
    verify [0,10,11] ((branch 10 11).take 48)
      ((witnesses_10_11).take 48) = true := by
  decide +kernel

private theorem checked_10_11_1 :
    verify [0,10,11] ((branch 10 11).drop 48 |>.take 48)
      ((witnesses_10_11).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_10_11_2 :
    verify [0,10,11] ((branch 10 11).drop 48 |>.drop 48)
      ((witnesses_10_11).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_10_11 :
    ∀ p ∈ branch 10 11, Good (rowOf ([0,10,11] ++ p)) :=
  cover_split (verify_sound checked_10_11_0)
    (cover_split (verify_sound checked_10_11_1) (verify_sound checked_10_11_2))

private def witnesses_10_12 : List Witness := [
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,5,175560), some (1,6,6,175560),
  some (2,2,5,175560), some (1,6,6,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,5,175560), some (1,6,6,175560),
  some (2,2,5,175560), some (1,6,6,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,5,175560), some (2,2,5,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,7,175560), some (2,2,7,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,4,5,175560), some (1,6,6,175560), none, some (1,6,6,175560),
  some (2,7,3,175560), some (2,5,7,175560), some (2,4,6,175560), some (1,6,6,175560),
  some (2,5,8,175560), some (1,6,6,175560), some (2,4,8,175560), some (2,4,9,175560),
  some (2,4,7,175560), some (2,7,3,175560), some (2,4,8,175560), some (2,4,9,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560)]

private theorem checked_10_12_0 :
    verify [0,10,12] ((branch 10 12).take 48)
      ((witnesses_10_12).take 48) = true := by
  decide +kernel

private theorem checked_10_12_1 :
    verify [0,10,12] ((branch 10 12).drop 48 |>.take 48)
      ((witnesses_10_12).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_10_12_2 :
    verify [0,10,12] ((branch 10 12).drop 48 |>.drop 48)
      ((witnesses_10_12).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_10_12 :
    ∀ p ∈ branch 10 12, Good (rowOf ([0,10,12] ++ p)) :=
  cover_split (verify_sound checked_10_12_0)
    (cover_split (verify_sound checked_10_12_1) (verify_sound checked_10_12_2))

private def witnesses_10_13 : List Witness := [
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,5,175560), some (1,6,6,175560),
  some (2,2,5,175560), some (1,6,6,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,5,175560), some (1,6,6,175560),
  some (2,2,5,175560), some (1,6,6,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560), some (1,5,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,4,175560), some (1,6,6,175560),
  some (2,2,4,175560), some (1,6,6,175560), some (2,2,4,175560), some (2,2,4,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,6,175560), some (2,2,6,175560), some (2,2,8,175560), some (2,2,6,175560),
  some (2,2,8,175560), some (2,2,6,175560), some (2,2,6,175560), some (2,2,6,175560),
  some (2,2,5,175560), some (2,2,5,175560), some (2,2,5,175560), some (2,2,5,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,7,175560), some (2,2,7,175560), some (2,2,9,175560), some (2,2,6,175560),
  some (2,2,9,175560), some (2,2,6,175560), some (2,2,7,175560), some (2,2,7,175560),
  some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560), some (2,2,4,175560),
  none, some (1,6,6,175560), some (2,4,5,175560), some (1,6,6,175560),
  some (2,5,7,175560), some (2,7,3,175560), some (2,5,8,175560), some (1,6,6,175560),
  some (2,4,6,175560), some (1,6,6,175560), some (2,4,9,175560), some (2,4,8,175560),
  some (2,7,3,175560), some (2,4,7,175560), some (2,4,9,175560), some (2,4,8,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (1,6,6,175560),
  some (2,2,3,175560), some (1,6,6,175560), some (2,2,3,175560), some (2,2,3,175560),
  some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560), some (2,2,3,175560)]

private theorem checked_10_13_0 :
    verify [0,10,13] ((branch 10 13).take 48)
      ((witnesses_10_13).take 48) = true := by
  decide +kernel

private theorem checked_10_13_1 :
    verify [0,10,13] ((branch 10 13).drop 48 |>.take 48)
      ((witnesses_10_13).drop 48 |>.take 48) = true := by
  decide +kernel

private theorem checked_10_13_2 :
    verify [0,10,13] ((branch 10 13).drop 48 |>.drop 48)
      ((witnesses_10_13).drop 48 |>.drop 48) = true := by
  decide +kernel

private theorem complete_10_13 :
    ∀ p ∈ branch 10 13, Good (rowOf ([0,10,13] ++ p)) :=
  cover_split (verify_sound checked_10_13_0)
    (cover_split (verify_sound checked_10_13_1) (verify_sound checked_10_13_2))

/-- All three branches following the ordinary row 10 are certified. -/
public theorem row10_good (b : Row) (hb : b = 11 ∨ b = 12 ∨ b = 13) :
    ∀ p ∈ branch 10 b, Good (rowOf ([0,10,b] ++ p)) := by
  rcases hb with rfl | rfl | rfl
  · exact complete_10_11
  · exact complete_10_12
  · exact complete_10_13

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering.FiniteCertificate
