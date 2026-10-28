module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.RootMatrices
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co1.CentralizerSection.OrthogonalEmbedding.Reduction

/-!
# Six checked Siegel words in the Co₁ local matrix image

Each word is evaluated in ten-step blocks using checked packed multiplication.
The final coordinate matrices are identified with the actual Siegel generators
by `rootGenerator_val`. All arithmetic is checked by the Lean kernel.

Reproduce with `source/generate.py`; word provenance and performance measurements
are recorded in `source/README.md`. The words use the literal `smallX` and `smallY`.
-/

@[expose] public section
-- Measured ten-step checks avoid retaining one large reduction; serial declaration
-- elaboration reduced the sample's peak RSS from 2.77 GB to 2.46 GB.
set_option Elab.async false
namespace Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
private def root0Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(false, ![175, 95, 44, 48, 87, 135, 80, 5]),
(true, ![12, 41, 1, 234, 170, 225, 51, 45]),
(true, ![111, 44, 193, 150, 33, 96, 159, 192]),
(true, ![195, 1, 14, 164, 175, 217, 230, 207]),
(true, ![186, 193, 219, 250, 12, 9, 249, 213]),
(true, ![165, 14, 189, 18, 111, 66, 103, 102]),
(true, ![59, 219, 60, 48, 195, 3, 64, 129])]

private theorem root0Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) :=
  valid_mem (Matrices.identityRows 8) root0Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root0Steps1 : List Step := [(false, ![165, 175, 67, 174, 110, 157, 161, 185]),
(true, ![59, 12, 194, 205, 2, 82, 215, 208]),
(true, ![28, 111, 123, 97, 180, 135, 210, 75]),
(true, ![235, 195, 171, 24, 126, 225, 255, 65]),
(true, ![87, 186, 224, 7, 134, 96, 63, 118]),
(true, ![170, 165, 161, 153, 32, 217, 240, 5]),
(true, ![33, 59, 215, 190, 110, 9, 37, 45]),
(true, ![175, 28, 210, 73, 2, 66, 67, 192]),
(true, ![12, 235, 255, 245, 180, 3, 194, 207]),
(true, ![111, 87, 63, 8, 126, 117, 123, 213])]

private theorem root0Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) :=
  valid_mem (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) root0Steps1 (by decide +kernel) (root0Prefix0)

private def root0Steps2 : List Step := [(true, ![195, 170, 240, 131, 134, 112, 171, 102]),
(false, ![110, 75, 93, 207, 95, 15, 160, 85]),
(true, ![2, 65, 157, 213, 41, 26, 22, 30]),
(true, ![180, 118, 82, 102, 44, 179, 220, 95]),
(true, ![126, 5, 135, 129, 1, 231, 36, 41]),
(true, ![134, 45, 225, 185, 193, 56, 130, 44]),
(true, ![32, 192, 96, 208, 14, 105, 204, 1]),
(true, ![110, 207, 217, 75, 219, 155, 160, 193]),
(true, ![2, 213, 9, 65, 189, 10, 22, 14]),
(true, ![180, 102, 66, 118, 60, 55, 220, 219])]

private theorem root0Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) :=
  valid_mem (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) root0Steps2 (by decide +kernel) (root0Prefix1)

private def root0Steps3 : List Step := [(true, ![126, 129, 3, 5, 133, 115, 36, 189]),
(true, ![134, 185, 117, 45, 85, 40, 130, 60]),
(true, ![32, 208, 112, 192, 30, 237, 204, 133]),
(false, ![249, 164, 15, 243, 204, 12, 30, 194]),
(true, ![103, 250, 26, 80, 160, 111, 95, 123]),
(true, ![64, 18, 179, 51, 22, 195, 41, 171]),
(true, ![183, 48, 231, 159, 220, 186, 44, 224]),
(true, ![11, 234, 56, 230, 36, 165, 1, 161]),
(true, ![246, 150, 105, 249, 130, 59, 193, 215]),
(true, ![125, 164, 155, 103, 204, 28, 14, 210])]

private theorem root0Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) :=
  valid_mem (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) root0Steps3 (by decide +kernel) (root0Prefix2)

private def root0Steps4 : List Step := [(true, ![243, 250, 10, 64, 160, 235, 219, 255]),
(true, ![80, 18, 55, 183, 22, 87, 189, 63]),
(true, ![51, 48, 115, 11, 220, 170, 60, 240]),
(false, ![51, 174, 146, 11, 73, 75, 67, 93]),
(true, ![159, 205, 72, 246, 245, 65, 194, 157]),
(false, ![117, 245, 55, 80, 205, 74, 133, 3]),
(true, ![112, 8, 115, 51, 97, 128, 85, 117]),
(true, ![93, 131, 40, 159, 24, 120, 30, 112]),
(true, ![157, 13, 237, 230, 7, 222, 95, 93]),
(true, ![82, 174, 15, 249, 153, 144, 41, 157])]

private theorem root0Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) :=
  valid_mem (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) root0Steps4 (by decide +kernel) (root0Prefix3)

private def root0Steps5 : List Step := [(true, ![135, 205, 26, 103, 190, 252, 44, 82]),
(true, ![225, 97, 179, 64, 73, 74, 1, 135]),
(true, ![96, 24, 231, 183, 245, 128, 193, 225]),
(true, ![217, 7, 56, 11, 8, 120, 14, 96]),
(false, ![217, 230, 56, 11, 150, 153, 155, 88]),
(true, ![9, 249, 105, 246, 164, 190, 10, 176]),
(false, ![125, 32, 37, 80, 208, 103, 224, 252]),
(true, ![243, 110, 67, 51, 75, 64, 161, 74]),
(false, ![192, 195, 60, 51, 170, 161, 64, 65]),
(true, ![207, 186, 133, 159, 33, 215, 183, 118])]

private theorem root0Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) :=
  valid_mem (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) root0Steps5 (by decide +kernel) (root0Prefix4)

private def root0Steps6 : List Step := [(true, ![213, 165, 85, 230, 175, 210, 11, 5]),
(true, ![102, 59, 30, 249, 12, 255, 246, 45]),
(true, ![129, 28, 95, 103, 111, 63, 125, 192]),
(true, ![185, 235, 41, 64, 195, 240, 243, 207]),
(true, ![208, 87, 44, 183, 186, 37, 80, 213]),
(true, ![75, 170, 1, 11, 165, 67, 51, 102]),
(true, ![65, 33, 193, 246, 59, 194, 159, 129]),
(true, ![118, 175, 14, 125, 28, 123, 230, 185]),
(true, ![5, 12, 219, 243, 235, 171, 249, 208]),
(true, ![45, 111, 189, 80, 87, 224, 103, 75])]

private theorem root0Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![45, 111, 189, 80, 87, 224, 103, 75] : Rows) :=
  valid_mem (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) root0Steps6 (by decide +kernel) (root0Prefix5)

private def root0Steps7 : List Step := [(false, ![255, 40, 250, 246, 16, 10, 190, 170]),
(true, ![63, 237, 18, 125, 132, 55, 73, 33]),
(false, ![222, 12, 33, 9, 41, 72, 220, 18]),
(true, ![144, 111, 175, 66, 44, 52, 36, 48]),
(false, ![5, 40, 219, 215, 20, 213, 130, 174]),
(true, ![45, 237, 189, 210, 104, 102, 204, 205]),
(true, ![192, 15, 60, 255, 90, 129, 160, 97]),
(true, ![207, 26, 133, 63, 4, 185, 22, 24]),
(true, ![213, 179, 85, 240, 236, 208, 220, 7]),
(true, ![102, 231, 30, 37, 206, 75, 36, 153])]

private theorem root0Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![102, 231, 30, 37, 206, 75, 36, 153] : Rows) :=
  valid_mem (![45, 111, 189, 80, 87, 224, 103, 75] : Rows) root0Steps7 (by decide +kernel) (root0Prefix6)

private def root0Steps8 : List Step := [(true, ![129, 56, 95, 67, 20, 65, 130, 190]),
(true, ![185, 105, 41, 194, 104, 118, 204, 73]),
(true, ![208, 155, 44, 123, 90, 5, 160, 245]),
(true, ![75, 10, 1, 171, 4, 45, 22, 8]),
(true, ![65, 55, 193, 224, 236, 192, 220, 131]),
(true, ![118, 115, 14, 161, 206, 207, 36, 13]),
(false, ![2, 146, 155, 64, 104, 131, 130, 6]),
(true, ![180, 72, 10, 183, 90, 13, 204, 88]),
(true, ![126, 52, 55, 11, 4, 174, 160, 176]),
(true, ![134, 6, 115, 246, 236, 205, 22, 146])]

private theorem root0Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![134, 6, 115, 246, 236, 205, 22, 146] : Rows) :=
  valid_mem (![102, 231, 30, 37, 206, 75, 36, 153] : Rows) root0Steps8 (by decide +kernel) (root0Prefix7)

private def root0Steps9 : List Step := [(true, ![32, 88, 40, 125, 206, 97, 220, 72]),
(true, ![110, 176, 237, 243, 20, 24, 36, 52]),
(true, ![2, 146, 15, 80, 104, 7, 130, 6]),
(true, ![180, 72, 26, 51, 90, 153, 204, 88]),
(true, ![126, 52, 179, 159, 4, 190, 160, 176]),
(true, ![134, 6, 231, 230, 236, 73, 22, 146]),
(true, ![32, 88, 56, 249, 206, 245, 220, 72]),
(true, ![110, 176, 105, 103, 20, 8, 36, 52]),
(false, ![195, 252, 37, 190, 44, 150, 130, 213]),
(true, ![186, 74, 67, 73, 1, 164, 204, 102])]

private theorem root0Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![186, 74, 67, 73, 1, 164, 204, 102] : Rows) :=
  valid_mem (![134, 6, 115, 246, 236, 205, 22, 146] : Rows) root0Steps9 (by decide +kernel) (root0Prefix8)

private def root0Steps10 : List Step := [(true, ![165, 128, 194, 245, 193, 250, 160, 129]),
(true, ![59, 120, 123, 8, 14, 18, 22, 185]),
(true, ![28, 222, 171, 131, 219, 48, 220, 208]),
(true, ![235, 144, 224, 13, 189, 234, 36, 75]),
(true, ![87, 252, 161, 174, 60, 150, 130, 65]),
(true, ![170, 74, 215, 205, 133, 164, 204, 118]),
(true, ![33, 128, 210, 97, 85, 250, 160, 5]),
(true, ![175, 120, 255, 24, 30, 18, 22, 45]),
(true, ![12, 222, 63, 7, 95, 48, 220, 192]),
(false, ![237, 63, 222, 230, 134, 174, 73, 243])]

private theorem root0Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![237, 63, 222, 230, 134, 174, 73, 243] : Rows) :=
  valid_mem (![186, 74, 67, 73, 1, 164, 204, 102] : Rows) root0Steps10 (by decide +kernel) (root0Prefix9)

private def root0Steps11 : List Step := [(true, ![15, 240, 144, 249, 32, 205, 245, 80]),
(true, ![26, 37, 252, 103, 110, 97, 8, 51]),
(true, ![179, 67, 74, 64, 2, 24, 131, 159]),
(true, ![231, 194, 128, 183, 180, 7, 13, 230]),
(true, ![56, 123, 120, 11, 126, 153, 174, 249]),
(true, ![105, 171, 222, 246, 134, 190, 205, 103]),
(true, ![155, 224, 144, 125, 32, 73, 97, 64]),
(true, ![10, 161, 252, 243, 110, 245, 24, 183]),
(true, ![55, 215, 74, 80, 2, 8, 7, 11]),
(true, ![115, 210, 128, 51, 180, 131, 153, 246])]

private theorem root0Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![115, 210, 128, 51, 180, 131, 153, 246] : Rows) :=
  valid_mem (![237, 63, 222, 230, 134, 174, 73, 243] : Rows) root0Steps11 (by decide +kernel) (root0Prefix10)

private def root0Steps12 : List Step := [(true, ![40, 255, 120, 159, 126, 13, 190, 125]),
(false, ![111, 45, 153, 117, 148, 6, 103, 9]),
(true, ![195, 192, 190, 112, 16, 88, 64, 66]),
(true, ![186, 207, 73, 93, 132, 176, 183, 3]),
(false, ![28, 131, 220, 240, 41, 252, 26, 157]),
(true, ![235, 13, 36, 37, 44, 74, 179, 82]),
(true, ![87, 174, 130, 67, 1, 128, 231, 135]),
(true, ![170, 205, 204, 194, 193, 120, 56, 225]),
(true, ![33, 97, 160, 123, 14, 222, 105, 96]),
(true, ![175, 24, 22, 171, 219, 144, 155, 217])]

private theorem root0Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![175, 24, 22, 171, 219, 144, 155, 217] : Rows) :=
  valid_mem (![115, 210, 128, 51, 180, 131, 153, 246] : Rows) root0Steps12 (by decide +kernel) (root0Prefix11)

private def root0Steps13 : List Step := [(true, ![12, 7, 220, 224, 189, 252, 10, 9]),
(true, ![111, 153, 36, 161, 60, 74, 55, 66]),
(true, ![195, 190, 130, 215, 133, 128, 115, 3]),
(true, ![186, 73, 204, 210, 85, 120, 40, 117]),
(true, ![165, 245, 160, 255, 30, 222, 237, 112]),
(true, ![59, 8, 22, 63, 95, 144, 15, 93]),
(false, ![165, 150, 90, 222, 134, 5, 112, 240]),
(true, ![59, 164, 4, 144, 32, 45, 93, 37]),
(true, ![28, 250, 236, 252, 110, 192, 157, 67]),
(true, ![235, 18, 206, 74, 2, 207, 82, 194])]

private theorem root0Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![235, 18, 206, 74, 2, 207, 82, 194] : Rows) :=
  valid_mem (![175, 24, 22, 171, 219, 144, 155, 217] : Rows) root0Steps13 (by decide +kernel) (root0Prefix12)

private def root0Steps14 : List Step := [(true, ![87, 48, 20, 128, 180, 213, 135, 123]),
(true, ![170, 234, 104, 120, 126, 102, 225, 171]),
(true, ![33, 150, 90, 222, 134, 129, 96, 224]),
(true, ![175, 164, 4, 144, 32, 185, 217, 161]),
(true, ![12, 250, 236, 252, 110, 208, 9, 215]),
(true, ![111, 18, 206, 74, 2, 75, 66, 210]),
(true, ![195, 48, 20, 128, 180, 65, 3, 255]),
(true, ![186, 234, 104, 120, 126, 118, 117, 63]),
(false, ![28, 234, 206, 153, 148, 2, 159, 222]),
(true, ![235, 150, 20, 190, 16, 180, 230, 144])]

private theorem root0Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![235, 150, 20, 190, 16, 180, 230, 144] : Rows) :=
  valid_mem (![235, 18, 206, 74, 2, 207, 82, 194] : Rows) root0Steps14 (by decide +kernel) (root0Prefix13)

private def root0Steps15 : List Step := [(true, ![87, 164, 104, 73, 132, 126, 249, 252]),
(true, ![170, 250, 90, 245, 148, 134, 103, 74]),
(true, ![33, 18, 4, 8, 16, 32, 64, 128])]

private theorem root0Prefix15 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![33, 18, 4, 8, 16, 32, 64, 128] : Rows) :=
  valid_mem (![235, 150, 20, 190, 16, 180, 230, 144] : Rows) root0Steps15 (by decide +kernel) (root0Prefix14)

theorem root0_mem : matrixHom (rootGenerator 0) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root0Prefix15
  have heq : matrixHom (rootGenerator 0) = g := by
    apply Units.ext
    exact (rootGenerator_val 0).trans hv.symm
  rw [heq]
  exact hg

private def root1Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(false, ![175, 95, 44, 48, 87, 135, 80, 5]),
(true, ![12, 41, 1, 234, 170, 225, 51, 45]),
(true, ![111, 44, 193, 150, 33, 96, 159, 192]),
(true, ![195, 1, 14, 164, 175, 217, 230, 207]),
(true, ![186, 193, 219, 250, 12, 9, 249, 213]),
(true, ![165, 14, 189, 18, 111, 66, 103, 102]),
(true, ![59, 219, 60, 48, 195, 3, 64, 129])]

private theorem root1Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) :=
  valid_mem (Matrices.identityRows 8) root1Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root1Steps1 : List Step := [(false, ![165, 175, 67, 174, 110, 157, 161, 185]),
(true, ![59, 12, 194, 205, 2, 82, 215, 208]),
(true, ![28, 111, 123, 97, 180, 135, 210, 75]),
(true, ![235, 195, 171, 24, 126, 225, 255, 65]),
(true, ![87, 186, 224, 7, 134, 96, 63, 118]),
(true, ![170, 165, 161, 153, 32, 217, 240, 5]),
(true, ![33, 59, 215, 190, 110, 9, 37, 45]),
(true, ![175, 28, 210, 73, 2, 66, 67, 192]),
(true, ![12, 235, 255, 245, 180, 3, 194, 207]),
(true, ![111, 87, 63, 8, 126, 117, 123, 213])]

private theorem root1Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) :=
  valid_mem (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) root1Steps1 (by decide +kernel) (root1Prefix0)

private def root1Steps2 : List Step := [(true, ![195, 170, 240, 131, 134, 112, 171, 102]),
(false, ![110, 75, 93, 207, 95, 15, 160, 85]),
(true, ![2, 65, 157, 213, 41, 26, 22, 30]),
(true, ![180, 118, 82, 102, 44, 179, 220, 95]),
(true, ![126, 5, 135, 129, 1, 231, 36, 41]),
(true, ![134, 45, 225, 185, 193, 56, 130, 44]),
(true, ![32, 192, 96, 208, 14, 105, 204, 1]),
(true, ![110, 207, 217, 75, 219, 155, 160, 193]),
(true, ![2, 213, 9, 65, 189, 10, 22, 14]),
(true, ![180, 102, 66, 118, 60, 55, 220, 219])]

private theorem root1Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) :=
  valid_mem (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) root1Steps2 (by decide +kernel) (root1Prefix1)

private def root1Steps3 : List Step := [(true, ![126, 129, 3, 5, 133, 115, 36, 189]),
(true, ![134, 185, 117, 45, 85, 40, 130, 60]),
(true, ![32, 208, 112, 192, 30, 237, 204, 133]),
(false, ![249, 164, 15, 243, 204, 12, 30, 194]),
(true, ![103, 250, 26, 80, 160, 111, 95, 123]),
(true, ![64, 18, 179, 51, 22, 195, 41, 171]),
(true, ![183, 48, 231, 159, 220, 186, 44, 224]),
(true, ![11, 234, 56, 230, 36, 165, 1, 161]),
(true, ![246, 150, 105, 249, 130, 59, 193, 215]),
(true, ![125, 164, 155, 103, 204, 28, 14, 210])]

private theorem root1Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) :=
  valid_mem (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) root1Steps3 (by decide +kernel) (root1Prefix2)

private def root1Steps4 : List Step := [(true, ![243, 250, 10, 64, 160, 235, 219, 255]),
(true, ![80, 18, 55, 183, 22, 87, 189, 63]),
(true, ![51, 48, 115, 11, 220, 170, 60, 240]),
(false, ![51, 174, 146, 11, 73, 75, 67, 93]),
(true, ![159, 205, 72, 246, 245, 65, 194, 157]),
(false, ![117, 245, 55, 80, 205, 74, 133, 3]),
(true, ![112, 8, 115, 51, 97, 128, 85, 117]),
(true, ![93, 131, 40, 159, 24, 120, 30, 112]),
(true, ![157, 13, 237, 230, 7, 222, 95, 93]),
(true, ![82, 174, 15, 249, 153, 144, 41, 157])]

private theorem root1Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) :=
  valid_mem (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) root1Steps4 (by decide +kernel) (root1Prefix3)

private def root1Steps5 : List Step := [(true, ![135, 205, 26, 103, 190, 252, 44, 82]),
(true, ![225, 97, 179, 64, 73, 74, 1, 135]),
(true, ![96, 24, 231, 183, 245, 128, 193, 225]),
(true, ![217, 7, 56, 11, 8, 120, 14, 96]),
(false, ![217, 230, 56, 11, 150, 153, 155, 88]),
(true, ![9, 249, 105, 246, 164, 190, 10, 176]),
(false, ![125, 32, 37, 80, 208, 103, 224, 252]),
(true, ![243, 110, 67, 51, 75, 64, 161, 74]),
(true, ![80, 2, 194, 159, 65, 183, 215, 128]),
(false, ![246, 118, 133, 117, 74, 26, 66, 82])]

private theorem root1Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![246, 118, 133, 117, 74, 26, 66, 82] : Rows) :=
  valid_mem (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) root1Steps5 (by decide +kernel) (root1Prefix4)

private def root1Steps6 : List Step := [(true, ![125, 5, 85, 112, 128, 179, 3, 135]),
(true, ![243, 45, 30, 93, 120, 231, 117, 225]),
(true, ![80, 192, 95, 157, 222, 56, 112, 96]),
(true, ![51, 207, 41, 82, 144, 105, 93, 217]),
(true, ![159, 213, 44, 135, 252, 155, 157, 9]),
(true, ![230, 102, 1, 225, 74, 10, 82, 66]),
(true, ![249, 129, 193, 96, 128, 55, 135, 3]),
(true, ![103, 185, 14, 217, 120, 115, 225, 117]),
(true, ![64, 208, 219, 9, 222, 40, 96, 112]),
(true, ![183, 75, 189, 66, 144, 237, 217, 93])]

private theorem root1Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![183, 75, 189, 66, 144, 237, 217, 93] : Rows) :=
  valid_mem (![246, 118, 133, 117, 74, 26, 66, 82] : Rows) root1Steps6 (by decide +kernel) (root1Prefix5)

private def root1Steps7 : List Step := [(true, ![11, 65, 60, 3, 252, 15, 9, 157]),
(false, ![11, 74, 67, 157, 176, 112, 125, 3]),
(true, ![246, 128, 194, 82, 146, 93, 243, 117]),
(true, ![125, 120, 123, 135, 72, 157, 80, 112]),
(true, ![243, 222, 171, 225, 52, 82, 51, 93]),
(true, ![80, 144, 224, 96, 6, 135, 159, 157]),
(true, ![51, 252, 161, 217, 88, 225, 230, 82]),
(true, ![159, 74, 215, 9, 176, 96, 249, 135]),
(true, ![230, 128, 210, 66, 146, 217, 103, 225]),
(true, ![249, 120, 255, 3, 72, 9, 64, 96])]

private theorem root1Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![249, 120, 255, 3, 72, 9, 64, 96] : Rows) :=
  valid_mem (![183, 75, 189, 66, 144, 237, 217, 93] : Rows) root1Steps7 (by decide +kernel) (root1Prefix6)

private def root1Steps8 : List Step := [(true, ![103, 222, 63, 117, 52, 66, 183, 217]),
(true, ![64, 144, 240, 112, 6, 3, 11, 9]),
(false, ![161, 5, 93, 15, 13, 157, 11, 125]),
(true, ![215, 45, 157, 26, 174, 82, 246, 243]),
(true, ![210, 192, 82, 179, 205, 135, 125, 80]),
(false, ![210, 243, 128, 97, 245, 180, 9, 246]),
(true, ![255, 80, 120, 24, 8, 126, 66, 125]),
(false, ![45, 246, 153, 193, 150, 148, 215, 9]),
(true, ![192, 125, 190, 14, 164, 16, 210, 66]),
(true, ![207, 243, 73, 219, 250, 132, 255, 3])]

private theorem root1Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![207, 243, 73, 219, 250, 132, 255, 3] : Rows) :=
  valid_mem (![249, 120, 255, 3, 72, 9, 64, 96] : Rows) root1Steps8 (by decide +kernel) (root1Prefix7)

private def root1Steps9 : List Step := [(true, ![213, 80, 245, 189, 18, 148, 63, 117]),
(true, ![102, 51, 8, 60, 48, 16, 240, 112]),
(true, ![129, 159, 131, 133, 234, 132, 37, 93]),
(true, ![185, 230, 13, 85, 150, 148, 67, 157]),
(true, ![208, 249, 174, 30, 164, 16, 194, 82]),
(true, ![75, 103, 205, 95, 250, 132, 123, 135]),
(true, ![65, 64, 97, 41, 18, 148, 171, 225]),
(true, ![118, 183, 24, 44, 48, 16, 224, 96]),
(true, ![5, 11, 7, 1, 234, 132, 161, 217]),
(false, ![144, 11, 230, 235, 234, 41, 64, 217])]

private theorem root1Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![144, 11, 230, 235, 234, 41, 64, 217] : Rows) :=
  valid_mem (![207, 243, 73, 219, 250, 132, 255, 3] : Rows) root1Steps9 (by decide +kernel) (root1Prefix8)

private def root1Steps10 : List Step := [(true, ![252, 246, 249, 87, 150, 44, 183, 9]),
(true, ![74, 125, 103, 170, 164, 1, 11, 66]),
(true, ![128, 243, 64, 33, 250, 193, 246, 3]),
(true, ![120, 80, 183, 175, 18, 14, 125, 117]),
(true, ![222, 51, 11, 12, 48, 219, 243, 112]),
(true, ![144, 159, 246, 111, 234, 189, 80, 93]),
(true, ![252, 230, 125, 195, 150, 60, 51, 157]),
(true, ![74, 249, 243, 186, 164, 133, 159, 82]),
(false, ![65, 32, 192, 28, 208, 194, 117, 128]),
(true, ![118, 110, 207, 235, 75, 123, 112, 120])]

private theorem root1Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![118, 110, 207, 235, 75, 123, 112, 120] : Rows) :=
  valid_mem (![144, 11, 230, 235, 234, 41, 64, 217] : Rows) root1Steps10 (by decide +kernel) (root1Prefix9)

private def root1Steps11 : List Step := [(true, ![5, 2, 213, 87, 65, 171, 93, 222]),
(true, ![45, 180, 102, 170, 118, 224, 157, 144]),
(false, ![255, 135, 85, 75, 2, 10, 3, 5]),
(true, ![63, 225, 30, 65, 180, 55, 117, 45]),
(false, ![222, 225, 204, 74, 135, 72, 159, 255]),
(true, ![144, 96, 160, 128, 225, 52, 230, 63]),
(true, ![252, 217, 22, 120, 96, 6, 249, 240]),
(false, ![176, 217, 90, 153, 88, 13, 32, 93]),
(true, ![146, 9, 4, 190, 176, 174, 110, 157]),
(true, ![72, 66, 236, 73, 146, 205, 2, 82])]

private theorem root1Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![72, 66, 236, 73, 146, 205, 2, 82] : Rows) :=
  valid_mem (![118, 110, 207, 235, 75, 123, 112, 120] : Rows) root1Steps11 (by decide +kernel) (root1Prefix10)

private def root1Steps12 : List Step := [(true, ![52, 3, 206, 245, 72, 97, 180, 135]),
(true, ![6, 117, 20, 8, 52, 24, 126, 225]),
(true, ![88, 112, 104, 131, 6, 7, 134, 96]),
(true, ![176, 93, 90, 13, 88, 153, 32, 217]),
(true, ![146, 157, 4, 174, 176, 190, 110, 9]),
(true, ![72, 82, 236, 205, 146, 73, 2, 66]),
(true, ![52, 135, 206, 97, 72, 245, 180, 3]),
(true, ![6, 225, 20, 24, 52, 8, 126, 117]),
(true, ![88, 96, 104, 7, 6, 131, 134, 112]),
(false, ![96, 88, 206, 230, 13, 207, 95, 15])]

private theorem root1Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![96, 88, 206, 230, 13, 207, 95, 15] : Rows) :=
  valid_mem (![72, 66, 236, 73, 146, 205, 2, 82] : Rows) root1Steps12 (by decide +kernel) (root1Prefix11)

private def root1Steps13 : List Step := [(true, ![217, 176, 20, 249, 174, 213, 41, 26]),
(true, ![9, 146, 104, 103, 205, 102, 44, 179]),
(false, ![125, 115, 206, 190, 245, 85, 20, 97]),
(true, ![243, 40, 20, 73, 8, 30, 104, 24]),
(true, ![80, 237, 104, 245, 131, 95, 90, 7]),
(true, ![51, 15, 90, 8, 13, 41, 4, 153]),
(false, ![51, 112, 22, 150, 6, 132, 123, 120]),
(true, ![159, 93, 220, 164, 88, 148, 171, 222]),
(true, ![230, 157, 36, 250, 176, 16, 224, 144]),
(true, ![249, 82, 130, 18, 146, 132, 161, 252])]

private theorem root1Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![249, 82, 130, 18, 146, 132, 161, 252] : Rows) :=
  valid_mem (![96, 88, 206, 230, 13, 207, 95, 15] : Rows) root1Steps13 (by decide +kernel) (root1Prefix12)

private def root1Steps14 : List Step := [(true, ![103, 135, 204, 48, 72, 148, 215, 74]),
(true, ![64, 225, 160, 234, 52, 16, 210, 128]),
(true, ![183, 96, 22, 150, 6, 132, 255, 120]),
(true, ![11, 217, 220, 164, 88, 148, 63, 222]),
(true, ![246, 9, 36, 250, 176, 16, 240, 144]),
(true, ![125, 66, 130, 18, 146, 132, 37, 252]),
(true, ![243, 3, 204, 48, 72, 148, 67, 74]),
(false, ![192, 157, 30, 174, 55, 126, 60, 65]),
(true, ![207, 82, 95, 205, 115, 134, 133, 118]),
(false, ![131, 128, 134, 245, 146, 95, 194, 2])]

private theorem root1Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![131, 128, 134, 245, 146, 95, 194, 2] : Rows) :=
  valid_mem (![249, 82, 130, 18, 146, 132, 161, 252] : Rows) root1Steps14 (by decide +kernel) (root1Prefix13)

private def root1Steps15 : List Step := [(true, ![13, 120, 32, 8, 72, 41, 123, 180]),
(true, ![174, 222, 110, 131, 52, 44, 171, 126]),
(true, ![205, 144, 2, 13, 6, 1, 224, 134]),
(true, ![97, 252, 180, 174, 88, 193, 161, 32]),
(true, ![24, 74, 126, 205, 176, 14, 215, 110]),
(true, ![7, 128, 134, 97, 146, 219, 210, 2]),
(true, ![153, 120, 32, 24, 72, 189, 255, 180]),
(true, ![190, 222, 110, 7, 52, 60, 63, 126]),
(true, ![73, 144, 2, 153, 6, 133, 240, 134]),
(true, ![245, 252, 180, 190, 88, 85, 37, 32])]

private theorem root1Prefix15 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![245, 252, 180, 190, 88, 85, 37, 32] : Rows) :=
  valid_mem (![131, 128, 134, 245, 146, 95, 194, 2] : Rows) root1Steps15 (by decide +kernel) (root1Prefix14)

private def root1Steps16 : List Step := [(true, ![8, 74, 126, 73, 176, 30, 67, 110]),
(false, ![150, 65, 148, 220, 252, 204, 60, 195]),
(true, ![164, 118, 16, 36, 74, 160, 133, 186]),
(true, ![250, 5, 132, 130, 128, 22, 85, 165]),
(true, ![18, 45, 148, 204, 120, 220, 30, 59]),
(false, ![33, 255, 126, 30, 153, 73, 204, 165]),
(true, ![175, 63, 134, 95, 190, 245, 160, 59]),
(true, ![12, 240, 32, 41, 73, 8, 22, 28]),
(true, ![111, 37, 110, 44, 245, 131, 220, 235]),
(true, ![195, 67, 2, 1, 8, 13, 36, 87])]

private theorem root1Prefix16 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![195, 67, 2, 1, 8, 13, 36, 87] : Rows) :=
  valid_mem (![245, 252, 180, 190, 88, 85, 37, 32] : Rows) root1Steps16 (by decide +kernel) (root1Prefix15)

private def root1Steps17 : List Step := [(true, ![186, 194, 180, 193, 131, 174, 130, 170]),
(true, ![165, 123, 126, 14, 13, 205, 204, 33]),
(true, ![59, 171, 134, 219, 174, 97, 160, 175]),
(true, ![28, 224, 32, 189, 205, 24, 22, 12]),
(true, ![235, 161, 110, 60, 97, 7, 220, 111]),
(true, ![87, 215, 2, 133, 24, 153, 36, 195]),
(true, ![170, 210, 180, 85, 7, 190, 130, 186]),
(false, ![75, 210, 135, 102, 230, 103, 36, 28]),
(true, ![65, 255, 225, 129, 249, 64, 130, 235]),
(true, ![118, 63, 96, 185, 103, 183, 204, 87])]

private theorem root1Prefix17 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![118, 63, 96, 185, 103, 183, 204, 87] : Rows) :=
  valid_mem (![195, 67, 2, 1, 8, 13, 36, 87] : Rows) root1Steps17 (by decide +kernel) (root1Prefix16)

private def root1Steps18 : List Step := [(true, ![5, 240, 217, 208, 64, 11, 160, 170]),
(false, ![144, 93, 217, 164, 161, 11, 171, 75]),
(true, ![252, 157, 9, 250, 215, 246, 224, 65]),
(true, ![74, 82, 66, 18, 210, 125, 161, 118]),
(true, ![128, 135, 3, 48, 255, 243, 215, 5]),
(true, ![120, 225, 117, 234, 63, 80, 210, 45]),
(true, ![222, 96, 112, 150, 240, 51, 255, 192]),
(true, ![144, 217, 93, 164, 37, 159, 63, 207]),
(false, ![5, 217, 240, 208, 105, 117, 222, 131]),
(true, ![45, 9, 37, 75, 155, 112, 144, 13])]

private theorem root1Prefix18 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![45, 9, 37, 75, 155, 112, 144, 13] : Rows) :=
  valid_mem (![118, 63, 96, 185, 103, 183, 204, 87] : Rows) root1Steps18 (by decide +kernel) (root1Prefix17)

private def root1Steps19 : List Step := [(false, ![255, 125, 105, 170, 14, 15, 5, 6]),
(true, ![63, 243, 155, 33, 219, 26, 45, 88]),
(true, ![240, 80, 10, 175, 189, 179, 192, 176]),
(true, ![37, 51, 55, 12, 60, 231, 207, 146]),
(true, ![67, 159, 115, 111, 133, 56, 213, 72]),
(true, ![194, 230, 40, 195, 85, 105, 102, 52]),
(true, ![123, 249, 237, 186, 30, 155, 129, 6]),
(true, ![171, 103, 15, 165, 95, 10, 185, 88]),
(true, ![224, 64, 26, 59, 41, 55, 208, 176]),
(true, ![161, 183, 179, 28, 44, 115, 75, 146])]

private theorem root1Prefix19 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![161, 183, 179, 28, 44, 115, 75, 146] : Rows) :=
  valid_mem (![45, 9, 37, 75, 155, 112, 144, 13] : Rows) root1Steps19 (by decide +kernel) (root1Prefix18)

private def root1Steps20 : List Step := [(true, ![215, 11, 231, 235, 1, 40, 65, 72]),
(true, ![210, 246, 56, 87, 193, 237, 118, 52]),
(true, ![255, 125, 105, 170, 14, 15, 5, 6]),
(true, ![63, 243, 155, 33, 219, 26, 45, 88]),
(false, ![222, 192, 14, 18, 175, 183, 255, 96]),
(true, ![144, 207, 219, 48, 12, 11, 63, 217]),
(true, ![252, 213, 189, 234, 111, 246, 240, 9]),
(true, ![74, 102, 60, 150, 195, 125, 37, 66]),
(true, ![128, 129, 133, 164, 186, 243, 67, 3]),
(true, ![120, 185, 85, 250, 165, 80, 194, 117])]

private theorem root1Prefix20 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![120, 185, 85, 250, 165, 80, 194, 117] : Rows) :=
  valid_mem (![161, 183, 179, 28, 44, 115, 75, 146] : Rows) root1Steps20 (by decide +kernel) (root1Prefix19)

private def root1Steps21 : List Step := [(true, ![222, 208, 30, 18, 59, 51, 123, 112]),
(true, ![144, 75, 95, 48, 28, 159, 171, 93]),
(true, ![252, 65, 41, 234, 235, 230, 224, 157]),
(true, ![74, 118, 44, 150, 87, 249, 161, 82]),
(false, ![65, 2, 20, 8, 16, 32, 64, 128])]

private theorem root1Prefix21 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![65, 2, 20, 8, 16, 32, 64, 128] : Rows) :=
  valid_mem (![120, 185, 85, 250, 165, 80, 194, 117] : Rows) root1Steps21 (by decide +kernel) (root1Prefix20)

theorem root1_mem : matrixHom (rootGenerator 1) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root1Prefix21
  have heq : matrixHom (rootGenerator 1) = g := by
    apply Units.ext
    exact (rootGenerator_val 1).trans hv.symm
  rw [heq]
  exact hg

private def root2Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(true, ![189, 32, 104, 205, 132, 126, 125, 252]),
(true, ![60, 110, 90, 97, 148, 134, 243, 74]),
(true, ![133, 2, 4, 24, 16, 32, 80, 128]),
(true, ![85, 180, 236, 7, 132, 110, 51, 120]),
(true, ![30, 126, 206, 153, 148, 2, 159, 222]),
(true, ![95, 134, 20, 190, 16, 180, 230, 144]),
(true, ![41, 32, 104, 73, 132, 126, 249, 252])]

private theorem root2Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![41, 32, 104, 73, 132, 126, 249, 252] : Rows) :=
  valid_mem (Matrices.identityRows 8) root2Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root2Steps1 : List Step := [(false, ![132, 249, 206, 220, 41, 148, 32, 176]),
(true, ![148, 103, 20, 36, 44, 16, 110, 146]),
(true, ![16, 64, 104, 130, 1, 132, 2, 72]),
(true, ![132, 183, 90, 204, 193, 148, 180, 52]),
(true, ![148, 11, 4, 160, 14, 16, 126, 6]),
(true, ![16, 246, 236, 22, 219, 132, 134, 88]),
(true, ![132, 125, 206, 220, 189, 148, 32, 176]),
(true, ![148, 243, 20, 36, 60, 16, 110, 146]),
(true, ![16, 80, 104, 130, 133, 132, 2, 72]),
(true, ![132, 51, 90, 204, 85, 148, 180, 52])]

private theorem root2Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![132, 51, 90, 204, 85, 148, 180, 52] : Rows) :=
  valid_mem (![41, 32, 104, 73, 132, 126, 249, 252] : Rows) root2Steps1 (by decide +kernel) (root2Prefix0)

private def root2Steps2 : List Step := [(true, ![148, 159, 4, 160, 30, 16, 126, 6]),
(true, ![16, 230, 236, 22, 95, 132, 134, 88]),
(false, ![87, 7, 231, 90, 134, 41, 95, 96]),
(true, ![170, 153, 56, 4, 32, 44, 41, 217]),
(true, ![33, 190, 105, 236, 110, 1, 44, 9]),
(true, ![175, 73, 155, 206, 2, 193, 1, 66]),
(true, ![12, 245, 10, 20, 180, 14, 193, 3]),
(false, ![237, 205, 224, 44, 135, 155, 24, 157]),
(true, ![15, 97, 161, 1, 225, 10, 7, 82]),
(true, ![26, 24, 215, 193, 96, 55, 153, 135])]

private theorem root2Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![26, 24, 215, 193, 96, 55, 153, 135] : Rows) :=
  valid_mem (![132, 51, 90, 204, 85, 148, 180, 52] : Rows) root2Steps2 (by decide +kernel) (root2Prefix1)

private def root2Steps3 : List Step := [(true, ![179, 7, 210, 14, 217, 115, 190, 225]),
(true, ![231, 153, 255, 219, 9, 40, 73, 96]),
(true, ![56, 190, 63, 189, 66, 237, 245, 217]),
(true, ![105, 73, 240, 60, 3, 15, 8, 9]),
(true, ![155, 245, 37, 133, 117, 26, 131, 66]),
(true, ![10, 8, 67, 85, 112, 179, 13, 3]),
(true, ![55, 131, 194, 30, 93, 231, 174, 117]),
(true, ![115, 13, 123, 95, 157, 56, 205, 112]),
(true, ![40, 174, 171, 41, 82, 105, 97, 93]),
(false, ![111, 48, 160, 132, 128, 37, 179, 240])]

private theorem root2Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 48, 160, 132, 128, 37, 179, 240] : Rows) :=
  valid_mem (![26, 24, 215, 193, 96, 55, 153, 135] : Rows) root2Steps3 (by decide +kernel) (root2Prefix2)

private def root2Steps4 : List Step := [(true, ![195, 234, 22, 148, 120, 67, 231, 37]),
(true, ![186, 150, 220, 16, 222, 194, 56, 67]),
(true, ![165, 164, 36, 132, 144, 123, 105, 194]),
(false, ![59, 208, 130, 41, 5, 4, 37, 133]),
(true, ![28, 75, 204, 44, 45, 236, 67, 85]),
(false, ![186, 170, 30, 20, 255, 231, 60, 102]),
(true, ![165, 33, 95, 104, 63, 56, 133, 129]),
(true, ![59, 175, 41, 90, 240, 105, 85, 185]),
(false, ![165, 219, 132, 22, 93, 37, 102, 129]),
(true, ![59, 189, 148, 220, 157, 67, 129, 185])]

private theorem root2Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 189, 148, 220, 157, 67, 129, 185] : Rows) :=
  valid_mem (![111, 48, 160, 132, 128, 37, 179, 240] : Rows) root2Steps4 (by decide +kernel) (root2Prefix3)

private def root2Steps5 : List Step := [(true, ![28, 60, 16, 36, 82, 194, 185, 208]),
(true, ![235, 133, 132, 130, 135, 123, 208, 75]),
(true, ![87, 85, 148, 204, 225, 171, 75, 65]),
(true, ![170, 30, 16, 160, 96, 224, 65, 118]),
(true, ![33, 95, 132, 22, 217, 161, 118, 5]),
(false, ![18, 134, 41, 90, 217, 64, 2, 144]),
(true, ![48, 32, 44, 4, 9, 183, 180, 252]),
(true, ![234, 110, 1, 236, 66, 11, 126, 74]),
(true, ![150, 2, 193, 206, 3, 246, 134, 128]),
(true, ![164, 180, 14, 20, 117, 125, 32, 120])]

private theorem root2Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![164, 180, 14, 20, 117, 125, 32, 120] : Rows) :=
  valid_mem (![59, 189, 148, 220, 157, 67, 129, 185] : Rows) root2Steps5 (by decide +kernel) (root2Prefix4)

private def root2Steps6 : List Step := [(true, ![250, 126, 219, 104, 112, 243, 110, 222]),
(true, ![18, 134, 189, 90, 93, 80, 2, 144]),
(true, ![48, 32, 60, 4, 157, 51, 180, 252]),
(true, ![234, 110, 133, 236, 82, 159, 126, 74]),
(false, ![234, 195, 194, 231, 128, 117, 148, 65]),
(true, ![150, 186, 123, 56, 120, 112, 16, 118]),
(false, ![8, 28, 4, 56, 153, 15, 87, 2]),
(true, ![131, 235, 236, 105, 190, 26, 170, 180]),
(true, ![13, 87, 206, 155, 73, 179, 33, 126]),
(true, ![174, 170, 20, 10, 245, 231, 175, 134])]

private theorem root2Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![174, 170, 20, 10, 245, 231, 175, 134] : Rows) :=
  valid_mem (![164, 180, 14, 20, 117, 125, 32, 120] : Rows) root2Steps6 (by decide +kernel) (root2Prefix5)

private def root2Steps7 : List Step := [(true, ![205, 33, 104, 55, 8, 56, 12, 32]),
(true, ![97, 175, 90, 115, 131, 105, 111, 110]),
(true, ![24, 12, 4, 40, 13, 155, 195, 2]),
(true, ![7, 111, 236, 237, 174, 10, 186, 180]),
(true, ![153, 195, 206, 15, 205, 55, 165, 126]),
(true, ![190, 186, 20, 26, 97, 115, 59, 134]),
(true, ![73, 165, 104, 179, 24, 40, 28, 32]),
(false, ![220, 59, 206, 97, 193, 111, 186, 249]),
(true, ![36, 28, 20, 24, 14, 195, 165, 103]),
(false, ![130, 186, 44, 193, 155, 110, 59, 190])]

private theorem root2Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![130, 186, 44, 193, 155, 110, 59, 190] : Rows) :=
  valid_mem (![174, 170, 20, 10, 245, 231, 175, 134] : Rows) root2Steps7 (by decide +kernel) (root2Prefix6)

private def root2Steps8 : List Step := [(true, ![204, 165, 1, 14, 10, 2, 28, 73]),
(true, ![160, 59, 193, 219, 55, 180, 235, 245]),
(true, ![22, 28, 14, 189, 115, 126, 87, 8]),
(false, ![90, 186, 155, 250, 146, 148, 16, 150]),
(true, ![4, 165, 10, 18, 72, 16, 132, 164]),
(true, ![236, 59, 55, 48, 52, 132, 148, 250]),
(true, ![206, 28, 115, 234, 6, 148, 16, 18]),
(true, ![20, 235, 40, 150, 88, 16, 132, 48]),
(true, ![104, 87, 237, 164, 176, 132, 148, 234]),
(true, ![90, 170, 15, 250, 146, 148, 16, 150])]

private theorem root2Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![90, 170, 15, 250, 146, 148, 16, 150] : Rows) :=
  valid_mem (![130, 186, 44, 193, 155, 110, 59, 190] : Rows) root2Steps8 (by decide +kernel) (root2Prefix7)

private def root2Steps9 : List Step := [(true, ![4, 33, 26, 18, 72, 16, 132, 164]),
(true, ![236, 175, 179, 48, 52, 132, 148, 250]),
(false, ![231, 219, 97, 174, 213, 41, 126, 189]),
(true, ![56, 189, 24, 205, 102, 44, 134, 60]),
(true, ![105, 60, 7, 97, 129, 1, 32, 133]),
(true, ![155, 133, 153, 24, 185, 193, 110, 85]),
(true, ![10, 85, 190, 7, 208, 14, 2, 30]),
(true, ![55, 30, 73, 153, 75, 219, 180, 95]),
(true, ![115, 95, 245, 190, 65, 189, 126, 41]),
(true, ![40, 41, 8, 73, 118, 60, 134, 44])]

private theorem root2Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![40, 41, 8, 73, 118, 60, 134, 44] : Rows) :=
  valid_mem (![90, 170, 15, 250, 146, 148, 16, 150] : Rows) root2Steps9 (by decide +kernel) (root2Prefix8)

private def root2Steps10 : List Step := [(true, ![237, 44, 131, 245, 5, 133, 32, 1]),
(true, ![15, 1, 13, 8, 45, 85, 110, 193]),
(true, ![26, 193, 174, 131, 192, 30, 2, 14]),
(false, ![183, 24, 48, 207, 243, 204, 118, 155]),
(true, ![11, 7, 234, 213, 80, 160, 5, 10]),
(true, ![246, 153, 150, 102, 51, 22, 45, 55]),
(true, ![125, 190, 164, 129, 159, 220, 192, 115]),
(false, ![9, 103, 208, 185, 117, 73, 243, 146]),
(true, ![66, 64, 75, 208, 112, 245, 80, 72]),
(true, ![3, 183, 65, 75, 93, 8, 51, 52])]

private theorem root2Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![3, 183, 65, 75, 93, 8, 51, 52] : Rows) :=
  valid_mem (![40, 41, 8, 73, 118, 60, 134, 44] : Rows) root2Steps10 (by decide +kernel) (root2Prefix9)

private def root2Steps11 : List Step := [(true, ![117, 11, 118, 65, 157, 131, 159, 6]),
(true, ![112, 246, 5, 118, 82, 13, 230, 88]),
(true, ![93, 125, 45, 5, 135, 174, 249, 176]),
(true, ![157, 243, 192, 45, 225, 205, 103, 146]),
(true, ![82, 80, 207, 192, 96, 97, 64, 72]),
(true, ![135, 51, 213, 207, 217, 24, 183, 52]),
(true, ![225, 159, 102, 213, 9, 7, 11, 6]),
(true, ![96, 230, 129, 102, 66, 153, 246, 88]),
(true, ![217, 249, 185, 129, 3, 190, 125, 176]),
(false, ![217, 32, 129, 185, 157, 103, 9, 252])]

private theorem root2Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![217, 32, 129, 185, 157, 103, 9, 252] : Rows) :=
  valid_mem (![3, 183, 65, 75, 93, 8, 51, 52] : Rows) root2Steps11 (by decide +kernel) (root2Prefix10)

private def root2Steps12 : List Step := [(true, ![9, 110, 185, 208, 82, 64, 66, 74]),
(true, ![66, 2, 208, 75, 135, 183, 3, 128]),
(false, ![215, 118, 164, 170, 180, 26, 157, 82]),
(true, ![210, 5, 250, 33, 126, 179, 82, 135]),
(true, ![255, 45, 18, 175, 134, 231, 135, 225]),
(true, ![63, 192, 48, 12, 32, 56, 225, 96]),
(true, ![240, 207, 234, 111, 110, 105, 96, 217]),
(true, ![37, 213, 150, 195, 2, 155, 217, 9]),
(true, ![67, 102, 164, 186, 180, 10, 9, 66]),
(true, ![194, 129, 250, 165, 126, 55, 66, 3])]

private theorem root2Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![194, 129, 250, 165, 126, 55, 66, 3] : Rows) :=
  valid_mem (![217, 32, 129, 185, 157, 103, 9, 252] : Rows) root2Steps12 (by decide +kernel) (root2Prefix11)

private def root2Steps13 : List Step := [(true, ![123, 185, 18, 59, 134, 115, 3, 117]),
(true, ![171, 208, 48, 28, 32, 40, 117, 112]),
(true, ![224, 75, 234, 235, 110, 237, 112, 93]),
(false, ![10, 170, 234, 1, 195, 12, 15, 240]),
(true, ![55, 33, 150, 193, 186, 111, 26, 37]),
(true, ![115, 175, 164, 14, 165, 195, 179, 67]),
(true, ![40, 12, 250, 219, 59, 186, 231, 194]),
(true, ![237, 111, 18, 189, 28, 165, 56, 123]),
(true, ![15, 195, 48, 60, 235, 59, 105, 171]),
(true, ![26, 186, 234, 133, 87, 28, 155, 224])]

private theorem root2Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![26, 186, 234, 133, 87, 28, 155, 224] : Rows) :=
  valid_mem (![194, 129, 250, 165, 126, 55, 66, 3] : Rows) root2Steps13 (by decide +kernel) (root2Prefix12)

private def root2Steps14 : List Step := [(false, ![183, 28, 234, 194, 16, 186, 14, 10]),
(true, ![11, 235, 150, 123, 132, 165, 219, 55]),
(true, ![246, 87, 164, 171, 148, 59, 189, 115]),
(false, ![80, 16, 208, 160, 126, 165, 250, 146]),
(true, ![51, 132, 75, 22, 134, 59, 18, 72]),
(false, ![51, 41, 170, 90, 95, 165, 33, 55]),
(true, ![159, 44, 33, 4, 41, 59, 175, 115]),
(true, ![230, 1, 175, 236, 44, 28, 12, 40]),
(true, ![249, 193, 12, 206, 1, 235, 111, 237]),
(true, ![103, 14, 111, 20, 193, 87, 195, 15])]

private theorem root2Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![103, 14, 111, 20, 193, 87, 195, 15] : Rows) :=
  valid_mem (![26, 186, 234, 133, 87, 28, 155, 224] : Rows) root2Steps14 (by decide +kernel) (root2Prefix13)

private def root2Steps15 : List Step := [(true, ![64, 219, 195, 104, 14, 170, 186, 26]),
(true, ![183, 189, 186, 90, 219, 33, 165, 179]),
(true, ![11, 60, 165, 4, 189, 175, 59, 231]),
(true, ![246, 133, 59, 236, 60, 12, 28, 56]),
(true, ![125, 85, 28, 206, 133, 111, 235, 105]),
(true, ![243, 30, 235, 20, 85, 195, 87, 155]),
(false, ![192, 204, 1, 44, 102, 110, 16, 14]),
(true, ![207, 160, 193, 1, 129, 2, 132, 219]),
(true, ![213, 22, 14, 193, 185, 180, 148, 189]),
(true, ![102, 220, 219, 14, 208, 126, 16, 60])]

private theorem root2Prefix15 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![102, 220, 219, 14, 208, 126, 16, 60] : Rows) :=
  valid_mem (![103, 14, 111, 20, 193, 87, 195, 15] : Rows) root2Steps15 (by decide +kernel) (root2Prefix14)

private def root2Steps16 : List Step := [(true, ![129, 36, 189, 219, 75, 134, 132, 133]),
(true, ![185, 130, 60, 189, 65, 32, 148, 85]),
(true, ![208, 204, 133, 60, 118, 110, 16, 30]),
(true, ![75, 160, 85, 133, 5, 2, 132, 95]),
(true, ![65, 22, 30, 85, 45, 180, 148, 41]),
(true, ![118, 220, 95, 30, 192, 126, 16, 44]),
(true, ![5, 36, 41, 95, 207, 134, 132, 1]),
(true, ![45, 130, 44, 41, 213, 32, 148, 193]),
(false, ![255, 36, 20, 132, 52, 249, 126, 24]),
(true, ![63, 130, 104, 148, 6, 103, 134, 7])]

private theorem root2Prefix16 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![63, 130, 104, 148, 6, 103, 134, 7] : Rows) :=
  valid_mem (![102, 220, 219, 14, 208, 126, 16, 60] : Rows) root2Steps16 (by decide +kernel) (root2Prefix15)

private def root2Steps17 : List Step := [(false, ![222, 36, 206, 126, 13, 190, 95, 230]),
(true, ![144, 130, 20, 134, 174, 73, 41, 249]),
(true, ![252, 204, 104, 32, 205, 245, 44, 103]),
(false, ![176, 30, 206, 249, 245, 205, 20, 190]),
(true, ![146, 95, 20, 103, 8, 97, 104, 73]),
(true, ![72, 41, 104, 64, 131, 24, 90, 245]),
(true, ![52, 44, 90, 183, 13, 7, 4, 8]),
(true, ![6, 1, 4, 11, 174, 153, 236, 131]),
(true, ![88, 193, 236, 246, 205, 190, 206, 13]),
(true, ![176, 14, 206, 125, 97, 73, 20, 174])]

private theorem root2Prefix17 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![176, 14, 206, 125, 97, 73, 20, 174] : Rows) :=
  valid_mem (![63, 130, 104, 148, 6, 103, 134, 7] : Rows) root2Steps17 (by decide +kernel) (root2Prefix16)

private def root2Steps18 : List Step := [(true, ![146, 219, 20, 243, 24, 245, 104, 205]),
(true, ![72, 189, 104, 80, 7, 8, 90, 97]),
(true, ![52, 60, 90, 51, 153, 131, 4, 24]),
(true, ![6, 133, 4, 159, 190, 13, 236, 7]),
(true, ![88, 85, 236, 230, 73, 174, 206, 153]),
(true, ![176, 30, 206, 249, 245, 205, 20, 190]),
(true, ![146, 95, 20, 103, 8, 97, 104, 73]),
(true, ![72, 41, 104, 64, 131, 24, 90, 245]),
(false, ![55, 132, 206, 161, 207, 193, 22, 205]),
(true, ![115, 148, 20, 215, 213, 14, 220, 97])]

private theorem root2Prefix18 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![115, 148, 20, 215, 213, 14, 220, 97] : Rows) :=
  valid_mem (![176, 14, 206, 125, 97, 73, 20, 174] : Rows) root2Steps18 (by decide +kernel) (root2Prefix17)

private def root2Steps19 : List Step := [(true, ![40, 16, 104, 210, 102, 219, 36, 24]),
(true, ![237, 132, 90, 255, 129, 189, 130, 7]),
(true, ![15, 148, 4, 63, 185, 60, 204, 153]),
(true, ![26, 16, 236, 240, 208, 133, 160, 190]),
(true, ![179, 132, 206, 37, 75, 85, 22, 73]),
(true, ![231, 148, 20, 67, 65, 30, 220, 245]),
(true, ![56, 16, 104, 194, 118, 95, 36, 8]),
(true, ![105, 132, 90, 123, 5, 41, 130, 131]),
(true, ![155, 148, 4, 171, 45, 44, 204, 13]),
(true, ![10, 16, 236, 224, 192, 1, 160, 174])]

private theorem root2Prefix19 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![10, 16, 236, 224, 192, 1, 160, 174] : Rows) :=
  valid_mem (![115, 148, 20, 215, 213, 14, 220, 97] : Rows) root2Steps19 (by decide +kernel) (root2Prefix18)

private def root2Steps20 : List Step := [(false, ![224, 87, 231, 10, 243, 235, 171, 48]),
(true, ![161, 170, 56, 55, 80, 87, 224, 234]),
(true, ![215, 33, 105, 115, 51, 170, 161, 150]),
(false, ![66, 18, 37, 146, 51, 75, 64, 8]),
(true, ![3, 48, 67, 72, 159, 65, 183, 131]),
(false, ![157, 174, 60, 55, 117, 74, 26, 207]),
(true, ![82, 205, 133, 115, 112, 128, 179, 213]),
(true, ![135, 97, 85, 40, 93, 120, 231, 102]),
(true, ![225, 24, 30, 237, 157, 222, 56, 129]),
(true, ![96, 7, 95, 15, 82, 144, 105, 185])]

private theorem root2Prefix20 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![96, 7, 95, 15, 82, 144, 105, 185] : Rows) :=
  valid_mem (![10, 16, 236, 224, 192, 1, 160, 174] : Rows) root2Steps20 (by decide +kernel) (root2Prefix19)

private def root2Steps21 : List Step := [(true, ![217, 153, 41, 26, 135, 252, 155, 208]),
(true, ![9, 190, 44, 179, 225, 74, 10, 75]),
(true, ![66, 73, 1, 231, 96, 128, 55, 65]),
(true, ![3, 245, 193, 56, 217, 120, 115, 118]),
(true, ![117, 8, 14, 105, 9, 222, 40, 5]),
(true, ![112, 131, 219, 155, 66, 144, 237, 45]),
(true, ![93, 13, 189, 10, 3, 252, 15, 192]),
(false, ![240, 6, 250, 224, 157, 176, 112, 243]),
(true, ![37, 88, 18, 161, 82, 146, 93, 80]),
(true, ![67, 176, 48, 215, 135, 72, 157, 51])]

private theorem root2Prefix21 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![67, 176, 48, 215, 135, 72, 157, 51] : Rows) :=
  valid_mem (![96, 7, 95, 15, 82, 144, 105, 185] : Rows) root2Steps21 (by decide +kernel) (root2Prefix20)

private def root2Steps22 : List Step := [(false, ![60, 252, 174, 66, 180, 55, 3, 51]),
(true, ![133, 74, 205, 3, 126, 115, 117, 159]),
(true, ![85, 128, 97, 117, 134, 40, 112, 230]),
(false, ![102, 82, 179, 159, 95, 111, 15, 7]),
(true, ![129, 135, 231, 230, 41, 195, 26, 153]),
(false, ![185, 180, 236, 7, 132, 110, 183, 120]),
(true, ![208, 126, 206, 153, 148, 2, 11, 222]),
(true, ![75, 134, 20, 190, 16, 180, 246, 144]),
(true, ![65, 32, 104, 73, 132, 126, 125, 252]),
(true, ![118, 110, 90, 245, 148, 134, 243, 74])]

private theorem root2Prefix22 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![118, 110, 90, 245, 148, 134, 243, 74] : Rows) :=
  valid_mem (![67, 176, 48, 215, 135, 72, 157, 51] : Rows) root2Steps22 (by decide +kernel) (root2Prefix21)

private def root2Steps23 : List Step := [(true, ![5, 2, 4, 8, 16, 32, 80, 128]),
(true, ![45, 180, 236, 131, 132, 110, 51, 120]),
(true, ![192, 126, 206, 13, 148, 2, 159, 222]),
(true, ![207, 134, 20, 174, 16, 180, 230, 144]),
(true, ![213, 32, 104, 205, 132, 126, 249, 252]),
(true, ![102, 110, 90, 97, 148, 134, 103, 74]),
(true, ![129, 2, 4, 24, 16, 32, 64, 128])]

private theorem root2Prefix23 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![129, 2, 4, 24, 16, 32, 64, 128] : Rows) :=
  valid_mem (![118, 110, 90, 245, 148, 134, 243, 74] : Rows) root2Steps23 (by decide +kernel) (root2Prefix22)

theorem root2_mem : matrixHom (rootGenerator 2) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root2Prefix23
  have heq : matrixHom (rootGenerator 2) = g := by
    apply Units.ext
    exact (rootGenerator_val 2).trans hv.symm
  rw [heq]
  exact hg

private def root3Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(false, ![175, 95, 44, 48, 87, 135, 80, 5]),
(true, ![12, 41, 1, 234, 170, 225, 51, 45]),
(true, ![111, 44, 193, 150, 33, 96, 159, 192]),
(true, ![195, 1, 14, 164, 175, 217, 230, 207]),
(true, ![186, 193, 219, 250, 12, 9, 249, 213]),
(true, ![165, 14, 189, 18, 111, 66, 103, 102]),
(true, ![59, 219, 60, 48, 195, 3, 64, 129])]

private theorem root3Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) :=
  valid_mem (Matrices.identityRows 8) root3Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root3Steps1 : List Step := [(false, ![165, 175, 67, 174, 110, 157, 161, 185]),
(true, ![59, 12, 194, 205, 2, 82, 215, 208]),
(true, ![28, 111, 123, 97, 180, 135, 210, 75]),
(true, ![235, 195, 171, 24, 126, 225, 255, 65]),
(true, ![87, 186, 224, 7, 134, 96, 63, 118]),
(true, ![170, 165, 161, 153, 32, 217, 240, 5]),
(true, ![33, 59, 215, 190, 110, 9, 37, 45]),
(true, ![175, 28, 210, 73, 2, 66, 67, 192]),
(true, ![12, 235, 255, 245, 180, 3, 194, 207]),
(true, ![111, 87, 63, 8, 126, 117, 123, 213])]

private theorem root3Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) :=
  valid_mem (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) root3Steps1 (by decide +kernel) (root3Prefix0)

private def root3Steps2 : List Step := [(true, ![195, 170, 240, 131, 134, 112, 171, 102]),
(false, ![110, 75, 93, 207, 95, 15, 160, 85]),
(true, ![2, 65, 157, 213, 41, 26, 22, 30]),
(true, ![180, 118, 82, 102, 44, 179, 220, 95]),
(true, ![126, 5, 135, 129, 1, 231, 36, 41]),
(true, ![134, 45, 225, 185, 193, 56, 130, 44]),
(true, ![32, 192, 96, 208, 14, 105, 204, 1]),
(true, ![110, 207, 217, 75, 219, 155, 160, 193]),
(true, ![2, 213, 9, 65, 189, 10, 22, 14]),
(true, ![180, 102, 66, 118, 60, 55, 220, 219])]

private theorem root3Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) :=
  valid_mem (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) root3Steps2 (by decide +kernel) (root3Prefix1)

private def root3Steps3 : List Step := [(true, ![126, 129, 3, 5, 133, 115, 36, 189]),
(true, ![134, 185, 117, 45, 85, 40, 130, 60]),
(true, ![32, 208, 112, 192, 30, 237, 204, 133]),
(false, ![249, 164, 15, 243, 204, 12, 30, 194]),
(true, ![103, 250, 26, 80, 160, 111, 95, 123]),
(true, ![64, 18, 179, 51, 22, 195, 41, 171]),
(true, ![183, 48, 231, 159, 220, 186, 44, 224]),
(true, ![11, 234, 56, 230, 36, 165, 1, 161]),
(true, ![246, 150, 105, 249, 130, 59, 193, 215]),
(true, ![125, 164, 155, 103, 204, 28, 14, 210])]

private theorem root3Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) :=
  valid_mem (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) root3Steps3 (by decide +kernel) (root3Prefix2)

private def root3Steps4 : List Step := [(true, ![243, 250, 10, 64, 160, 235, 219, 255]),
(true, ![80, 18, 55, 183, 22, 87, 189, 63]),
(true, ![51, 48, 115, 11, 220, 170, 60, 240]),
(false, ![51, 174, 146, 11, 73, 75, 67, 93]),
(true, ![159, 205, 72, 246, 245, 65, 194, 157]),
(false, ![117, 245, 55, 80, 205, 74, 133, 3]),
(true, ![112, 8, 115, 51, 97, 128, 85, 117]),
(true, ![93, 131, 40, 159, 24, 120, 30, 112]),
(true, ![157, 13, 237, 230, 7, 222, 95, 93]),
(true, ![82, 174, 15, 249, 153, 144, 41, 157])]

private theorem root3Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) :=
  valid_mem (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) root3Steps4 (by decide +kernel) (root3Prefix3)

private def root3Steps5 : List Step := [(true, ![135, 205, 26, 103, 190, 252, 44, 82]),
(true, ![225, 97, 179, 64, 73, 74, 1, 135]),
(true, ![96, 24, 231, 183, 245, 128, 193, 225]),
(true, ![217, 7, 56, 11, 8, 120, 14, 96]),
(false, ![217, 230, 56, 11, 150, 153, 155, 88]),
(true, ![9, 249, 105, 246, 164, 190, 10, 176]),
(false, ![125, 32, 37, 80, 208, 103, 224, 252]),
(true, ![243, 110, 67, 51, 75, 64, 161, 74]),
(true, ![80, 2, 194, 159, 65, 183, 215, 128]),
(false, ![246, 118, 133, 117, 74, 26, 66, 82])]

private theorem root3Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![246, 118, 133, 117, 74, 26, 66, 82] : Rows) :=
  valid_mem (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) root3Steps5 (by decide +kernel) (root3Prefix4)

private def root3Steps6 : List Step := [(true, ![125, 5, 85, 112, 128, 179, 3, 135]),
(false, ![9, 144, 102, 15, 82, 97, 157, 180]),
(true, ![66, 252, 129, 26, 135, 24, 82, 126]),
(false, ![215, 176, 185, 183, 180, 193, 128, 148]),
(true, ![210, 146, 208, 11, 126, 14, 120, 16]),
(true, ![255, 72, 75, 246, 134, 219, 222, 132]),
(true, ![63, 52, 65, 125, 32, 189, 144, 148]),
(true, ![240, 6, 118, 243, 110, 60, 252, 16]),
(true, ![37, 88, 5, 80, 2, 133, 74, 132]),
(true, ![67, 176, 45, 51, 180, 85, 128, 148])]

private theorem root3Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![67, 176, 45, 51, 180, 85, 128, 148] : Rows) :=
  valid_mem (![246, 118, 133, 117, 74, 26, 66, 82] : Rows) root3Steps6 (by decide +kernel) (root3Prefix5)

private def root3Steps7 : List Step := [(true, ![194, 146, 192, 159, 126, 30, 120, 16]),
(true, ![123, 72, 207, 230, 134, 95, 222, 132]),
(true, ![171, 52, 213, 249, 32, 41, 144, 148]),
(true, ![224, 6, 102, 103, 110, 44, 252, 16]),
(false, ![10, 13, 85, 190, 195, 20, 176, 87]),
(true, ![55, 174, 30, 73, 186, 104, 146, 170]),
(true, ![115, 205, 95, 245, 165, 90, 72, 33]),
(true, ![40, 97, 41, 8, 59, 4, 52, 175]),
(true, ![237, 24, 44, 131, 28, 236, 6, 12]),
(true, ![15, 7, 1, 13, 235, 206, 88, 111])]

private theorem root3Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![15, 7, 1, 13, 235, 206, 88, 111] : Rows) :=
  valid_mem (![67, 176, 45, 51, 180, 85, 128, 148] : Rows) root3Steps7 (by decide +kernel) (root3Prefix6)

private def root3Steps8 : List Step := [(true, ![26, 153, 193, 174, 87, 20, 176, 195]),
(false, ![183, 120, 24, 48, 16, 44, 252, 110]),
(true, ![11, 222, 7, 234, 132, 1, 74, 2]),
(true, ![246, 144, 153, 150, 148, 193, 128, 180]),
(false, ![80, 5, 120, 8, 126, 24, 82, 135]),
(true, ![51, 45, 222, 131, 134, 7, 135, 225]),
(true, ![159, 192, 144, 13, 32, 153, 225, 96]),
(true, ![230, 207, 252, 174, 110, 190, 96, 217]),
(true, ![249, 213, 74, 205, 2, 73, 217, 9]),
(true, ![103, 102, 128, 97, 180, 245, 9, 66])]

private theorem root3Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![103, 102, 128, 97, 180, 245, 9, 66] : Rows) :=
  valid_mem (![15, 7, 1, 13, 235, 206, 88, 111] : Rows) root3Steps8 (by decide +kernel) (root3Prefix7)

private def root3Steps9 : List Step := [(true, ![64, 129, 120, 24, 126, 8, 66, 3]),
(true, ![183, 185, 222, 7, 134, 131, 3, 117]),
(true, ![11, 208, 144, 153, 32, 13, 117, 112]),
(true, ![246, 75, 252, 190, 110, 174, 112, 93]),
(false, ![80, 170, 176, 103, 195, 48, 15, 240]),
(true, ![51, 33, 146, 64, 186, 234, 26, 37]),
(true, ![159, 175, 72, 183, 165, 150, 179, 67]),
(true, ![230, 12, 52, 11, 59, 164, 231, 194]),
(true, ![249, 111, 6, 246, 28, 250, 56, 123]),
(true, ![103, 195, 88, 125, 235, 18, 105, 171])]

private theorem root3Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![103, 195, 88, 125, 235, 18, 105, 171] : Rows) :=
  valid_mem (![103, 102, 128, 97, 180, 245, 9, 66] : Rows) root3Steps9 (by decide +kernel) (root3Prefix8)

private def root3Steps10 : List Step := [(true, ![64, 186, 176, 243, 87, 48, 155, 224]),
(true, ![183, 165, 146, 80, 170, 234, 10, 161]),
(true, ![11, 59, 72, 51, 33, 150, 55, 215]),
(true, ![246, 28, 52, 159, 175, 164, 115, 210]),
(false, ![80, 186, 213, 117, 219, 208, 146, 210]),
(true, ![51, 165, 102, 112, 189, 75, 72, 255]),
(false, ![51, 59, 85, 15, 250, 170, 55, 45]),
(true, ![159, 28, 30, 26, 18, 33, 115, 192]),
(true, ![230, 235, 95, 179, 48, 175, 40, 207]),
(true, ![249, 87, 41, 231, 234, 12, 237, 213])]

private theorem root3Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![249, 87, 41, 231, 234, 12, 237, 213] : Rows) :=
  valid_mem (![103, 195, 88, 125, 235, 18, 105, 171] : Rows) root3Steps10 (by decide +kernel) (root3Prefix9)

private def root3Steps11 : List Step := [(true, ![103, 170, 44, 56, 150, 111, 15, 102]),
(true, ![64, 33, 1, 105, 164, 195, 26, 129]),
(true, ![183, 175, 193, 155, 250, 186, 179, 185]),
(true, ![11, 12, 14, 10, 18, 165, 231, 208]),
(true, ![246, 111, 219, 55, 48, 59, 56, 75]),
(false, ![80, 40, 175, 72, 174, 165, 56, 170]),
(true, ![51, 237, 12, 52, 205, 59, 105, 33]),
(false, ![51, 12, 237, 213, 245, 165, 37, 18]),
(true, ![159, 111, 15, 102, 8, 59, 67, 48]),
(true, ![230, 195, 26, 129, 131, 28, 194, 234])]

private theorem root3Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![230, 195, 26, 129, 131, 28, 194, 234] : Rows) :=
  valid_mem (![249, 87, 41, 231, 234, 12, 237, 213] : Rows) root3Steps11 (by decide +kernel) (root3Prefix10)

private def root3Steps12 : List Step := [(true, ![249, 186, 179, 185, 13, 235, 123, 150]),
(false, ![32, 28, 97, 129, 6, 1, 4, 8]),
(true, ![110, 235, 24, 185, 88, 193, 236, 131]),
(false, ![195, 1, 193, 129, 96, 24, 231, 207]),
(true, ![186, 193, 14, 185, 217, 7, 56, 213]),
(true, ![165, 14, 219, 208, 9, 153, 105, 102]),
(true, ![59, 219, 189, 75, 66, 190, 155, 129]),
(true, ![28, 189, 60, 65, 3, 73, 10, 185]),
(true, ![235, 60, 133, 118, 117, 245, 55, 208]),
(true, ![87, 133, 85, 5, 112, 8, 115, 75])]

private theorem root3Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![87, 133, 85, 5, 112, 8, 115, 75] : Rows) :=
  valid_mem (![230, 195, 26, 129, 131, 28, 194, 234] : Rows) root3Steps12 (by decide +kernel) (root3Prefix11)

private def root3Steps13 : List Step := [(true, ![170, 85, 30, 45, 93, 131, 40, 65]),
(true, ![33, 30, 95, 192, 157, 13, 237, 118]),
(true, ![175, 95, 41, 207, 82, 174, 15, 5]),
(true, ![12, 41, 44, 213, 135, 205, 26, 45]),
(false, ![237, 132, 20, 52, 180, 245, 183, 255]),
(true, ![15, 148, 104, 6, 126, 8, 11, 63]),
(false, ![112, 126, 206, 13, 148, 150, 11, 222]),
(true, ![93, 134, 20, 174, 16, 164, 246, 144]),
(true, ![157, 32, 104, 205, 132, 250, 125, 252]),
(true, ![82, 110, 90, 97, 148, 18, 243, 74])]

private theorem root3Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 110, 90, 97, 148, 18, 243, 74] : Rows) :=
  valid_mem (![87, 133, 85, 5, 112, 8, 115, 75] : Rows) root3Steps13 (by decide +kernel) (root3Prefix12)

private def root3Steps14 : List Step := [(true, ![135, 2, 4, 24, 16, 48, 80, 128]),
(true, ![225, 180, 236, 7, 132, 234, 51, 120]),
(true, ![96, 126, 206, 153, 148, 150, 159, 222]),
(true, ![217, 134, 20, 190, 16, 164, 230, 144]),
(true, ![9, 32, 104, 73, 132, 250, 249, 252]),
(true, ![66, 110, 90, 245, 148, 18, 103, 74]),
(true, ![3, 2, 4, 8, 16, 48, 64, 128])]

private theorem root3Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![3, 2, 4, 8, 16, 48, 64, 128] : Rows) :=
  valid_mem (![82, 110, 90, 97, 148, 18, 243, 74] : Rows) root3Steps14 (by decide +kernel) (root3Prefix13)

theorem root3_mem : matrixHom (rootGenerator 3) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root3Prefix14
  have heq : matrixHom (rootGenerator 3) = g := by
    apply Units.ext
    exact (rootGenerator_val 3).trans hv.symm
  rw [heq]
  exact hg

private def root4Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(false, ![175, 95, 44, 48, 87, 135, 80, 5]),
(true, ![12, 41, 1, 234, 170, 225, 51, 45]),
(true, ![111, 44, 193, 150, 33, 96, 159, 192]),
(true, ![195, 1, 14, 164, 175, 217, 230, 207]),
(true, ![186, 193, 219, 250, 12, 9, 249, 213]),
(true, ![165, 14, 189, 18, 111, 66, 103, 102]),
(true, ![59, 219, 60, 48, 195, 3, 64, 129])]

private theorem root4Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) :=
  valid_mem (Matrices.identityRows 8) root4Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root4Steps1 : List Step := [(false, ![165, 175, 67, 174, 110, 157, 161, 185]),
(true, ![59, 12, 194, 205, 2, 82, 215, 208]),
(true, ![28, 111, 123, 97, 180, 135, 210, 75]),
(true, ![235, 195, 171, 24, 126, 225, 255, 65]),
(true, ![87, 186, 224, 7, 134, 96, 63, 118]),
(true, ![170, 165, 161, 153, 32, 217, 240, 5]),
(true, ![33, 59, 215, 190, 110, 9, 37, 45]),
(true, ![175, 28, 210, 73, 2, 66, 67, 192]),
(true, ![12, 235, 255, 245, 180, 3, 194, 207]),
(true, ![111, 87, 63, 8, 126, 117, 123, 213])]

private theorem root4Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) :=
  valid_mem (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) root4Steps1 (by decide +kernel) (root4Prefix0)

private def root4Steps2 : List Step := [(true, ![195, 170, 240, 131, 134, 112, 171, 102]),
(false, ![110, 75, 93, 207, 95, 15, 160, 85]),
(true, ![2, 65, 157, 213, 41, 26, 22, 30]),
(true, ![180, 118, 82, 102, 44, 179, 220, 95]),
(true, ![126, 5, 135, 129, 1, 231, 36, 41]),
(true, ![134, 45, 225, 185, 193, 56, 130, 44]),
(true, ![32, 192, 96, 208, 14, 105, 204, 1]),
(true, ![110, 207, 217, 75, 219, 155, 160, 193]),
(true, ![2, 213, 9, 65, 189, 10, 22, 14]),
(true, ![180, 102, 66, 118, 60, 55, 220, 219])]

private theorem root4Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) :=
  valid_mem (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) root4Steps2 (by decide +kernel) (root4Prefix1)

private def root4Steps3 : List Step := [(true, ![126, 129, 3, 5, 133, 115, 36, 189]),
(true, ![134, 185, 117, 45, 85, 40, 130, 60]),
(true, ![32, 208, 112, 192, 30, 237, 204, 133]),
(false, ![249, 164, 15, 243, 204, 12, 30, 194]),
(true, ![103, 250, 26, 80, 160, 111, 95, 123]),
(true, ![64, 18, 179, 51, 22, 195, 41, 171]),
(true, ![183, 48, 231, 159, 220, 186, 44, 224]),
(true, ![11, 234, 56, 230, 36, 165, 1, 161]),
(true, ![246, 150, 105, 249, 130, 59, 193, 215]),
(true, ![125, 164, 155, 103, 204, 28, 14, 210])]

private theorem root4Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) :=
  valid_mem (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) root4Steps3 (by decide +kernel) (root4Prefix2)

private def root4Steps4 : List Step := [(true, ![243, 250, 10, 64, 160, 235, 219, 255]),
(true, ![80, 18, 55, 183, 22, 87, 189, 63]),
(true, ![51, 48, 115, 11, 220, 170, 60, 240]),
(false, ![51, 174, 146, 11, 73, 75, 67, 93]),
(true, ![159, 205, 72, 246, 245, 65, 194, 157]),
(false, ![117, 245, 55, 80, 205, 74, 133, 3]),
(true, ![112, 8, 115, 51, 97, 128, 85, 117]),
(true, ![93, 131, 40, 159, 24, 120, 30, 112]),
(true, ![157, 13, 237, 230, 7, 222, 95, 93]),
(true, ![82, 174, 15, 249, 153, 144, 41, 157])]

private theorem root4Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) :=
  valid_mem (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) root4Steps4 (by decide +kernel) (root4Prefix3)

private def root4Steps5 : List Step := [(true, ![135, 205, 26, 103, 190, 252, 44, 82]),
(true, ![225, 97, 179, 64, 73, 74, 1, 135]),
(true, ![96, 24, 231, 183, 245, 128, 193, 225]),
(true, ![217, 7, 56, 11, 8, 120, 14, 96]),
(false, ![217, 230, 56, 11, 150, 153, 155, 88]),
(true, ![9, 249, 105, 246, 164, 190, 10, 176]),
(false, ![125, 32, 37, 80, 208, 103, 224, 252]),
(true, ![243, 110, 67, 51, 75, 64, 161, 74]),
(false, ![192, 195, 60, 51, 170, 161, 64, 65]),
(true, ![207, 186, 133, 159, 33, 215, 183, 118])]

private theorem root4Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) :=
  valid_mem (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) root4Steps5 (by decide +kernel) (root4Prefix4)

private def root4Steps6 : List Step := [(false, ![131, 28, 194, 117, 18, 66, 26, 2]),
(true, ![13, 235, 123, 112, 48, 3, 179, 180]),
(true, ![174, 87, 171, 93, 234, 117, 231, 126]),
(true, ![205, 170, 224, 157, 150, 112, 56, 134]),
(true, ![97, 33, 161, 82, 164, 93, 105, 32]),
(true, ![24, 175, 215, 135, 250, 157, 155, 110]),
(true, ![7, 12, 210, 225, 18, 82, 10, 2]),
(true, ![153, 111, 255, 96, 48, 135, 55, 180]),
(true, ![190, 195, 63, 217, 234, 225, 115, 126]),
(true, ![73, 186, 240, 9, 150, 96, 40, 134])]

private theorem root4Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![73, 186, 240, 9, 150, 96, 40, 134] : Rows) :=
  valid_mem (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) root4Steps6 (by decide +kernel) (root4Prefix5)

private def root4Steps7 : List Step := [(true, ![245, 165, 37, 66, 164, 217, 237, 32]),
(false, ![205, 59, 105, 215, 208, 217, 12, 249]),
(true, ![97, 28, 155, 210, 75, 9, 111, 103]),
(false, ![179, 186, 14, 210, 170, 125, 40, 190]),
(true, ![231, 165, 219, 255, 33, 243, 237, 73]),
(true, ![56, 59, 189, 63, 175, 80, 15, 245]),
(true, ![105, 28, 60, 240, 12, 51, 26, 8]),
(false, ![37, 186, 67, 93, 237, 51, 183, 150]),
(true, ![67, 165, 194, 157, 15, 159, 11, 164]),
(true, ![194, 59, 123, 82, 26, 230, 246, 250])]

private theorem root4Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![194, 59, 123, 82, 26, 230, 246, 250] : Rows) :=
  valid_mem (![73, 186, 240, 9, 150, 96, 40, 134] : Rows) root4Steps7 (by decide +kernel) (root4Prefix6)

private def root4Steps8 : List Step := [(true, ![123, 28, 171, 135, 179, 249, 125, 18]),
(true, ![171, 235, 224, 225, 231, 103, 243, 48]),
(true, ![224, 87, 161, 96, 56, 64, 80, 234]),
(true, ![161, 170, 215, 217, 105, 183, 51, 150]),
(true, ![215, 33, 210, 9, 155, 11, 159, 164]),
(true, ![210, 175, 255, 66, 10, 246, 230, 250]),
(false, ![210, 219, 45, 215, 224, 80, 7, 189]),
(true, ![255, 189, 192, 210, 161, 51, 153, 60]),
(true, ![63, 60, 207, 255, 215, 159, 190, 133]),
(true, ![240, 133, 213, 63, 210, 230, 73, 85])]

private theorem root4Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![240, 133, 213, 63, 210, 230, 73, 85] : Rows) :=
  valid_mem (![194, 59, 123, 82, 26, 230, 246, 250] : Rows) root4Steps8 (by decide +kernel) (root4Prefix7)

private def root4Steps9 : List Step := [(true, ![37, 85, 102, 240, 255, 249, 245, 30]),
(true, ![67, 30, 129, 37, 63, 103, 8, 95]),
(true, ![194, 95, 185, 67, 240, 64, 131, 41]),
(true, ![123, 41, 208, 194, 37, 183, 13, 44]),
(true, ![171, 44, 75, 123, 67, 11, 174, 1]),
(true, ![224, 1, 65, 171, 194, 246, 205, 193]),
(true, ![161, 193, 118, 224, 123, 125, 97, 14]),
(false, ![64, 24, 2, 10, 4, 9, 179, 155]),
(true, ![183, 7, 180, 55, 236, 66, 231, 10]),
(true, ![11, 153, 126, 115, 206, 3, 56, 55])]

private theorem root4Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![11, 153, 126, 115, 206, 3, 56, 55] : Rows) :=
  valid_mem (![240, 133, 213, 63, 210, 230, 73, 85] : Rows) root4Steps9 (by decide +kernel) (root4Prefix8)

private def root4Steps10 : List Step := [(true, ![246, 190, 134, 40, 20, 117, 105, 115]),
(false, ![80, 103, 95, 111, 44, 159, 37, 146]),
(true, ![51, 64, 41, 195, 1, 230, 67, 72]),
(true, ![159, 183, 44, 186, 193, 249, 194, 52]),
(true, ![230, 11, 1, 165, 14, 103, 123, 6]),
(true, ![249, 246, 193, 59, 219, 64, 171, 88]),
(true, ![103, 125, 14, 28, 189, 183, 224, 176]),
(true, ![64, 243, 219, 235, 60, 11, 161, 146]),
(true, ![183, 80, 189, 87, 133, 246, 215, 72]),
(true, ![11, 51, 60, 170, 85, 125, 210, 52])]

private theorem root4Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![11, 51, 60, 170, 85, 125, 210, 52] : Rows) :=
  valid_mem (![11, 153, 126, 115, 206, 3, 56, 55] : Rows) root4Steps10 (by decide +kernel) (root4Prefix9)

private def root4Steps11 : List Step := [(true, ![246, 159, 133, 33, 30, 243, 255, 6]),
(true, ![125, 230, 85, 175, 95, 80, 63, 88]),
(true, ![243, 249, 30, 12, 41, 51, 240, 176]),
(false, ![192, 32, 204, 237, 132, 51, 93, 252]),
(true, ![207, 110, 160, 15, 148, 159, 157, 74]),
(true, ![213, 2, 22, 26, 16, 230, 82, 128]),
(false, ![52, 118, 90, 183, 87, 7, 128, 82]),
(true, ![6, 5, 4, 11, 170, 153, 120, 135]),
(true, ![88, 45, 236, 246, 33, 190, 222, 225]),
(true, ![176, 192, 206, 125, 175, 73, 144, 96])]

private theorem root4Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![176, 192, 206, 125, 175, 73, 144, 96] : Rows) :=
  valid_mem (![11, 51, 60, 170, 85, 125, 210, 52] : Rows) root4Steps11 (by decide +kernel) (root4Prefix10)

private def root4Steps12 : List Step := [(true, ![146, 207, 20, 243, 12, 245, 252, 217]),
(true, ![72, 213, 104, 80, 111, 8, 74, 9]),
(true, ![52, 102, 90, 51, 195, 131, 128, 66]),
(true, ![6, 129, 4, 159, 186, 13, 120, 3]),
(true, ![88, 185, 236, 230, 165, 174, 222, 117]),
(true, ![176, 208, 206, 249, 59, 205, 144, 112]),
(true, ![146, 75, 20, 103, 28, 97, 252, 93]),
(true, ![72, 65, 104, 64, 235, 24, 74, 157]),
(false, ![55, 74, 206, 161, 1, 193, 65, 3]),
(true, ![115, 128, 20, 215, 193, 14, 118, 117])]

private theorem root4Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![115, 128, 20, 215, 193, 14, 118, 117] : Rows) :=
  valid_mem (![176, 192, 206, 125, 175, 73, 144, 96] : Rows) root4Steps12 (by decide +kernel) (root4Prefix11)

private def root4Steps13 : List Step := [(true, ![40, 120, 104, 210, 14, 219, 5, 112]),
(true, ![237, 222, 90, 255, 219, 189, 45, 93]),
(true, ![15, 144, 4, 63, 189, 60, 192, 157]),
(true, ![26, 252, 236, 240, 60, 133, 207, 82]),
(true, ![179, 74, 206, 37, 133, 85, 213, 135]),
(true, ![231, 128, 20, 67, 85, 30, 102, 225]),
(true, ![56, 120, 104, 194, 30, 95, 129, 96]),
(true, ![105, 222, 90, 123, 95, 41, 185, 217]),
(true, ![155, 144, 4, 171, 41, 44, 208, 9]),
(false, ![14, 5, 123, 160, 132, 20, 164, 125])]

private theorem root4Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![14, 5, 123, 160, 132, 20, 164, 125] : Rows) :=
  valid_mem (![115, 128, 20, 215, 193, 14, 118, 117] : Rows) root4Steps13 (by decide +kernel) (root4Prefix12)

private def root4Steps14 : List Step := [(true, ![219, 45, 171, 22, 148, 104, 250, 243]),
(true, ![189, 192, 224, 220, 16, 90, 18, 80]),
(false, ![250, 243, 10, 73, 87, 22, 33, 246]),
(true, ![18, 80, 55, 245, 170, 220, 175, 125]),
(false, ![33, 246, 72, 205, 75, 73, 219, 9]),
(true, ![175, 125, 52, 97, 65, 245, 189, 66]),
(true, ![12, 243, 6, 24, 118, 8, 60, 3]),
(true, ![111, 80, 88, 7, 5, 131, 133, 117]),
(true, ![195, 51, 176, 153, 45, 13, 85, 112]),
(true, ![186, 159, 146, 190, 192, 174, 30, 93])]

private theorem root4Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![186, 159, 146, 190, 192, 174, 30, 93] : Rows) :=
  valid_mem (![14, 5, 123, 160, 132, 20, 164, 125] : Rows) root4Steps14 (by decide +kernel) (root4Prefix13)

private def root4Steps15 : List Step := [(true, ![165, 230, 72, 73, 207, 205, 95, 157]),
(true, ![59, 249, 52, 245, 213, 97, 41, 82]),
(true, ![28, 103, 6, 8, 102, 24, 44, 135]),
(true, ![235, 64, 88, 131, 129, 7, 1, 225]),
(true, ![87, 183, 176, 13, 185, 153, 193, 96]),
(true, ![170, 11, 146, 174, 208, 190, 14, 217]),
(false, ![75, 11, 115, 48, 164, 103, 155, 217]),
(true, ![65, 246, 40, 234, 250, 64, 10, 9]),
(true, ![118, 125, 237, 150, 18, 183, 55, 66]),
(true, ![5, 243, 15, 164, 48, 11, 115, 3])]

private theorem root4Prefix15 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![5, 243, 15, 164, 48, 11, 115, 3] : Rows) :=
  valid_mem (![186, 159, 146, 190, 192, 174, 30, 93] : Rows) root4Steps15 (by decide +kernel) (root4Prefix14)

private def root4Steps16 : List Step := [(true, ![45, 80, 26, 250, 234, 246, 40, 117]),
(true, ![192, 51, 179, 18, 150, 125, 237, 112]),
(true, ![207, 159, 231, 48, 164, 243, 15, 93]),
(true, ![213, 230, 56, 234, 250, 80, 26, 157]),
(true, ![102, 249, 105, 150, 18, 51, 179, 82]),
(false, ![85, 32, 37, 8, 33, 51, 97, 128]),
(true, ![30, 110, 67, 131, 175, 159, 24, 120]),
(false, ![204, 195, 60, 207, 219, 117, 193, 153]),
(true, ![160, 186, 133, 213, 189, 112, 14, 190]),
(true, ![22, 165, 85, 102, 60, 93, 219, 73])]

private theorem root4Prefix16 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![22, 165, 85, 102, 60, 93, 219, 73] : Rows) :=
  valid_mem (![5, 243, 15, 164, 48, 11, 115, 3] : Rows) root4Steps16 (by decide +kernel) (root4Prefix15)

private def root4Steps17 : List Step := [(true, ![220, 59, 30, 129, 133, 157, 189, 245]),
(true, ![36, 28, 95, 185, 85, 82, 60, 8]),
(true, ![130, 235, 41, 208, 30, 135, 133, 131]),
(true, ![204, 87, 44, 75, 95, 225, 85, 13]),
(false, ![30, 16, 20, 170, 134, 225, 102, 6]),
(true, ![95, 132, 104, 33, 32, 96, 129, 88]),
(true, ![41, 148, 90, 175, 110, 217, 185, 176]),
(true, ![44, 16, 4, 12, 2, 9, 208, 146]),
(false, ![20, 87, 123, 237, 118, 125, 164, 115]),
(true, ![104, 170, 171, 15, 5, 243, 250, 40])]

private theorem root4Prefix17 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![104, 170, 171, 15, 5, 243, 250, 40] : Rows) :=
  valid_mem (![22, 165, 85, 102, 60, 93, 219, 73] : Rows) root4Steps17 (by decide +kernel) (root4Prefix16)

private def root4Steps18 : List Step := [(true, ![90, 33, 224, 26, 45, 80, 18, 237]),
(true, ![4, 175, 161, 179, 192, 51, 48, 15]),
(true, ![236, 12, 215, 231, 207, 159, 234, 26]),
(false, ![231, 237, 66, 236, 131, 117, 234, 183]),
(true, ![56, 15, 3, 206, 13, 112, 150, 11]),
(true, ![105, 26, 117, 20, 174, 93, 164, 246]),
(true, ![155, 179, 112, 104, 205, 157, 250, 125]),
(true, ![10, 231, 93, 90, 97, 82, 18, 243]),
(true, ![55, 56, 157, 4, 24, 135, 48, 80]),
(true, ![115, 105, 82, 236, 7, 225, 234, 51])]

private theorem root4Prefix18 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![115, 105, 82, 236, 7, 225, 234, 51] : Rows) :=
  valid_mem (![104, 170, 171, 15, 5, 243, 250, 40] : Rows) root4Steps18 (by decide +kernel) (root4Prefix17)

private def root4Steps19 : List Step := [(true, ![40, 155, 135, 206, 153, 96, 150, 159]),
(true, ![237, 10, 225, 20, 190, 217, 164, 230]),
(true, ![15, 55, 96, 104, 73, 9, 250, 249]),
(true, ![26, 115, 217, 90, 245, 66, 18, 103]),
(true, ![179, 40, 9, 4, 8, 3, 48, 64]),
(false, ![97, 111, 125, 123, 150, 157, 174, 161]),
(true, ![24, 195, 243, 171, 164, 82, 205, 215]),
(true, ![7, 186, 80, 224, 250, 135, 97, 210]),
(true, ![153, 165, 51, 161, 18, 225, 24, 255]),
(false, ![120, 59, 51, 64, 33, 225, 193, 45])]

private theorem root4Prefix19 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![120, 59, 51, 64, 33, 225, 193, 45] : Rows) :=
  valid_mem (![115, 105, 82, 236, 7, 225, 234, 51] : Rows) root4Steps19 (by decide +kernel) (root4Prefix18)

private def root4Steps20 : List Step := [(true, ![222, 28, 159, 183, 175, 96, 14, 192]),
(true, ![144, 235, 230, 11, 12, 217, 219, 207]),
(false, ![5, 1, 7, 11, 237, 217, 175, 131]),
(true, ![45, 193, 153, 246, 15, 9, 12, 13]),
(false, ![255, 24, 120, 80, 112, 125, 237, 6]),
(true, ![63, 7, 222, 51, 93, 243, 15, 88]),
(true, ![240, 153, 144, 159, 157, 80, 26, 176]),
(true, ![37, 190, 252, 230, 82, 51, 179, 146]),
(false, ![105, 103, 176, 7, 128, 51, 97, 115]),
(true, ![155, 64, 146, 153, 120, 159, 24, 40])]

private theorem root4Prefix20 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![155, 64, 146, 153, 120, 159, 24, 40] : Rows) :=
  valid_mem (![120, 59, 51, 64, 33, 225, 193, 45] : Rows) root4Steps20 (by decide +kernel) (root4Prefix19)

private def root4Steps21 : List Step := [(true, ![10, 183, 72, 190, 222, 230, 7, 237]),
(true, ![55, 11, 52, 73, 144, 249, 153, 15]),
(false, ![72, 11, 213, 220, 5, 32, 120, 112]),
(true, ![52, 246, 102, 36, 45, 110, 222, 93]),
(true, ![6, 125, 129, 130, 192, 2, 144, 157]),
(true, ![88, 243, 185, 204, 207, 180, 252, 82]),
(false, ![96, 192, 129, 30, 131, 135, 176, 128]),
(true, ![217, 207, 185, 95, 13, 225, 146, 120]),
(true, ![9, 213, 208, 41, 174, 96, 72, 222]),
(true, ![66, 102, 75, 44, 205, 217, 52, 144])]

private theorem root4Prefix21 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![66, 102, 75, 44, 205, 217, 52, 144] : Rows) :=
  valid_mem (![155, 64, 146, 153, 120, 159, 24, 40] : Rows) root4Steps21 (by decide +kernel) (root4Prefix20)

private def root4Steps22 : List Step := [(true, ![3, 129, 65, 1, 97, 9, 6, 252]),
(true, ![117, 185, 118, 193, 24, 66, 88, 74]),
(true, ![112, 208, 5, 14, 7, 3, 176, 128]),
(true, ![93, 75, 45, 219, 153, 117, 146, 120]),
(true, ![157, 65, 192, 189, 190, 112, 72, 222]),
(true, ![82, 118, 207, 60, 73, 93, 52, 144]),
(true, ![135, 5, 213, 133, 245, 157, 6, 252]),
(true, ![225, 45, 102, 85, 8, 82, 88, 74]),
(false, ![225, 255, 85, 102, 150, 128, 96, 65]),
(true, ![96, 63, 30, 129, 164, 120, 217, 118])]

private theorem root4Prefix22 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![96, 63, 30, 129, 164, 120, 217, 118] : Rows) :=
  valid_mem (![66, 102, 75, 44, 205, 217, 52, 144] : Rows) root4Steps22 (by decide +kernel) (root4Prefix21)

private def root4Steps23 : List Step := [(false, ![88, 222, 204, 185, 208, 153, 217, 2]),
(true, ![176, 144, 160, 208, 75, 190, 9, 180]),
(false, ![252, 5, 171, 164, 170, 103, 125, 135]),
(true, ![74, 45, 224, 250, 33, 64, 243, 225]),
(true, ![128, 192, 161, 18, 175, 183, 80, 96]),
(true, ![120, 207, 215, 48, 12, 11, 51, 217]),
(true, ![222, 213, 210, 234, 111, 246, 159, 9]),
(true, ![144, 102, 255, 150, 195, 125, 230, 66]),
(true, ![252, 129, 63, 164, 186, 243, 249, 3]),
(true, ![74, 185, 240, 250, 165, 80, 103, 117])]

private theorem root4Prefix23 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![74, 185, 240, 250, 165, 80, 103, 117] : Rows) :=
  valid_mem (![96, 63, 30, 129, 164, 120, 217, 118] : Rows) root4Steps23 (by decide +kernel) (root4Prefix22)

private def root4Steps24 : List Step := [(true, ![128, 208, 37, 18, 59, 51, 64, 112]),
(true, ![120, 75, 67, 48, 28, 159, 183, 93]),
(true, ![222, 65, 194, 234, 235, 230, 11, 157]),
(true, ![144, 118, 123, 150, 87, 249, 246, 82]),
(false, ![5, 2, 4, 8, 16, 32, 80, 128])]

private theorem root4Prefix24 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![5, 2, 4, 8, 16, 32, 80, 128] : Rows) :=
  valid_mem (![74, 185, 240, 250, 165, 80, 103, 117] : Rows) root4Steps24 (by decide +kernel) (root4Prefix23)

theorem root4_mem : matrixHom (rootGenerator 4) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root4Prefix24
  have heq : matrixHom (rootGenerator 4) = g := by
    apply Units.ext
    exact (rootGenerator_val 4).trans hv.symm
  rw [heq]
  exact hg

private def root5Steps0 : List Step := [(true, ![193, 180, 236, 131, 132, 110, 183, 120]),
(true, ![14, 126, 206, 13, 148, 2, 11, 222]),
(true, ![219, 134, 20, 174, 16, 180, 246, 144]),
(false, ![175, 95, 44, 48, 87, 135, 80, 5]),
(true, ![12, 41, 1, 234, 170, 225, 51, 45]),
(true, ![111, 44, 193, 150, 33, 96, 159, 192]),
(true, ![195, 1, 14, 164, 175, 217, 230, 207]),
(true, ![186, 193, 219, 250, 12, 9, 249, 213]),
(true, ![165, 14, 189, 18, 111, 66, 103, 102]),
(true, ![59, 219, 60, 48, 195, 3, 64, 129])]

private theorem root5Prefix0 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) :=
  valid_mem (Matrices.identityRows 8) root5Steps0 (by decide +kernel) (⟨1, smallGenerated.one_mem, (Matrices.decode_identity 8).symm⟩)

private def root5Steps1 : List Step := [(false, ![165, 175, 67, 174, 110, 157, 161, 185]),
(true, ![59, 12, 194, 205, 2, 82, 215, 208]),
(true, ![28, 111, 123, 97, 180, 135, 210, 75]),
(true, ![235, 195, 171, 24, 126, 225, 255, 65]),
(true, ![87, 186, 224, 7, 134, 96, 63, 118]),
(true, ![170, 165, 161, 153, 32, 217, 240, 5]),
(true, ![33, 59, 215, 190, 110, 9, 37, 45]),
(true, ![175, 28, 210, 73, 2, 66, 67, 192]),
(true, ![12, 235, 255, 245, 180, 3, 194, 207]),
(true, ![111, 87, 63, 8, 126, 117, 123, 213])]

private theorem root5Prefix1 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) :=
  valid_mem (![59, 219, 60, 48, 195, 3, 64, 129] : Rows) root5Steps1 (by decide +kernel) (root5Prefix0)

private def root5Steps2 : List Step := [(true, ![195, 170, 240, 131, 134, 112, 171, 102]),
(false, ![110, 75, 93, 207, 95, 15, 160, 85]),
(true, ![2, 65, 157, 213, 41, 26, 22, 30]),
(true, ![180, 118, 82, 102, 44, 179, 220, 95]),
(true, ![126, 5, 135, 129, 1, 231, 36, 41]),
(true, ![134, 45, 225, 185, 193, 56, 130, 44]),
(true, ![32, 192, 96, 208, 14, 105, 204, 1]),
(true, ![110, 207, 217, 75, 219, 155, 160, 193]),
(true, ![2, 213, 9, 65, 189, 10, 22, 14]),
(true, ![180, 102, 66, 118, 60, 55, 220, 219])]

private theorem root5Prefix2 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) :=
  valid_mem (![111, 87, 63, 8, 126, 117, 123, 213] : Rows) root5Steps2 (by decide +kernel) (root5Prefix1)

private def root5Steps3 : List Step := [(true, ![126, 129, 3, 5, 133, 115, 36, 189]),
(true, ![134, 185, 117, 45, 85, 40, 130, 60]),
(true, ![32, 208, 112, 192, 30, 237, 204, 133]),
(false, ![249, 164, 15, 243, 204, 12, 30, 194]),
(true, ![103, 250, 26, 80, 160, 111, 95, 123]),
(true, ![64, 18, 179, 51, 22, 195, 41, 171]),
(true, ![183, 48, 231, 159, 220, 186, 44, 224]),
(true, ![11, 234, 56, 230, 36, 165, 1, 161]),
(true, ![246, 150, 105, 249, 130, 59, 193, 215]),
(true, ![125, 164, 155, 103, 204, 28, 14, 210])]

private theorem root5Prefix3 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) :=
  valid_mem (![180, 102, 66, 118, 60, 55, 220, 219] : Rows) root5Steps3 (by decide +kernel) (root5Prefix2)

private def root5Steps4 : List Step := [(true, ![243, 250, 10, 64, 160, 235, 219, 255]),
(true, ![80, 18, 55, 183, 22, 87, 189, 63]),
(true, ![51, 48, 115, 11, 220, 170, 60, 240]),
(false, ![51, 174, 146, 11, 73, 75, 67, 93]),
(true, ![159, 205, 72, 246, 245, 65, 194, 157]),
(false, ![117, 245, 55, 80, 205, 74, 133, 3]),
(true, ![112, 8, 115, 51, 97, 128, 85, 117]),
(true, ![93, 131, 40, 159, 24, 120, 30, 112]),
(true, ![157, 13, 237, 230, 7, 222, 95, 93]),
(true, ![82, 174, 15, 249, 153, 144, 41, 157])]

private theorem root5Prefix4 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) :=
  valid_mem (![125, 164, 155, 103, 204, 28, 14, 210] : Rows) root5Steps4 (by decide +kernel) (root5Prefix3)

private def root5Steps5 : List Step := [(true, ![135, 205, 26, 103, 190, 252, 44, 82]),
(true, ![225, 97, 179, 64, 73, 74, 1, 135]),
(true, ![96, 24, 231, 183, 245, 128, 193, 225]),
(true, ![217, 7, 56, 11, 8, 120, 14, 96]),
(false, ![217, 230, 56, 11, 150, 153, 155, 88]),
(true, ![9, 249, 105, 246, 164, 190, 10, 176]),
(false, ![125, 32, 37, 80, 208, 103, 224, 252]),
(true, ![243, 110, 67, 51, 75, 64, 161, 74]),
(false, ![192, 195, 60, 51, 170, 161, 64, 65]),
(true, ![207, 186, 133, 159, 33, 215, 183, 118])]

private theorem root5Prefix5 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) :=
  valid_mem (![82, 174, 15, 249, 153, 144, 41, 157] : Rows) root5Steps5 (by decide +kernel) (root5Prefix4)

private def root5Steps6 : List Step := [(false, ![131, 28, 194, 117, 18, 66, 26, 2]),
(true, ![13, 235, 123, 112, 48, 3, 179, 180]),
(true, ![174, 87, 171, 93, 234, 117, 231, 126]),
(true, ![205, 170, 224, 157, 150, 112, 56, 134]),
(true, ![97, 33, 161, 82, 164, 93, 105, 32]),
(true, ![24, 175, 215, 135, 250, 157, 155, 110]),
(true, ![7, 12, 210, 225, 18, 82, 10, 2]),
(true, ![153, 111, 255, 96, 48, 135, 55, 180]),
(true, ![190, 195, 63, 217, 234, 225, 115, 126]),
(true, ![73, 186, 240, 9, 150, 96, 40, 134])]

private theorem root5Prefix6 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![73, 186, 240, 9, 150, 96, 40, 134] : Rows) :=
  valid_mem (![207, 186, 133, 159, 33, 215, 183, 118] : Rows) root5Steps6 (by decide +kernel) (root5Prefix5)

private def root5Steps7 : List Step := [(true, ![245, 165, 37, 66, 164, 217, 237, 32]),
(false, ![205, 59, 105, 215, 208, 217, 12, 249]),
(true, ![97, 28, 155, 210, 75, 9, 111, 103]),
(false, ![179, 186, 14, 210, 170, 125, 40, 190]),
(true, ![231, 165, 219, 255, 33, 243, 237, 73]),
(true, ![56, 59, 189, 63, 175, 80, 15, 245]),
(true, ![105, 28, 60, 240, 12, 51, 26, 8]),
(false, ![37, 186, 67, 93, 237, 51, 183, 150]),
(true, ![67, 165, 194, 157, 15, 159, 11, 164]),
(true, ![194, 59, 123, 82, 26, 230, 246, 250])]

private theorem root5Prefix7 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![194, 59, 123, 82, 26, 230, 246, 250] : Rows) :=
  valid_mem (![73, 186, 240, 9, 150, 96, 40, 134] : Rows) root5Steps7 (by decide +kernel) (root5Prefix6)

private def root5Steps8 : List Step := [(true, ![123, 28, 171, 135, 179, 249, 125, 18]),
(true, ![171, 235, 224, 225, 231, 103, 243, 48]),
(true, ![224, 87, 161, 96, 56, 64, 80, 234]),
(true, ![161, 170, 215, 217, 105, 183, 51, 150]),
(true, ![215, 33, 210, 9, 155, 11, 159, 164]),
(true, ![210, 175, 255, 66, 10, 246, 230, 250]),
(false, ![210, 219, 45, 215, 224, 80, 7, 189]),
(true, ![255, 189, 192, 210, 161, 51, 153, 60]),
(true, ![63, 60, 207, 255, 215, 159, 190, 133]),
(true, ![240, 133, 213, 63, 210, 230, 73, 85])]

private theorem root5Prefix8 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![240, 133, 213, 63, 210, 230, 73, 85] : Rows) :=
  valid_mem (![194, 59, 123, 82, 26, 230, 246, 250] : Rows) root5Steps8 (by decide +kernel) (root5Prefix7)

private def root5Steps9 : List Step := [(true, ![37, 85, 102, 240, 255, 249, 245, 30]),
(true, ![67, 30, 129, 37, 63, 103, 8, 95]),
(true, ![194, 95, 185, 67, 240, 64, 131, 41]),
(true, ![123, 41, 208, 194, 37, 183, 13, 44]),
(true, ![171, 44, 75, 123, 67, 11, 174, 1]),
(true, ![224, 1, 65, 171, 194, 246, 205, 193]),
(true, ![161, 193, 118, 224, 123, 125, 97, 14]),
(false, ![64, 24, 2, 10, 4, 9, 179, 155]),
(true, ![183, 7, 180, 55, 236, 66, 231, 10]),
(true, ![11, 153, 126, 115, 206, 3, 56, 55])]

private theorem root5Prefix9 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![11, 153, 126, 115, 206, 3, 56, 55] : Rows) :=
  valid_mem (![240, 133, 213, 63, 210, 230, 73, 85] : Rows) root5Steps9 (by decide +kernel) (root5Prefix8)

private def root5Steps10 : List Step := [(true, ![246, 190, 134, 40, 20, 117, 105, 115]),
(false, ![80, 103, 95, 111, 44, 159, 37, 146]),
(true, ![51, 64, 41, 195, 1, 230, 67, 72]),
(true, ![159, 183, 44, 186, 193, 249, 194, 52]),
(true, ![230, 11, 1, 165, 14, 103, 123, 6]),
(true, ![249, 246, 193, 59, 219, 64, 171, 88]),
(true, ![103, 125, 14, 28, 189, 183, 224, 176]),
(true, ![64, 243, 219, 235, 60, 11, 161, 146]),
(true, ![183, 80, 189, 87, 133, 246, 215, 72]),
(true, ![11, 51, 60, 170, 85, 125, 210, 52])]

private theorem root5Prefix10 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![11, 51, 60, 170, 85, 125, 210, 52] : Rows) :=
  valid_mem (![11, 153, 126, 115, 206, 3, 56, 55] : Rows) root5Steps10 (by decide +kernel) (root5Prefix9)

private def root5Steps11 : List Step := [(true, ![246, 159, 133, 33, 30, 243, 255, 6]),
(true, ![125, 230, 85, 175, 95, 80, 63, 88]),
(true, ![243, 249, 30, 12, 41, 51, 240, 176]),
(false, ![192, 32, 204, 237, 132, 51, 93, 252]),
(true, ![207, 110, 160, 15, 148, 159, 157, 74]),
(true, ![213, 2, 22, 26, 16, 230, 82, 128]),
(false, ![52, 118, 90, 183, 87, 7, 128, 82]),
(true, ![6, 5, 4, 11, 170, 153, 120, 135]),
(true, ![88, 45, 236, 246, 33, 190, 222, 225]),
(true, ![176, 192, 206, 125, 175, 73, 144, 96])]

private theorem root5Prefix11 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![176, 192, 206, 125, 175, 73, 144, 96] : Rows) :=
  valid_mem (![11, 51, 60, 170, 85, 125, 210, 52] : Rows) root5Steps11 (by decide +kernel) (root5Prefix10)

private def root5Steps12 : List Step := [(true, ![146, 207, 20, 243, 12, 245, 252, 217]),
(true, ![72, 213, 104, 80, 111, 8, 74, 9]),
(true, ![52, 102, 90, 51, 195, 131, 128, 66]),
(true, ![6, 129, 4, 159, 186, 13, 120, 3]),
(true, ![88, 185, 236, 230, 165, 174, 222, 117]),
(true, ![176, 208, 206, 249, 59, 205, 144, 112]),
(true, ![146, 75, 20, 103, 28, 97, 252, 93]),
(true, ![72, 65, 104, 64, 235, 24, 74, 157]),
(false, ![55, 74, 206, 161, 1, 193, 65, 3]),
(true, ![115, 128, 20, 215, 193, 14, 118, 117])]

private theorem root5Prefix12 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![115, 128, 20, 215, 193, 14, 118, 117] : Rows) :=
  valid_mem (![176, 192, 206, 125, 175, 73, 144, 96] : Rows) root5Steps12 (by decide +kernel) (root5Prefix11)

private def root5Steps13 : List Step := [(true, ![40, 120, 104, 210, 14, 219, 5, 112]),
(false, ![111, 153, 206, 210, 155, 175, 144, 15]),
(true, ![195, 190, 20, 255, 10, 12, 252, 26]),
(true, ![186, 73, 104, 63, 55, 111, 74, 179]),
(false, ![28, 220, 206, 222, 72, 40, 65, 97]),
(true, ![235, 36, 20, 144, 52, 237, 118, 24]),
(true, ![87, 130, 104, 252, 6, 15, 5, 7]),
(true, ![170, 204, 90, 74, 88, 26, 45, 153]),
(true, ![33, 160, 4, 128, 176, 179, 192, 190]),
(true, ![175, 22, 236, 120, 146, 231, 207, 73])]

private theorem root5Prefix13 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![175, 22, 236, 120, 146, 231, 207, 73] : Rows) :=
  valid_mem (![115, 128, 20, 215, 193, 14, 118, 117] : Rows) root5Steps13 (by decide +kernel) (root5Prefix12)

private def root5Steps14 : List Step := [(true, ![12, 220, 206, 222, 72, 56, 213, 245]),
(true, ![111, 36, 20, 144, 52, 105, 102, 8]),
(true, ![195, 130, 104, 252, 6, 155, 129, 131]),
(true, ![186, 204, 90, 74, 88, 10, 185, 13]),
(false, ![28, 30, 22, 65, 96, 224, 129, 6]),
(true, ![235, 95, 220, 118, 217, 161, 185, 88]),
(true, ![87, 41, 36, 5, 9, 215, 208, 176]),
(true, ![170, 44, 130, 45, 66, 210, 75, 146]),
(true, ![33, 1, 204, 192, 3, 255, 65, 72]),
(false, ![18, 235, 30, 243, 157, 45, 74, 55])]

private theorem root5Prefix14 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![18, 235, 30, 243, 157, 45, 74, 55] : Rows) :=
  valid_mem (![175, 22, 236, 120, 146, 231, 207, 73] : Rows) root5Steps14 (by decide +kernel) (root5Prefix13)

private def root5Steps15 : List Step := [(true, ![48, 87, 95, 80, 82, 192, 128, 115]),
(false, ![174, 16, 134, 246, 128, 243, 82, 146]),
(true, ![205, 132, 32, 125, 120, 80, 135, 72]),
(true, ![97, 148, 110, 243, 222, 51, 225, 52]),
(true, ![24, 16, 2, 80, 144, 159, 96, 6]),
(true, ![7, 132, 180, 51, 252, 230, 217, 88]),
(true, ![153, 148, 126, 159, 74, 249, 9, 176]),
(true, ![190, 16, 134, 230, 128, 103, 66, 146]),
(true, ![73, 132, 32, 249, 120, 64, 3, 72]),
(true, ![245, 148, 110, 103, 222, 183, 117, 52])]

private theorem root5Prefix15 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![245, 148, 110, 103, 222, 183, 117, 52] : Rows) :=
  valid_mem (![18, 235, 30, 243, 157, 45, 74, 55] : Rows) root5Steps15 (by decide +kernel) (root5Prefix14)

private def root5Steps16 : List Step := [(false, ![205, 126, 195, 190, 63, 26, 159, 213]),
(true, ![97, 134, 186, 73, 240, 179, 230, 102]),
(true, ![24, 32, 165, 245, 37, 231, 249, 129]),
(true, ![7, 110, 59, 8, 67, 56, 103, 185]),
(true, ![153, 2, 28, 131, 194, 105, 64, 208]),
(true, ![190, 180, 235, 13, 123, 155, 183, 75]),
(true, ![73, 126, 87, 174, 171, 10, 11, 65]),
(true, ![245, 134, 170, 205, 224, 55, 246, 118]),
(true, ![8, 32, 33, 97, 161, 115, 125, 5]),
(true, ![131, 110, 175, 24, 215, 40, 243, 45])]

private theorem root5Prefix16 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![131, 110, 175, 24, 215, 40, 243, 45] : Rows) :=
  valid_mem (![245, 148, 110, 103, 222, 183, 117, 52] : Rows) root5Steps16 (by decide +kernel) (root5Prefix15)

private def root5Steps17 : List Step := [(true, ![13, 2, 12, 7, 210, 237, 80, 192]),
(false, ![6, 118, 237, 230, 210, 12, 246, 243]),
(true, ![88, 5, 15, 249, 255, 111, 125, 80]),
(true, ![176, 45, 26, 103, 63, 195, 243, 51]),
(true, ![146, 192, 179, 64, 240, 186, 80, 159]),
(true, ![72, 207, 231, 183, 37, 165, 51, 230]),
(true, ![52, 213, 56, 11, 67, 59, 159, 249]),
(true, ![6, 102, 105, 246, 194, 28, 230, 103]),
(true, ![88, 129, 155, 125, 123, 235, 249, 64]),
(true, ![176, 185, 10, 243, 171, 87, 103, 183])]

private theorem root5Prefix17 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![176, 185, 10, 243, 171, 87, 103, 183] : Rows) :=
  valid_mem (![131, 110, 175, 24, 215, 40, 243, 45] : Rows) root5Steps17 (by decide +kernel) (root5Prefix16)

private def root5Steps18 : List Step := [(true, ![146, 208, 55, 80, 224, 170, 64, 11]),
(true, ![72, 75, 115, 51, 161, 33, 183, 246]),
(true, ![52, 65, 40, 159, 215, 175, 11, 125]),
(false, ![213, 74, 111, 117, 66, 219, 11, 9]),
(true, ![102, 128, 195, 112, 3, 189, 246, 66]),
(false, ![85, 82, 110, 15, 157, 250, 80, 215]),
(true, ![30, 135, 2, 26, 82, 18, 51, 210]),
(true, ![95, 225, 180, 179, 135, 48, 159, 255]),
(false, ![134, 225, 135, 97, 180, 174, 117, 45]),
(true, ![32, 96, 225, 24, 126, 205, 112, 192])]

private theorem root5Prefix18 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![32, 96, 225, 24, 126, 205, 112, 192] : Rows) :=
  valid_mem (![176, 185, 10, 243, 171, 87, 103, 183] : Rows) root5Steps18 (by decide +kernel) (root5Prefix17)

private def root5Steps19 : List Step := [(true, ![110, 217, 96, 7, 134, 97, 93, 207]),
(true, ![2, 9, 217, 153, 32, 24, 157, 213]),
(true, ![180, 66, 9, 190, 110, 7, 82, 102]),
(true, ![126, 3, 66, 73, 2, 153, 135, 129]),
(true, ![134, 117, 3, 245, 180, 190, 225, 185]),
(true, ![32, 112, 117, 8, 126, 73, 96, 208]),
(true, ![110, 93, 112, 131, 134, 245, 217, 75]),
(true, ![2, 157, 93, 13, 32, 8, 9, 65]),
(true, ![180, 82, 157, 174, 110, 131, 66, 118]),
(true, ![126, 135, 82, 205, 2, 13, 3, 5])]

private theorem root5Prefix19 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![126, 135, 82, 205, 2, 13, 3, 5] : Rows) :=
  valid_mem (![32, 96, 225, 24, 126, 205, 112, 192] : Rows) root5Steps19 (by decide +kernel) (root5Prefix18)

private def root5Steps20 : List Step := [(false, ![148, 180, 128, 245, 118, 6, 157, 144]),
(true, ![16, 126, 120, 8, 5, 88, 82, 252]),
(true, ![132, 134, 222, 131, 45, 176, 135, 74]),
(true, ![148, 32, 144, 13, 192, 146, 225, 128]),
(true, ![16, 110, 252, 174, 207, 72, 96, 120]),
(true, ![132, 2, 74, 205, 213, 52, 217, 222]),
(true, ![148, 180, 128, 97, 102, 6, 9, 144]),
(true, ![16, 126, 120, 24, 129, 88, 66, 252]),
(true, ![132, 134, 222, 7, 185, 176, 3, 74]),
(true, ![148, 32, 144, 153, 208, 146, 117, 128])]

private theorem root5Prefix20 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![148, 32, 144, 153, 208, 146, 117, 128] : Rows) :=
  valid_mem (![126, 135, 82, 205, 2, 13, 3, 5] : Rows) root5Steps20 (by decide +kernel) (root5Prefix19)

private def root5Steps21 : List Step := [(true, ![16, 110, 252, 190, 75, 72, 112, 120]),
(true, ![132, 2, 74, 73, 65, 52, 93, 222]),
(false, ![41, 118, 65, 220, 74, 213, 240, 63]),
(true, ![44, 5, 118, 36, 128, 102, 37, 240]),
(true, ![1, 45, 5, 130, 120, 129, 67, 37]),
(true, ![193, 192, 45, 204, 222, 185, 194, 67]),
(true, ![14, 207, 192, 160, 144, 208, 123, 194]),
(true, ![219, 213, 207, 22, 252, 75, 171, 123]),
(true, ![189, 102, 213, 220, 74, 65, 224, 171]),
(true, ![60, 129, 102, 36, 128, 118, 161, 224])]

private theorem root5Prefix21 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![60, 129, 102, 36, 128, 118, 161, 224] : Rows) :=
  valid_mem (![148, 32, 144, 153, 208, 146, 117, 128] : Rows) root5Steps21 (by decide +kernel) (root5Prefix20)

private def root5Steps22 : List Step := [(true, ![133, 185, 129, 130, 120, 5, 215, 161]),
(true, ![85, 208, 185, 204, 222, 45, 210, 215]),
(true, ![30, 75, 208, 160, 144, 192, 255, 210]),
(false, ![204, 170, 164, 171, 5, 243, 45, 210]),
(true, ![160, 33, 250, 224, 45, 80, 192, 255]),
(true, ![22, 175, 18, 161, 192, 51, 207, 63]),
(true, ![220, 12, 48, 215, 207, 159, 213, 240]),
(true, ![36, 111, 234, 210, 213, 230, 102, 37]),
(true, ![130, 195, 150, 255, 102, 249, 129, 67]),
(true, ![204, 186, 164, 63, 129, 103, 185, 194])]

private theorem root5Prefix22 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![204, 186, 164, 63, 129, 103, 185, 194] : Rows) :=
  valid_mem (![60, 129, 102, 36, 128, 118, 161, 224] : Rows) root5Steps22 (by decide +kernel) (root5Prefix21)

private def root5Steps23 : List Step := [(true, ![160, 165, 250, 240, 185, 64, 208, 123]),
(true, ![22, 59, 18, 37, 208, 183, 75, 171]),
(true, ![220, 28, 48, 67, 75, 11, 65, 224]),
(true, ![36, 235, 234, 194, 65, 246, 118, 161]),
(false, ![130, 1, 234, 133, 74, 80, 2, 64]),
(true, ![204, 193, 150, 85, 128, 51, 180, 183]),
(true, ![160, 14, 164, 30, 120, 159, 126, 11]),
(true, ![22, 219, 250, 95, 222, 230, 134, 246]),
(true, ![220, 189, 18, 41, 144, 249, 32, 125]),
(true, ![36, 60, 48, 44, 252, 103, 110, 243])]

private theorem root5Prefix23 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![36, 60, 48, 44, 252, 103, 110, 243] : Rows) :=
  valid_mem (![204, 186, 164, 63, 129, 103, 185, 194] : Rows) root5Steps23 (by decide +kernel) (root5Prefix22)

private def root5Steps24 : List Step := [(true, ![130, 133, 234, 1, 74, 64, 2, 80]),
(true, ![204, 85, 150, 193, 128, 183, 180, 51]),
(true, ![160, 30, 164, 14, 120, 11, 126, 159]),
(true, ![22, 95, 250, 219, 222, 246, 134, 230]),
(true, ![220, 41, 18, 189, 144, 125, 32, 249]),
(false, ![73, 132, 33, 250, 5, 9, 249, 32]),
(true, ![245, 148, 175, 18, 45, 66, 103, 110]),
(true, ![8, 16, 12, 48, 192, 3, 64, 2]),
(true, ![131, 132, 111, 234, 207, 117, 183, 180]),
(true, ![13, 148, 195, 150, 213, 112, 11, 126])]

private theorem root5Prefix24 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![13, 148, 195, 150, 213, 112, 11, 126] : Rows) :=
  valid_mem (![36, 60, 48, 44, 252, 103, 110, 243] : Rows) root5Steps24 (by decide +kernel) (root5Prefix23)

private def root5Steps25 : List Step := [(true, ![174, 16, 186, 164, 102, 93, 246, 134]),
(true, ![205, 132, 165, 250, 129, 157, 125, 32]),
(true, ![97, 148, 59, 18, 185, 82, 243, 110]),
(true, ![24, 16, 28, 48, 208, 135, 80, 2]),
(true, ![7, 132, 235, 234, 75, 225, 51, 180]),
(false, ![230, 41, 1, 234, 170, 225, 51, 135]),
(true, ![249, 44, 193, 150, 33, 96, 159, 225]),
(true, ![103, 1, 14, 164, 175, 217, 230, 96]),
(true, ![64, 193, 219, 250, 12, 9, 249, 217]),
(true, ![183, 14, 189, 18, 111, 66, 103, 9])]

private theorem root5Prefix25 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![183, 14, 189, 18, 111, 66, 103, 9] : Rows) :=
  valid_mem (![13, 148, 195, 150, 213, 112, 11, 126] : Rows) root5Steps25 (by decide +kernel) (root5Prefix24)

private def root5Steps26 : List Step := [(true, ![11, 219, 60, 48, 195, 3, 64, 66]),
(true, ![246, 189, 133, 234, 186, 117, 183, 3]),
(true, ![125, 60, 85, 150, 165, 112, 11, 117]),
(true, ![243, 133, 30, 164, 59, 93, 246, 112]),
(true, ![80, 85, 95, 250, 28, 157, 125, 93]),
(true, ![51, 30, 41, 18, 235, 82, 243, 157]),
(true, ![159, 95, 44, 48, 87, 135, 80, 82]),
(false, ![117, 134, 20, 174, 16, 180, 246, 128]),
(true, ![112, 32, 104, 205, 132, 126, 125, 120]),
(true, ![93, 110, 90, 97, 148, 134, 243, 222])]

private theorem root5Prefix26 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![93, 110, 90, 97, 148, 134, 243, 222] : Rows) :=
  valid_mem (![183, 14, 189, 18, 111, 66, 103, 9] : Rows) root5Steps26 (by decide +kernel) (root5Prefix25)

private def root5Steps27 : List Step := [(true, ![157, 2, 4, 24, 16, 32, 80, 144]),
(true, ![82, 180, 236, 7, 132, 110, 51, 252]),
(true, ![135, 126, 206, 153, 148, 2, 159, 74]),
(true, ![225, 134, 20, 190, 16, 180, 230, 128]),
(true, ![96, 32, 104, 73, 132, 126, 249, 120]),
(true, ![217, 110, 90, 245, 148, 134, 103, 222]),
(true, ![9, 2, 4, 8, 16, 32, 64, 144])]

private theorem root5Prefix27 : ∃ g ∈ smallGenerated, g.val = Packed.decode (![9, 2, 4, 8, 16, 32, 64, 144] : Rows) :=
  valid_mem (![93, 110, 90, 97, 148, 134, 243, 222] : Rows) root5Steps27 (by decide +kernel) (root5Prefix26)

theorem root5_mem : matrixHom (rootGenerator 5) ∈ smallGenerated := by
  obtain ⟨g, hg, hv⟩ := root5Prefix27
  have heq : matrixHom (rootGenerator 5) = g := by
    apply Units.ext
    exact (rootGenerator_val 5).trans hv.symm
  rw [heq]
  exact hg

theorem sixRoots : SixRoots := by
  intro i
  fin_cases i
  · exact root0_mem
  · exact root1_mem
  · exact root2_mem
  · exact root3_mem
  · exact root4_mem
  · exact root5_mem

end Sporadic.LeechRelated.Co1.CentralizerSection.OrthogonalEmbedding
