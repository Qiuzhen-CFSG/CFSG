module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Placement.Transport
public import Theory.SpecificGroups.AlternatingSix.M10.InvolutionAlignment

/-!
# Aligning the original involution in the cubic normalizer

The literal marked quotient map sends the original z to an involution of the
specified M₁₀ extension. The model involution theorem supplies an actual
six-letter permutation carrying the canonical center (02)(13) to that image.
This discharges the alignment premise in `Placement.Lift.rotation_four` and
`Placement.Lift.embedded_center`; constructing the compatible lift is separate.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448), the choice of the
semidihedral normalizer with center ⟨z⟩ in the final cubic argument.
-/

public section

namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
open AlternatingSix.ShadowLocal
open AlternatingSix.M10.LocalGeometry

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The original marked involution is a permutation conjugate of the canonical center. -/
theorem exists_marked_z_alignment (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* AutA6)
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension) :
    ∃ σ : Equiv.Perm (Fin 6), markedMap c e (zInNB c) =
      (MulAut.conj (permutationAction σ)) (permutationAction (standardU * standardZ)) :=
  AlternatingSix.M10.InvolutionAlignment.exists_permutation_alignment
    (markedMap c e (zInNB c)) (marked_z_order c hB hz e)
    (marked_z_mem_extension c e hM)

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.Placement
