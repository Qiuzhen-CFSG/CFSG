module

public import Theory.SpecificGroups.AlternatingSix.M10.SylowRecognition
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.LocalReduction

/-!
# The A₆ extension branch of intrinsic semidihedral recognition

The involution centralizer is an actual Sylow subgroup by the intrinsic
local reduction. Its given SD16 model selects the specified M₁₀ extension
once the normal index-two subgroup has been identified with A₆. The latter
identification remains the earlier I.4.1 input of the source assembly.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses

variable {W : Type*} [Group W] [Finite W]

/-- The A₆ branch gives an actual M₁₀ equivalence, with the original normal
subgroup mapped to the literal inner automorphisms. -/
theorem exists_marked_M10_equiv (h : Hypotheses W)
    (N : Subgroup W) [N.Normal] (hi : N.index = 2)
    (eN : N ≃* alternatingGroup (Fin 6)) :
    ∃ e : W ≃* AlternatingSix.M10.extension,
      N.map e.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension := by
  obtain ⟨S, hS⟩ := h.centralizer_isSylow
  exact AlternatingSix.M10.SylowRecognition.exists_marked_equiv N hi eN S
    ((MulEquiv.subgroupCongr hS).trans h.model)

end CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses
