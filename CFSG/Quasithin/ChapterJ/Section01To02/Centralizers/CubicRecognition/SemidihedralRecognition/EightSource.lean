module

public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Eight
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition

/-!
# Discharging the D8 recognition input in J.2.7

The proved `n = 3` case of I.4.1 supplies the existing universal
`DihedralEightRecognition` contract. Its original application to the actual
quotient `C_G(B)/B` then gives the marked `M₁₀` isomorphism, including the
image of the two-residual. The preceding local J.2.5/J.2.6 witnesses and
the chosen cubic generator's fusion remain unchanged.

Source: Aschbacher–Smith, J.2.7(2), printed p.435 (PDF p.446).
-/

public section

namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition
universe u

/-- The exact earlier-source recognition implication used by J.2.7. -/
theorem dihedralEightRecognition_source : DihedralEightRecognition.{u} := by
  intro X _ _ h
  exact h.recognize_eight

end CFSG.Quasithin.ChapterJ.SemidihedralRecognition

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- J.2.7(2) on the original quotient, with I.4.1(2) discharged and the
two-residual retained as the actual inner-A₆ subgroup of M₁₀. -/
theorem quotient_marked_M10_recognition_of_source
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    ∃ e : c.CubicQuotient ≃* AlternatingSix.M10.extension,
      (pResidual 2 c.CubicQuotient).map e.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension :=
  c.quotient_marked_M10_recognition
    SemidihedralRecognition.dihedralEightRecognition_source hB t h25 h26 b hb hcontrol

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
