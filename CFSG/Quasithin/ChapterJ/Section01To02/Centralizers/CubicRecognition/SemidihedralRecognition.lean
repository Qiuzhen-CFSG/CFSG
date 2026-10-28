module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.RecognitionInputs
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.LocalReduction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.Intrinsic

/-!
# Semidihedral recognition of the literal cubic quotient

The intrinsic recognition theorem applies to the actual quotient C_G(B)/B,
with the image of the chosen z and its proved centralizer equivalence. It
identifies that quotient with the specified M10 subgroup of Aut(A6), and
maps its actual two-residual onto the restricted inner-A6 subgroup.

Exactly I.4.1(2), the earlier local source inputs and fusion of the chosen
cubic generator remain explicit. Their source producers and final discharge
belong to the centralizer and cubic-recognition assembly owners.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The exact intrinsic recognition input on the original quotient map. -/
def semidihedralRecognitionHypotheses (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    SemidihedralRecognition.Hypotheses c.CubicQuotient :=
  let hi := c.quotient_recognition_hypotheses hB t h25 h26 b hb hcontrol
  { z := c.cubicQuotientMap c.zInGB
    z_order := hi.1
    involutions_conjugate := hi.2.1
    centralizer_equiv := hi.2.2 }

/-- The Sylow and transfer deductions for the literal C_G(B)/B. -/
theorem quotient_sylow_and_transfer (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    (∃ S : Sylow 2 c.CubicQuotient, (S : Subgroup c.CubicQuotient) =
      centralizer ({c.cubicQuotientMap c.zInGB} : Set c.CubicQuotient)) ∧
    (∃ N : Subgroup c.CubicQuotient, N.Normal ∧ N.index = 2) ∧
    pResidual 2 c.CubicQuotient ≠ ⊤ := by
  let hi := c.semidihedralRecognitionHypotheses hB t h25 h26 b hb hcontrol
  exact ⟨hi.centralizer_isSylow, hi.exists_normal_index_two, hi.twoResidual_ne_top⟩

/-- Conditional J.2.7(2) on the literal quotient, retaining its two-residual
as the actual inner-A₆ subgroup of M₁₀. The sole recognition premise is I.4.1(2). -/
theorem quotient_marked_M10_recognition
    (hI : SemidihedralRecognition.DihedralEightRecognition.{u})
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    ∃ e : c.CubicQuotient ≃* AlternatingSix.M10.extension,
      (pResidual 2 c.CubicQuotient).map e.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension :=
  (c.semidihedralRecognitionHypotheses hB t h25 h26 b hb hcontrol).recognize_marked hI

/-- Conditional J.2.7(2): the original C_G(B)/B is the actual M₁₀. -/
theorem quotient_M10_recognition
    (hI : SemidihedralRecognition.DihedralEightRecognition.{u})
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    Nonempty (c.CubicQuotient ≃* AlternatingSix.M10.extension) :=
  ⟨(c.quotient_marked_M10_recognition hI hB t h25 h26 b hb hcontrol).choose⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
