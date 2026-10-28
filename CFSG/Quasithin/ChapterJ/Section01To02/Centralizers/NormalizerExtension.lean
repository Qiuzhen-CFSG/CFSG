module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.Quotient
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.FusionSylow
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.EightSource

/-!
# The normalizer-extension argument for J.2.7(3)

The proved cubic recognition identifies the actual centralizer image with M10.
An actual involutory inverter of B then constructs the normal index-two
extension and fixes the normalizer quotient order at 1440. The companion
fusion module proves the terminal Sylow/exponent obstruction to the split case.

The source theorem still requires the local equality C_H(s) = T_s, the
H-conjugate inverter construction, the marked extension dichotomy and the
split-case fusion argument. These are not inferred from the conditional
extension construction below. Final Aut(A6) recognition belongs at this boundary
once those obligations are proved; no normalizer identification is assumed here.

Source: Aschbacher–Smith, J.2.7(3), printed p.436 (PDF p.447).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Apply the local inverter-transport implication to the original s. The
transport implication is supplied by the separate local-geometry proof. -/
theorem exists_s_inverting_H_conjugate_of_transport
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) (hinv : c.InverterTransport) :
    ∃ h ∈ d.toTypeRuSetup.H,
      c.InvertsB (h*c.s*h⁻¹) ∧ orderOf (h*c.s*h⁻¹) = 2 := by
  have hsH : c.s ∈ d.toTypeRuSetup.H :=
    d.toTypeRuSetup.T_le_H (d.S_le_T c.s_mem.1)
  have hsKQ := c.s_conjugate_mem_K_sdiff_Q h26 hsH (IsConj.refl c.s)
  obtain ⟨h, hh, hhinv⟩ := hinv c.s hsKQ.1 hsKQ.2 c.s_order_source
  exact ⟨h, hh, hhinv, ((MulAut.conj h).orderOf_eq c.s).trans c.s_order_source⟩

/-- Source M10 recognition on the literal centralizer image; the commuting
quotient diagram records precisely which identification is being used. -/
theorem centralizerImage_M10_of_source
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    ∃ (e : c.centralizerImage ≃* AlternatingSix.M10.extension)
      (eB : c.CubicQuotient ≃* AlternatingSix.M10.extension),
      (∀ x, e (c.cubicEquivCentralizerImage x) = eB x) ∧
      (pResidual 2 c.CubicQuotient).map eB.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension := by
  obtain ⟨eB, heB⟩ := c.quotient_marked_M10_recognition_of_source
    hB t h25 h26 b hb hcontrol
  refine ⟨c.cubicEquivCentralizerImage.symm.trans eB, eB, ?_, heB⟩
  intro x
  exact congrArg eB (c.cubicEquivCentralizerImage.symm_apply_apply x)

/-- Once the local inverter is supplied, the constructed index-two extension
has the order of Aut(A6). Order alone is not the normalizer recognition. -/
theorem normalizerQuotient_card_of_source_inverter
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b)
    (v : G) (hv : c.InvertsB v) (hv2 : orderOf v = 2) :
    Nat.card c.NormalizerQuotient = 1440 := by
  obtain ⟨e, _, _, _⟩ := c.centralizerImage_M10_of_source hB t h25 h26 b hb hcontrol
  have hc : Nat.card c.centralizerImage = 720 :=
    (Nat.card_congr e.toEquiv).trans AlternatingSix.M10.Action.card_extension
  have hi := (c.normalizer_extension_of_inverter hB v hv hv2).2.1
  rw [← c.centralizerImage.index_mul_card, hi, hc]

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
