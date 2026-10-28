module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedComplement
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.DiagonalAction

/-!
# The marked source diagonal lies in the original quaternion CQ

The model ratio s₅q⁻¹ centralizes the actual five-rotation. Transport through
the marked endpoint puts its original image in C_G(B₅), as well as in the
chosen order32 complement R. The original orders |C_H(B₅)|=40 and |CQ|=8
force R∩C_G(B₅)=CQ. This proves placement in the original quaternion group,
without replacing the still-needed identification with Q₀∩I.
Source: Aschbacher--Smith J.3.6 and J.4.7, printed pp.439,442.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The transported cyclic diagonal centralizes the original B₅. -/
theorem sourceIz_le_G5
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceIz e ≤ G5 B5 := by
  rintro x ⟨a,ha,rfl⟩ b hb
  rw [← hfive] at hb
  obtain ⟨v,hv,rfl⟩ := hb
  have hv' : (v:ReeF4.Model 0)∈five := by
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hv
    exact zpow_mem (mem_zpowers _) n
  have hc := Iz_le_centralizer_five ha v hv'
  have he : v*a=a*v := Subtype.ext hc
  exact (by simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    Subgroup.subtype_apply,map_mul,coe_mul] using
    congrArg (fun y:F => (y:G)) (congrArg e he))

/-- The very same source diagonal belongs to the original J.3 quaternion
centralizer, using the actual compatible complement already constructed. -/
theorem sourceIz_le_CQ
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceIz e ≤ CQ B5 := by
  obtain ⟨R,hIR,hRH,_,hR32,hQR,_,_,_,_⟩ := exists_source_complement c B5 e hz hfive
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  have hle : CQ B5 ≤ R⊓G5 B5 := le_inf hQR inf_le_right
  have h32 : Nat.card (R⊓G5 B5 : Subgroup G)∣32 := hR32 ▸ card_dvd_of_le inf_le_left
  have h40 : Nat.card (R⊓G5 B5 : Subgroup G)∣40 :=
    q.local_card ▸ card_dvd_of_le (inf_le_inf_right _ hRH)
  have he : R⊓G5 B5=CQ B5 := (eq_of_le_of_card_ge hle (by
    rw [CQ_card B5 q]
    exact Nat.le_of_dvd (by decide) (show Nat.card (R⊓G5 B5 : Subgroup G)∣8 from
      Nat.dvd_gcd h32 h40))).symm
  rw [← he]
  exact le_inf ((sourceIz_le_I e).trans hIR) (sourceIz_le_G5 B5 e hfive)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
