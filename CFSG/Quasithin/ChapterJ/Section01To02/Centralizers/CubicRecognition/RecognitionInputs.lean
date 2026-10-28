module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.QuotientFusion
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# The exact semidihedral recognition input on C_G(B)/B

Coprime centralizer lifting identifies the centralizer of the image of z
with the image of C_H(B). The kernel of the original inclusion followed by
the quotient map is precisely B restricted to C_H(B); the first isomorphism
theorem therefore transports J.2.5's SD16 marking to that centralizer.
The image of z still has order two because the kernel has order three.

Together with the preceding fusion results, this supplies one involution
class and an SD16 involution centralizer on the literal C_G(B)/B. Transfer,
recognition of its O² subgroup via I.4.1(2), exclusion of PSL3(2), and
identification with the concrete M10 remain separate obligations. None is
asserted by the input theorem below.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
noncomputable section

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

theorem quotient_z_order (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2) :
    orderOf (c.cubicQuotientMap c.zInGB) = 2 := by
  have hz' : orderOf c.zInGB = 2 := (Subgroup.orderOf_coe c.zInGB).symm.trans hz
  apply orderOf_eq_prime
  · rw [← map_pow, ← hz', pow_orderOf_eq_one, map_one]
  · intro he
    have hk : c.zInGB ∈ c.cubicKernel := by
      rw [← c.cubicQuotientMap_ker]
      exact he
    have hd := c.cubicKernel.orderOf_dvd_natCard hk
    rw [hz', c.cubicKernel_card hB] at hd
    norm_num at hd

/-- The involution centralizer in the literal quotient is the image of C_H(B).
Coprime centralizer lifting discharges surjectivity; the actual map is retained. -/
theorem localCentralizer_quotient_image (hB : Nat.card c.B = 3) (hz : orderOf c.z = 2) :
    (centralizer ({c.zInGB} : Set c.GB)).map c.cubicQuotientMap =
      centralizer ({c.cubicQuotientMap c.zInGB} : Set c.CubicQuotient) := by
  let T := zpowers c.zInGB
  let : Fact (IsPGroup 2 T) := ⟨IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact hz)⟩
  have h := centralizer_map_quotient_eq_map_centralizer 2 T c.cubicKernel inferInstance
    (by rw [c.cubicKernel_card hB]; decide)
  dsimp only [T] at h
  rw [MonoidHom.map_zpowers] at h
  simpa only [zpowers_eq_closure, centralizer_closure, cubicQuotientMap] using h.symm

/-- J.2.5 supplies exactly the SD16 involution centralizer needed for recognition
of C_G(B)/B. The equivalence is induced by the original subgroup inclusion. -/
theorem quotient_centralizer_semidihedral (hB : Nat.card c.B = 3)
    (hz : orderOf c.z = 2) (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree) :
    Nonempty ((centralizer ({c.cubicQuotientMap c.zInGB} : Set c.CubicQuotient)) ≃*
      Semidihedral.StandardModel 4 (Nat.le_refl 4)) := by
  let C := Fusion.CB d.toTypeRuSetup c.sylowThree
  let inc : C →* c.GB := inclusion inf_le_right
  let f := c.cubicQuotientMap.comp inc
  have hk : f.ker = c.B.subgroupOf C := by
    ext x
    change c.cubicQuotientMap (inc x) = 1 ↔ (x : G) ∈ c.B
    change inc x ∈ c.cubicQuotientMap.ker ↔ _
    rw [c.cubicQuotientMap_ker]
    rfl
  have hinc : inc.range = centralizer ({c.zInGB} : Set c.GB) := by
    rw [c.localCentralizer_eq]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property.1
    · intro hx
      exact ⟨⟨x, hx, x.property⟩, rfl⟩
  have hr : f.range = centralizer ({c.cubicQuotientMap c.zInGB} : Set c.CubicQuotient) := by
    rw [MonoidHom.range_comp, hinc]
    exact c.localCentralizer_quotient_image hB hz
  let : (c.B.subgroupOf C).Normal := hk ▸ (inferInstance : f.ker.Normal)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))
  exact ⟨e.symm.trans h25.2.2.some⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The complete input to semidihedral involution-centralizer recognition,
on the actual C_G(B)/B. Recognition itself is a separate source step. -/
theorem quotient_recognition_hypotheses (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    orderOf (c.cubicQuotientMap c.zInGB) = 2 ∧
      (∀ x : c.CubicQuotient, orderOf x = 2 →
        IsConj x (c.cubicQuotientMap c.zInGB)) ∧
      Nonempty ((centralizer ({c.cubicQuotientMap c.zInGB} : Set c.CubicQuotient)) ≃*
        Semidihedral.StandardModel 4 (Nat.le_refl 4)) :=
  ⟨c.quotient_z_order hB t.z_order,
    c.involutions_cubicQuotient_isConj hB t h26 b hb hcontrol,
    c.quotient_centralizer_semidihedral hB t.z_order h25⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
