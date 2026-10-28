module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.Defs

/-!
# The literal cubic centralizer and normalizer quotients in J.2.7

The chosen B lies in H, and H = C_G(z), so z belongs to C_G(B).
The quotient kernels are the actual subgroup restrictions of B. For |B|=3,
B is abelian and contained in its centralizer; its kernel there is central
and has order three. The kernel in N_G(B) is normal, with the original
ambient image B. No model recognition is assumed.

Source: Aschbacher–Smith, J.2.7, printed pp.435–437 (PDF pp.446–448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers
open Subgroup
variable {G : Type*} [Group G] [Finite G]
namespace Choices
variable {d : LocalSetup G} (c : Choices d)

theorem B_le_H : c.B ≤ d.toTypeRuSetup.H :=
  (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_right)

theorem z_mem_Z : c.z ∈ d.toTypeRuSetup.Z := by
  rw [c.z_generator]
  exact mem_zpowers _

theorem H_eq_centralizer_z : d.toTypeRuSetup.H = centralizer ({c.z} : Set G) := by
  change centralizer (d.toTypeRuSetup.Z : Set G) = _
  rw [c.z_generator, zpowers_eq_closure, centralizer_closure]

theorem z_mem_GB : c.z ∈ c.GB := by
  intro b hb
  exact ((c.B_le_H hb) c.z c.z_mem_Z).symm

def zInGB : c.GB := ⟨c.z, c.z_mem_GB⟩

def cubicKernel : Subgroup c.GB := c.B.subgroupOf c.GB

instance cubicKernel_normal : c.cubicKernel.Normal where
  conj_mem a ha h := by
    change (a : G) ∈ c.B at ha
    change (h : G) * (a : G) * (h : G)⁻¹ ∈ c.B
    have he : (a : G) * (h : G) = (h : G) * (a : G) := h.property a ha
    simpa only [← he, mul_assoc, mul_inv_cancel, mul_one] using ha

abbrev CubicQuotient := c.GB ⧸ c.cubicKernel

def cubicQuotientMap : c.GB →* c.CubicQuotient := QuotientGroup.mk' _

theorem cubicQuotientMap_surjective : Function.Surjective c.cubicQuotientMap :=
  QuotientGroup.mk'_surjective _

theorem cubicQuotientMap_ker : c.cubicQuotientMap.ker = c.cubicKernel :=
  QuotientGroup.ker_mk' _

theorem cubicQuotientMap_ker_image (hB : c.B ≤ c.GB) :
    c.cubicQuotientMap.ker.map c.GB.subtype = c.B := by
  rw [c.cubicQuotientMap_ker]
  exact map_subgroupOf_eq_of_le hB

theorem localCentralizer_eq : centralizer ({c.zInGB} : Set c.GB) =
    d.toTypeRuSetup.H.subgroupOf c.GB := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change (x * c.zInGB = c.zInGB * x) ↔ (x : G) ∈ d.toTypeRuSetup.H
  rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

end Choices
end CFSG.Quasithin.ChapterJ.Centralizers

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The source three-group is central in its own centralizer. -/
theorem B_le_GB_of_card (hB : Nat.card c.B = 3) : c.B ≤ c.GB := by
  let : IsCyclic c.B := isCyclic_of_prime_card hB
  intro b hb x hx
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : c.B) ⟨b, hb⟩)

theorem cubicKernel_card (hB : Nat.card c.B = 3) : Nat.card c.cubicKernel = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe (c.B_le_GB_of_card hB)).toEquiv).trans hB

theorem cubicKernel_le_center : c.cubicKernel ≤ center c.GB := by
  intro b hb
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext ((x.property b hb).symm)

abbrev normalizerKernel : Subgroup c.NB := c.B.subgroupOf c.NB
instance normalizerKernel_normal : c.normalizerKernel.Normal where
  conj_mem b hb g := by
    exact (g.property (b : G)).mp hb

abbrev NormalizerQuotient := c.NB ⧸ c.normalizerKernel

def normalizerQuotientMap : c.NB →* c.NormalizerQuotient := QuotientGroup.mk' _

theorem normalizerQuotientMap_surjective : Function.Surjective c.normalizerQuotientMap :=
  QuotientGroup.mk'_surjective _

theorem normalizerQuotientMap_ker : c.normalizerQuotientMap.ker = c.normalizerKernel :=
  QuotientGroup.ker_mk' _

theorem normalizerQuotientMap_ker_image : c.normalizerQuotientMap.ker.map c.NB.subtype = c.B := by
  rw [c.normalizerQuotientMap_ker]
  exact map_subgroupOf_eq_of_le le_normalizer

theorem GB_le_NB : c.GB ≤ c.NB := Subgroup.centralizer_le_normalizer _

/-- The original centralizer's image inside the normalizer quotient. -/
def centralizerImage : Subgroup c.NormalizerQuotient :=
  (c.GB.subgroupOf c.NB).map c.normalizerQuotientMap

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
