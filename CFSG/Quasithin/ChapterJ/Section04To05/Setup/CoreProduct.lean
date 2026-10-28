module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.SecondCore
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer.Core

/-!
# The two source cores generate the original Sylow subgroup

The second core fixes the chosen natural plane pointwise. The first core
Q cannot do so: its fixed subgroup in U is the original point Z, whose
order is smaller than the plane. Since R₂ has index two in T, this gives
T = R₂Q with the original subgroups and quotient map.

Source: Aschbacher–Smith, J.4.2(1), printed p.440.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The second core lies in the original selected Sylow group. -/
theorem Plane.R₂_le_T : p.R₂ ≤ (d.T : Subgroup G) := by
  rw [p.R₂_eq]
  have h := pCoreIn_le_sylow p.parabolic (d.T.subtype p.sylow_le_parabolic)
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le p.sylow_le_parabolic] using h

/-- The second core fixes the actual four-group pointwise. -/
theorem Plane.R₂_centralizes : p.R₂ ≤ centralizer (p.group : Set G) := by
  intro a ha
  rw [p.R₂_eq] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  have hi : (pCore 2 p.parabolic).map p.quotient ≤
      pCore 2 (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer p.naturalSpace) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance p.quotient p.quotient_surjective,
      pCore_isPGroup.map p.quotient⟩
  have hm := hi (mem_map_of_mem p.quotient hb)
  have hm' := mem_map_of_mem
    (BinaryLinearThree.NaturalPlaneStabilizer.stabilizer p.naturalSpace).subtype hm
  intro v hv
  let x : d.V := ⟨v,p.le_seed hv⟩
  let l : d.L := ⟨b,((p.mem_parabolic _).mp b.property).1⟩
  have hf := BinaryLinearThree.NaturalPlaneStabilizer.core_fixes p.naturalSpace
    p.finrank_naturalSpace _ hm' (d.ru1.natural.coordinates x).toAdd
      ((p.mem_naturalSpace x).mpr hv)
  change BinaryLinearThree.W (p.quotient b : BinaryLinearThree.Group)
    (d.ru1.natural.coordinates x).toAdd = _ at hf
  rw [p.quotient_apply] at hf
  have he := d.ru1.natural.equivariant l x
  have hiq : Function.Injective d.ru1.natural.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [d.ru1.natural.kernel_eq,bot_subgroupOf]
  have heq := hiq (Multiplicative.toAdd.injective (he.trans hf))
  have hc : (b : G) * v * (b : G)⁻¹ = v := congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

/-- Q moves the plane and therefore is not contained in the second core. -/
theorem Plane.not_Q_le_R₂ : ¬ d.toTypeRuSetup.Q ≤ p.R₂ := by
  intro h
  have hf : p.group ≤ centralizer (d.toTypeRuSetup.Q : Set G) :=
    le_centralizer_iff.mp (h.trans p.R₂_centralizes)
  have hU : p.group ≤ d.toTypeRuSetup.U := p.le_seed.trans (le_conjugateSpan _ _)
  have hZ : p.group ≤ d.toTypeRuSetup.Z := by
    rw [← d.centralizer_Q_inf_U]
    exact le_inf hU hf
  have hc := card_le_of_le hZ
  rw [p.card,d.card_Z] at hc
  omega

/-- J.4.2(1), on the original Sylow subgroup and original two-cores. -/
theorem Plane.R₂_sup_Q : p.R₂ ⊔ d.toTypeRuSetup.Q = (d.T : Subgroup G) := by
  have hQT : d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := by
    have h := pCoreIn_le_sylow d.toTypeRuSetup.H (d.T.subtype d.toTypeRuSetup.T_le_H)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le d.toTypeRuSetup.T_le_H] using h
  have hle : p.R₂ ⊔ d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := sup_le p.R₂_le_T hQT
  have hlt : 8192 < Nat.card (p.R₂ ⊔ d.toTypeRuSetup.Q : Subgroup G) := by
    by_contra hn
    have he : p.R₂ = p.R₂ ⊔ d.toTypeRuSetup.Q := eq_of_le_of_card_ge le_sup_left
      (by rw [p.card_R₂]; omega)
    exact p.not_Q_le_R₂ (he ▸ le_sup_right)
  have hd := card_dvd_of_le (show p.R₂ ≤ p.R₂ ⊔ d.toTypeRuSetup.Q from le_sup_left)
  rw [p.card_R₂] at hd
  apply eq_of_le_of_card_ge hle
  rw [d.toTypeRuSetup.card_T_of_card_Z d.card_Z]
  obtain ⟨k,hk⟩ := hd
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup
