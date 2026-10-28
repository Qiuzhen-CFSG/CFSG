module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Earlier
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.SylowGeometry

/-!
# The actual Sylow action before the Frattini conclusion

Restrict the compatible H-action to S. Its kernel is S_C, and the image of
S_K is precisely the inner part of the actual Sylow subgroup of Aut(A₆).
The crossing conjugate of S_C is faithful for this action. These transports
use only the earlier-source interface, not rank one or the terminal setup.

Source: Aschbacher–Smith, printed pp.567–568, the action quotient used in
2.5.22–25. The lifting argument for the inner image uses ker(action) ≤ S.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

namespace EarlierSetup
variable (d : EarlierSetup κ G)

theorem k_le_h : d.K ≤ d.H := d.generated ▸ le_sup_left

theorem s_le_h : d.S ≤ d.H := d.generated ▸ le_sup_right

theorem sc_le_s : d.SC ≤ d.S := d.centralizer_K ▸ inf_le_left

theorem sc_le_h : d.SC ≤ d.H := d.sc_le_s.trans d.s_le_h

theorem isTwoGroupS : IsPGroup 2 d.S :=
  d.sylow_eq ▸ d.sylow.isPGroup'.map d.H.subtype

theorem normal_sk : ((d.S ⊓ d.K).subgroupOf d.S).Normal := by
  have hn := (normal_subgroupOf_iff_le_normalizer d.k_le_h).mp d.normalK
  exact normal_subgroupOf_of_le_normalizer
    ((le_inf d.S.le_normalizer (d.s_le_h.trans hn)).trans
      inf_normalizer_le_normalizer_inf)

theorem normal_sc : (d.SC.subgroupOf d.S).Normal := by
  have hn : (d.SC.subgroupOf d.H).Normal := d.action_kernel ▸ inferInstance
  exact normal_subgroupOf_of_le_normalizer (d.s_le_h.trans
    ((normal_subgroupOf_iff_le_normalizer d.sc_le_h).mp hn))

theorem rightConjugate_s : rightConjugate d.x d.S = d.S :=
  mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes)

theorem rightConjugate_le {A : Subgroup G} (hA : A ≤ d.S) :
    rightConjugate d.x A ≤ d.S := d.rightConjugate_s ▸ map_mono hA

theorem rightConjugate_normal {A : Subgroup G} (hA : A ≤ d.S)
    (hn : (A.subgroupOf d.S).Normal) :
    ((rightConjugate d.x A).subgroupOf d.S).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (d.rightConjugate_le hA)).mpr
  have hSN := (normal_subgroupOf_iff_le_normalizer hA).mp hn
  calc
    d.S = rightConjugate d.x d.S := d.rightConjugate_s.symm
    _ ≤ (normalizer (A : Set G)).map (MulAut.conj d.x⁻¹).toMonoidHom := map_mono hSN
    _ ≤ normalizer (rightConjugate d.x A : Set G) := le_normalizer_map _

/-- This uses the trivial center of the actual A₆, not a later involution identity. -/
theorem disjoint_k_sc : Disjoint d.K d.SC := by
  apply disjoint_def.mpr
  intro a haK haC
  have hc : a ∈ centralizer (d.K : Set G) := (d.centralizer_K ▸ haC).2
  have haz : (⟨a, haK⟩ : d.K) ∈ center d.K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (hc k k.property)
  have hz := (Subgroup.centerCongr d.modelK ⟨⟨a, haK⟩, haz⟩).property
  change d.modelK ⟨a, haK⟩ ∈ center A6 at hz
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hz
  exact congrArg Subtype.val (d.modelK.injective (hz.trans d.modelK.map_one.symm))

def sylowAction : d.S →* AutA6 :=
  d.action.comp (inclusion d.s_le_h)

theorem sylowAction_kernel : d.sylowAction.ker = d.SC.subgroupOf d.S := by
  ext s
  change d.action ⟨s, d.s_le_h s.property⟩ = 1 ↔ (s : G) ∈ d.SC
  rw [← MonoidHom.mem_ker, d.action_kernel]
  rfl

def skAction : (d.S ⊓ d.K : Subgroup G) →* AutA6 :=
  d.sylowAction.comp (inclusion inf_le_left)

theorem action_on_K (k : d.K) :
    d.action ⟨k, d.k_le_h k.property⟩ = MulAut.conj (d.modelK k) := by
  ext a : 1
  obtain ⟨b, rfl⟩ := d.modelK.surjective a
  apply d.modelK.symm.injective
  apply Subtype.ext
  rw [d.action_compatible]
  simp [MulAut.conj_apply]


def imageSylow : Sylow 2 AutA6 := d.sylow.mapSurjective d.action_surjective

theorem imageSylow_eq_range : (d.imageSylow : Subgroup AutA6) = d.sylowAction.range := by
  have hSyl : (d.sylow : Subgroup d.H) = d.S.subgroupOf d.H := by
    rw [← d.sylow_eq, subgroupOf, comap_map_eq_self_of_injective d.H.subtype_injective]
  change (d.sylow : Subgroup d.H).map d.action = _
  rw [hSyl]
  ext a
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, d.s_le_h s.property⟩, s.property, rfl⟩

/-- The image is the actual inner Sylow intersection, with both containments proved. -/
theorem skAction_range : d.skAction.range = (d.imageSylow : Subgroup AutA6) ⊓ inner := by
  ext a
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨?_, d.modelK ⟨k, k.property.2⟩, ?_⟩
    · rw [d.imageSylow_eq_range]
      exact ⟨⟨k, k.property.1⟩, rfl⟩
    · exact (d.action_on_K ⟨k, k.property.2⟩).symm
  · rintro ⟨haP, k, hk⟩
    rw [d.imageSylow_eq_range] at haP
    obtain ⟨s, hs⟩ := haP
    let kG : d.K := d.modelK.symm k
    let kH : d.H := ⟨kG, d.k_le_h kG.property⟩
    let sH : d.H := ⟨s, d.s_le_h s.property⟩
    have hkact : d.action kH = a := by
      rw [d.action_on_K]
      simpa only [kG, d.modelK.apply_symm_apply] using hk
    have hc : sH * kH⁻¹ ∈ d.action.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkact]
      change d.sylowAction s * a⁻¹ = 1
      rw [hs, mul_inv_cancel]
    rw [d.action_kernel] at hc
    have hkS : (kG : G) ∈ d.S := by
      have h := d.S.mul_mem (d.S.inv_mem (d.sc_le_s hc)) s.property
      change (((s : G) * (kG : G)⁻¹)⁻¹ * (s : G)) ∈ d.S at h
      simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h
    exact ⟨⟨kG, hkS, kG.property⟩, hkact⟩

/-- The homomorphism to the chosen actual Sylow image. -/
def toImageSylow : d.S →* d.imageSylow :=
  d.sylowAction.codRestrict (d.imageSylow : Subgroup AutA6)
    (fun s => d.imageSylow_eq_range ▸ ⟨s, rfl⟩)

theorem toImageSylow_kernel : d.toImageSylow.ker = d.SC.subgroupOf d.S := by
  rw [← d.sylowAction_kernel]
  ext s
  exact Subtype.ext_iff

/-- The source right-conjugate core maps injectively into the Sylow image. -/
theorem crossing_action_injective : Function.Injective
    (d.toImageSylow.comp (inclusion (d.rightConjugate_le d.sc_le_s))) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro a ha
  have hk : (⟨a, d.rightConjugate_le d.sc_le_s a.property⟩ : d.S) ∈
      d.toImageSylow.ker := ha
  rw [d.toImageSylow_kernel] at hk
  exact Subtype.ext (disjoint_def.mp d.disjoint_conjugate hk a.property)

end EarlierSetup
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
