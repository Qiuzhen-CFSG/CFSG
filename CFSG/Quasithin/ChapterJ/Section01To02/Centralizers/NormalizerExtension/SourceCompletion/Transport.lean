module
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Cubic
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.LocalGeometry

/-!
# Source inverters and the quaternion test for membership in K

Every involution of H outside Q normalizes a dihedral group with an odd
cubic rotation. Sylow conjugacy in H transports that rotation to the original
B. This includes a member of the distinguished z-class, obtained from the
marked SD16 reflection. Separately, an involution of H centralizing C_Q(B)
belongs to K: otherwise the genuine indecomposable six-dimensional Ru2 action
would move a quaternion vector.

The private dihedral lifting lemma in `LocalGeometry` is deliberately reused
through `import all`; its original statement already permits every H-member
outside Q, while the older public wrapper was restricted to K.

Source: Aschbacher–Smith J.2.7(3), printed p.436 (PDF p.447).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- Transport any involution of H outside Q to an inverter of the specified B. -/
public theorem H_inverter_transport_source (i : G) (hiH : i ∈ d.toTypeRuSetup.H)
    (hiQ : i ∉ d.toTypeRuSetup.Q) (hi2 : orderOf i = 2) :
    ∃ h ∈ d.toTypeRuSetup.H, c.InvertsB (h*i*h⁻¹) := by
  obtain ⟨P, hP⟩ := SourceCompletion.source_sylowThree_H c
  let w : d.toTypeRuSetup.H := ⟨i, hiH⟩
  have hw : w ^ 2 = 1 := Subtype.ext (hi2 ▸ pow_orderOf_eq_one i)
  obtain ⟨A, hA, hinv⟩ := inverted_three_in_H d w hw hiQ
  obtain ⟨R, hAR⟩ := (IsPGroup.of_card (p := 3) (n := 1) hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq d.toTypeRuSetup.H R P
  let e := MulAut.conj g
  have hAP : A.map e.toMonoidHom ≤ (P : Subgroup d.toTypeRuSetup.H) := by
    rw [← hg]
    exact map_mono hAR
  have hB : Nat.card c.B = 3 :=
    SpecialCore.cubicSubgroup_card d.toTypeRuSetup c.sylowThree d.card_Z
      (d.center_eq.le.trans inf_le_left)
  have hPc : Nat.card (P : Subgroup d.toTypeRuSetup.H) = 3 := by
    have hc := congrArg (fun U : Subgroup G => Nat.card U) hP
    rw [card_map_of_injective d.toTypeRuSetup.H.subtype_injective, hB] at hc
    exact hc
  have hAPeq : A.map e.toMonoidHom = (P : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hAP (by rw [card_map_of_injective e.injective, hA, hPc])
  refine ⟨g, g.property, ?_⟩
  intro b hb
  rw [← hP] at hb
  obtain ⟨bH, hbH, rfl⟩ := hb
  rw [← hAPeq] at hbH
  obtain ⟨a, ha, rfl⟩ := hbH
  have he := congrArg e (hinv a ha)
  simp only [map_mul, map_inv] at he
  have heG := congrArg (fun x : d.toTypeRuSetup.H => (x : G)) he
  exact heG

/-- The original z-class has an involutory inverter of B lying in H. -/
public theorem exists_z_class_inverter_source : ∃ u : G,
    u ∈ d.toTypeRuSetup.H ∧ IsConj c.z u ∧ c.InvertsB u ∧ orderOf u = 2 := by
  obtain ⟨t⟩ := SourceCompletion.cubicLocalTwo c
  let j : t.TB := t.marking.symm (Semidihedral.standardReflection 4 (Nat.le_refl 4))
  have hjH : ((j : c.GB) : G) ∈ d.toTypeRuSetup.H := by
    have hjC : (j : c.GB) ∈ centralizer ({c.zInGB} : Set c.GB) := map_subtype_le _ j.property
    rwa [c.localCentralizer_eq] at hjC
  have hjQ : ((j : c.GB) : G) ∉ d.toTypeRuSetup.Q :=
    fun h => t.reflection_outside (d.Q_le_K h)
  have hj2 : orderOf ((j : c.GB) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact (t.marking.symm.orderOf_eq _).trans (Semidihedral.standardReflection_order 4 (Nat.le_refl 4))
  obtain ⟨h, hh, hhinv⟩ := c.H_inverter_transport_source _ hjH hjQ hj2
  refine ⟨h*((j : c.GB) : G)*h⁻¹, ?_, ?_, hhinv, ?_⟩
  · exact d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.mul_mem hh hjH)
      (d.toTypeRuSetup.H.inv_mem hh)
  · exact (t.reflection_fused (SourceCompletion.fusion c).2.2.1).symm.trans
      (isConj_iff.mpr ⟨h, rfl⟩)
  · exact ((MulAut.conj h).orderOf_eq _).trans hj2

/-- The genuine Ru2 action detects K using its fixed quaternion subgroup. -/
public theorem involution_mem_K_of_centralizes_quaternion
    (i : G) (hiH : i ∈ d.toTypeRuSetup.H) (hi2 : orderOf i = 2)
    (hc : ∀ q ∈ Fusion.HB d.toTypeRuSetup c.sylowThree, Commute i q) :
    i ∈ d.toTypeRuSetup.K := by
  by_contra hiK
  let head := d.fusionNaturalHead
  let cp := Fusion.centralProductData_of_quaternion d c.sylowThree
    (SourceCompletion.quaternion c.sylowThree)
  let iH : d.toTypeRuSetup.H := ⟨i, hiH⟩
  have ht := Fusion.Outer.quotientMap_not_alternating d.toTypeRuSetup d.Q_le_K iH hiK
  have ht2 := Fusion.Outer.quotientMap_involution d.toTypeRuSetup iH hi2
  have hmoved := head.sixProjection_kernel_moved d
    (fun q hq k hk => d.HC_commutator_K_mem_U ⟨q, hq⟩ ⟨k, hk⟩) _ ht ht2
  obtain ⟨q, hq, hne⟩ := head.quaternion_moved_of_kernel_moved d c.sylowThree cp iH hmoved
  apply hne
  have he : ⁅i, q⁆ = 1 := by
    change i*q*i⁻¹*q⁻¹ = 1
    rw [hc q hq]
    group
  change ⁅i, q⁆ ∈ d.toTypeRuSetup.Z
  rw [he]
  exact d.toTypeRuSetup.Z.one_mem

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
