module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements
public import Theory.GroupTheory.SemidihedralSixteenInvolutions
public import Theory.GroupTheory.CentralizerSylowPromotion
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The Sylow and ambient involution-fusion steps of J.2.7

The local witness retains a Sylow subgroup of C_H(B), its actual SD16
marking, its central half-turn z, and its reflection outside K. These
are the marked local data constructed in the proof of J.2.5, not ambient
fusion or recognition assumptions. Their construction remains with the
earlier-source assembly; the quotient isomorphism alone is not this witness.

The center calculation promotes the same subgroup to Sylow in C_G(B).
Every involution of SD16 is its central half-turn or conjugate to its
reflection. J.2.6 fuses the reflection to z; Sylow conjugacy then proves
J.2.7(9) for every involution in C_G(B).

Source: Aschbacher–Smith, printed pp.434–435 (PDF pp.445–446).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterJ.Centralizers
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The marked semidihedral Sylow obtained in the proof of J.2.5.
Only local data in C_H(B) are included; no ambient fusion or recognition is a field. -/
structure CubicLocalTwo {d : LocalSetup G} (c : Choices d) where
  P : Sylow 2 (centralizer ({c.zInGB} : Set c.GB))
  marking : ((P : Subgroup (centralizer ({c.zInGB} : Set c.GB))).map
    (centralizer ({c.zInGB} : Set c.GB)).subtype) ≃*
    Semidihedral.StandardModel 4 (Nat.le_refl 4)
  central_marking : (marking.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) : c.GB) =
    c.zInGB
  reflection_outside :
    ((marking.symm (Semidihedral.standardReflection 4 (Nat.le_refl 4)) : c.GB) : G) ∉
      d.toTypeRuSetup.K

namespace CubicLocalTwo
variable {d : LocalSetup G} {c : Choices d} (t : CubicLocalTwo c)
include t

abbrev TB : Subgroup c.GB := (t.P : Subgroup (centralizer ({c.zInGB} : Set c.GB))).map
  (centralizer ({c.zInGB} : Set c.GB)).subtype

theorem center_TB : (center t.TB).map t.TB.subtype = zpowers c.zInGB := by
  have hc : center t.TB = (center (Semidihedral.StandardModel 4 (Nat.le_refl 4))).map
      t.marking.symm.toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨t.marking x, mem_center_iff.mpr ?_, t.marking.symm_apply_apply x⟩
      intro y
      obtain ⟨y, rfl⟩ := t.marking.surjective y
      simpa only [← map_mul] using congrArg t.marking (mem_center_iff.mp hx y)
    · rintro ⟨y, hy, rfl⟩
      apply mem_center_iff.mpr
      intro x
      apply t.marking.injective
      simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        using mem_center_iff.mp hy (t.marking x)
  rw [hc, Semidihedral.center_standard_sixteen, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers]
  exact congrArg zpowers t.central_marking

theorem z_order : orderOf c.z = 2 := by
  have hr : orderOf (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) = 2 := by
    rw [orderOf_pow_of_dvd (by decide : 4 ≠ 0)
      (by rw [Semidihedral.standardRotation_order]; decide), Semidihedral.standardRotation_order]
    decide
  have hz := t.marking.symm.orderOf_eq (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4)
  rw [← Subgroup.orderOf_coe, t.central_marking, ← Subgroup.orderOf_coe] at hz
  exact hz.trans hr

/-- Promote the literal local Sylow image, without replacing it by a conjugate. -/
theorem exists_sylow_GB : ∃ P : Sylow 2 c.GB, (P : Subgroup c.GB) = t.TB := by
  exact exists_ambient_sylow_of_centralizer_center c.zInGB
    ((Subgroup.orderOf_coe c.zInGB).symm.trans t.z_order) t.P t.center_TB

/-- The reflection used in the model is the actual outer involution of J.2.5. -/
theorem reflection_fused (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z) :
    IsConj ((t.marking.symm (Semidihedral.standardReflection 4 (Nat.le_refl 4)) : c.GB) : G) c.z := by
  let j : t.TB := t.marking.symm (Semidihedral.standardReflection 4 (Nat.le_refl 4))
  have hjH : ((j : c.GB) : G) ∈ d.toTypeRuSetup.H := by
    have hjC : (j : c.GB) ∈ centralizer ({c.zInGB} : Set c.GB) := map_subtype_le _ j.property
    rwa [c.localCentralizer_eq] at hjC
  apply h26.1.2.2
  refine ⟨hjH, t.reflection_outside, ?_⟩
  have hj := t.marking.symm.orderOf_eq (Semidihedral.standardReflection 4 (Nat.le_refl 4))
  rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at hj
  exact hj.trans (Semidihedral.standardReflection_order 4 (Nat.le_refl 4))

/-- Every involution in the marked Sylow image is fused to z, using J.2.6. -/
theorem involution_TB_fused (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (i : t.TB) (hi : orderOf i = 2) : IsConj ((i : c.GB) : G) c.z := by
  rcases Semidihedral.involution_standard_sixteen (t.marking i)
      ((t.marking.orderOf_eq i).trans hi) with he | he
  · have hi' : i = t.marking.symm (Semidihedral.standardRotation 4 (Nat.le_refl 4) ^ 4) :=
      t.marking.injective (he.trans (t.marking.apply_symm_apply _).symm)
    rw [hi', t.central_marking]
    exact IsConj.refl _
  · have hconj := c.GB.subtype.map_isConj
      (t.TB.subtype.map_isConj (t.marking.symm.toMonoidHom.map_isConj he))
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hconj
    exact hconj.trans (t.reflection_fused h26)

/-- J.2.7(9) from the marked J.2.5 Sylow and the actual J.2.6 fusion theorem. -/
theorem involutions_GB_fused (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (i : G) (hiB : i ∈ c.GB) (hi : orderOf i = 2) : IsConj i c.z := by
  obtain ⟨P, hP⟩ := t.exists_sylow_GB
  obtain ⟨j, hj⟩ := P.exists_isConj_of_orderOf_eq_prime_pow
    (x := (⟨i, hiB⟩ : c.GB)) (n := 1)
    (by rw [← Subgroup.orderOf_coe, hi, pow_one])
  have hjorder : orderOf (j : c.GB) = 2 := by
    obtain ⟨g, hg⟩ := hj
    have hh := SemiconjBy.orderOf_eq (g : c.GB) hg
    simpa only [← Subgroup.orderOf_coe, hi] using hh.symm
  have hjmem : (j : c.GB) ∈ t.TB := hP ▸ j.property
  exact (c.GB.subtype.map_isConj hj).trans
    (t.involution_TB_fused h26 ⟨j, hjmem⟩
      ((Subgroup.orderOf_coe (⟨j, hjmem⟩ : t.TB)).symm.trans hjorder))

end CubicLocalTwo
end CFSG.Quasithin.ChapterJ.Centralizers
