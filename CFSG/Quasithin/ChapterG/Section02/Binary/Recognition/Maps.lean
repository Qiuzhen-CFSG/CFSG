module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Geometry
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Literal maps for binary quotient recognition

The restricted star maps retain the original quotient LT/O₂(LT).
The conjugation map on V is defined from the given natural coordinates
and the original T-invariance. These maps provide common interfaces for
the small permutation-action calculation and the residual generation lift.

Source: Aschbacher–Smith, G.2.3(1–2), printed p.333.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] {D : Setup G}

/-- The original quotient, restricted to an actual subgroup of LT. -/
def binaryStarRestriction (D : Setup G) (A : Subgroup G) (hA : A ≤ D.LT) :
    A →* D.Star :=
  (QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion hA)

theorem binaryStarRestriction_range (A : Subgroup G) (hA : A ≤ D.LT) :
    (D.binaryStarRestriction A hA).range = D.star A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨inclusion hA a, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem binaryStarRestriction_map (A B : Subgroup G) (hA : A ≤ D.LT)
    (hBA : B ≤ A) :
    (B.subgroupOf A).map (D.binaryStarRestriction A hA) = D.star B := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨inclusion hA b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hBA hb⟩, hb, rfl⟩

theorem binaryStarRestriction_ker (A : Subgroup G) (hA : A ≤ D.LT) :
    (D.binaryStarRestriction A hA).ker =
      (pCore 2 D.LT).comap (inclusion hA) := by
  ext a
  exact QuotientGroup.eq_one_iff _

theorem binaryStarRestriction_ker_isPGroup (A : Subgroup G) (hA : A ≤ D.LT) :
    IsPGroup 2 (D.binaryStarRestriction A hA).ker := by
  rw [binaryStarRestriction_ker]
  exact pCore_isPGroup.comap_of_injective (inclusion hA) (inclusion_injective hA)

theorem binary_star_mono {A B : Subgroup G} (hAB : A ≤ B) : D.star A ≤ D.star B :=
  map_mono (comap_mono hAB)

theorem binary_star_sup (A B : Subgroup G) (hA : A ≤ D.LT) (hB : B ≤ D.LT) :
    D.star (A ⊔ B) = D.star A ⊔ D.star B := by
  rw [star, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

variable [Finite G]

theorem BaseHypothesis.binary_T_isPGroup (h : D.BaseHypothesis) : IsPGroup 2 D.T := by
  obtain ⟨P, hP⟩ := h.sylow_LT
  rw [← hP]
  exact P.isPGroup'.map D.LT.subtype

theorem BaseHypothesis.binary_U_isPGroup (h : D.BaseHypothesis) (hUT : D.U ≤ D.T) :
    IsPGroup 2 D.U := h.binary_T_isPGroup.to_le hUT

theorem BaseHypothesis.binary_T_normalizes_U (h : D.BaseHypothesis) :
    D.T ≤ normalizer (D.U : Set G) :=
  (le_sup_right.trans h.local_le).trans (le_normalizer_conjugateSpanBy D.V D.H)

theorem BaseHypothesis.binary_core_le_T (h : D.BaseHypothesis) : D.LT.pCoreIn 2 ≤ D.T := by
  obtain ⟨P, hP⟩ := h.sylow_LT
  exact hP ▸ pCoreIn_le_sylow D.LT P

theorem BinaryNaturalData.binary_LT_normalizes_V (b : D.BinaryNaturalData)
    (h : D.BaseHypothesis) : D.LT ≤ normalizer (D.V : Set G) :=
  sup_le b.L_normalizes_V h.T_normalizes_V

/-- Conjugation on the original four-group, before passing to any quotient. -/
def binaryConjugation (D : Setup G) (h : D.BaseHypothesis) (b : D.BinaryNaturalData) :
    D.LT →* MulAut D.V :=
  D.V.normalizerMonoidHom.comp (inclusion (b.binary_LT_normalizes_V h))

theorem binaryConjugation_apply (h : D.BaseHypothesis) (b : D.BinaryNaturalData)
    (x : D.LT) (v : D.V) :
    ((D.binaryConjugation h b x v : D.V) : G) = (x : G) * (v : G) * (x : G)⁻¹ := rfl

omit [Finite G] in
theorem binary_I_le_join {g : G} (hgL : g ∈ D.L) : D.I g ≤ D.L ⊔ D.U := by
  refine sup_le le_sup_right ?_
  rintro x ⟨u, hu, rfl⟩
  change g⁻¹ * u * g⁻¹⁻¹ ∈ D.L ⊔ D.U
  rw [inv_inv]
  exact (D.L ⊔ D.U).mul_mem
    ((D.L ⊔ D.U).mul_mem ((D.L ⊔ D.U).inv_mem (mem_sup_left hgL))
      (mem_sup_right hu)) (mem_sup_left hgL)

omit [Finite G] in
theorem binary_join_le_LT (hUT : D.U ≤ D.T) : D.L ⊔ D.U ≤ D.LT :=
  sup_le le_sup_left (hUT.trans le_sup_right)

omit [Finite G] in
theorem binary_I_le_LT (hUT : D.U ≤ D.T)
    {g : G} (hgL : g ∈ D.L) : D.I g ≤ D.LT :=
  (binary_I_le_join hgL).trans (binary_join_le_LT hUT)

end CFSG.Quasithin.ChapterG.Section02.Setup
