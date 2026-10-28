module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.FixedSubgroups

/-!
# The original conjugation actions in the cubic argument

The actor is the intersection of the ambient image of a Sylow two-subgroup
of N_G(B) with the normalizer of the actual Sylow three-subgroup image.
Its action on R and its induced action on the literal quotient R/B are
conjugation by the same elements of G. Fixed points on R are identified
with the corresponding ambient centralizer intersection.

These definitions do not assert the existence of the marked semidihedral
placement. They supply the shared action interface for that construction.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The actual image in G of the chosen Sylow two-subgroup of N_G(B). -/
def twoAmbient (Tplus : Sylow 2 c.NB) : Subgroup G :=
  (Tplus : Subgroup c.NB).map c.NB.subtype

/-- The source's T_R = N_{T_+}(R), expressed entirely in G. -/
def TR (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) : Subgroup G :=
  twoAmbient c Tplus ⊓ normalizer (ambient c R : Set G)

theorem TR_le_NB (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) :
    TR c R Tplus ≤ c.NB :=
  inf_le_left.trans (map_subtype_le _)

theorem TR_le_normalizer (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) :
    TR c R Tplus ≤ normalizer (ambient c R : Set G) := inf_le_right

theorem TR_isPGroup (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) :
    IsPGroup 2 (TR c R Tplus) :=
  (Tplus.isPGroup'.map c.NB.subtype).of_injective
    (inclusion (show TR c R Tplus ≤ twoAmbient c Tplus from inf_le_left))
    (inclusion_injective _)

/-- Conjugation on the actual ambient R, with no change of action. -/
def action (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) :
    TR c R Tplus →* MulAut (ambient c R) :=
  (ambient c R).normalizerMonoidHom.comp (inclusion (TR_le_normalizer c R Tplus))

theorem action_apply (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) (x : ambient c R) :
    (action c R Tplus t x : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl

theorem action_preserves_B (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) :
    (c.B.subgroupOf (ambient c R)).map (action c R Tplus t).toMonoidHom =
      c.B.subgroupOf (ambient c R) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp (TR_le_NB c R Tplus t.property) (y : G)).mp hy
  · intro hx
    refine ⟨(action c R Tplus t).symm x, ?_, (action c R Tplus t).apply_symm_apply x⟩
    have he : ((action c R Tplus t).symm x : G) =
        (t : G)⁻¹ * (x : G) * (t : G) := by
      change ((action c R Tplus t)⁻¹ x : G) = _
      rw [← map_inv, action_apply]
      simp only [coe_inv, inv_inv]
    change ((action c R Tplus t).symm x : G) ∈ c.B
    rw [he]
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (c.NB.inv_mem (TR_le_NB c R Tplus t.property)) (x : G)).mp hx

/-- The quotient is the literal R/B used by the source. -/
abbrev Quotient (R : Sylow 3 c.NB) := ambient c R ⧸ c.B.subgroupOf (ambient c R)

/-- The descended conjugation homomorphism on R/B. -/
def quotientAction (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) :
    TR c R Tplus →* MulAut (Quotient c R) where
  toFun t := QuotientGroup.congr _ _ (action c R Tplus t) (action_preserves_B c R Tplus t)
  map_one' := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (c.B.subgroupOf (ambient c R)) q
    change QuotientGroup.mk' _ (action c R Tplus 1 x) = QuotientGroup.mk' _ x
    rw [map_one]
    rfl
  map_mul' t u := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (c.B.subgroupOf (ambient c R)) q
    change QuotientGroup.mk' _ (action c R Tplus (t * u) x) =
      QuotientGroup.mk' _ (action c R Tplus t (action c R Tplus u x))
    rw [map_mul]
    rfl

theorem quotientAction_mk (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) (x : ambient c R) :
    quotientAction c R Tplus t (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (action c R Tplus t x) := rfl

/-- Action-fixed elements and the ambient centralizer intersection are identical. -/
def fixedEquiv (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (t : TR c R Tplus) :
    {x : ambient c R // action c R Tplus t x = x} ≃
      ↥(ambient c R ⊓ centralizer ({(t : G)} : Set G)) where
  toFun x := ⟨x.val.val, x.val.property, mem_centralizer_singleton_iff.mpr (by
    have h := congrArg Subtype.val x.property
    change (t : G) * x.val.val * (t : G)⁻¹ = x.val.val at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, Subtype.ext (by
    change (t : G) * x.val * (t : G)⁻¹ = x.val
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp x.property.2).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed-point count for the actual marked z, using its Sylow placement in H. -/
theorem fixed_card_z (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (hzT : c.z ∈ TR c R Tplus) :
    Nat.card {x : ambient c R // action c R Tplus ⟨c.z, hzT⟩ x = x} = 3 := by
  rw [Nat.card_congr (fixedEquiv c R Tplus ⟨c.z, hzT⟩), centralizer_z_eq c hB P hP R, hB]

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction
