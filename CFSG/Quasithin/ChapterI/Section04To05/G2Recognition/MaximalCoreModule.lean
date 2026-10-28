module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreAction

/-!
# The four-dimensional module of an original cubic endpoint

The marked cubic line is the derived subgroup of the large core D.
The entire endpoint acts on the literal elementary quotient D/D′ of order81.
Its action kernel is exactly D. The projection to D/Z(D) is equivariant,
with kernel the original center plane of order nine. Thus the GL₂(3) actor
has a faithful four-dimensional representation with this invariant plane,
while the quotient is the already marked two-dimensional action.

These constructions retain actual quotient maps, not only dimensions or
abstract module tags. They supply the full module and central-extension
data needed for the endpoint comparison in Aschbacher–Smith I.4.5, p.417.
The remaining Atlas comparison is not asserted here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

/-- The line quotient is the full original abelianization in the large-core branch. -/
theorem cubicCoreLine_eq_commutator (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicCoreLine c t.x=_root_.commutator (cubicOddCore c t.x) := by
  apply (map_injective (cubicOddCore c t.x).subtype_injective)
  rw [cubicCoreLine,map_subgroupOf_eq_of_le (cubic_line_le_oddCore c t.x t.x_order),
    map_subtype_commutator,t.maximal_core_derived hc]

/-- Conjugation preserves the exact marked cubic line. -/
theorem cubicCoreAction_line (a : cubicNormalizer c t.x) :
    (cubicCoreLine c t.x).map (t.cubicCoreAction a).toMonoidHom=cubicCoreLine c t.x := by
  apply eq_of_le_of_card_ge
  · rintro v ⟨d,hd,rfl⟩
    change (a:G)*(d:G)*(a:G)⁻¹∈zpowers ((t.x:c.H):G)
    exact (mem_normalizer_iff.mp a.property (d:G)).mp hd
  · exact le_of_eq (card_map_of_injective (t.cubicCoreAction a).injective).symm

/-- The original whole endpoint acts on its full four-dimensional abelianization. -/
def cubicAbelianizationAction : cubicNormalizer c t.x →*
    MulAut (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) where
  toFun a := QuotientGroup.congr _ _ (t.cubicCoreAction a) (t.cubicCoreAction_line a)
  map_one' := by
    ext v
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
    change QuotientGroup.mk' _ (t.cubicCoreAction 1 v)=QuotientGroup.mk' _ v
    rw [map_one]; rfl
  map_mul' a b := by
    ext v
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
    change QuotientGroup.mk' _ (t.cubicCoreAction (a*b) v)=
      QuotientGroup.mk' _ (t.cubicCoreAction a (t.cubicCoreAction b v))
    rw [map_mul]; rfl

@[simp] theorem cubicAbelianizationAction_mk (a : cubicNormalizer c t.x)
    (v : cubicOddCore c t.x) :
    t.cubicAbelianizationAction a (QuotientGroup.mk' (cubicCoreLine c t.x) v)=
      QuotientGroup.mk' (cubicCoreLine c t.x) (t.cubicCoreAction a v) := rfl

/-- The literal projection from the line quotient to the central quotient. -/
def cubicCentralProjection : (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) →*
    (cubicOddCore c t.x ⧸ center (cubicOddCore c t.x)) :=
  QuotientGroup.map _ _ (.id _) (by intro v hv; exact cubicCoreLine_le_center c t.x hv)

omit [Finite G] in
@[simp] theorem cubicCentralProjection_mk (v : cubicOddCore c t.x) :
    t.cubicCentralProjection (QuotientGroup.mk' (cubicCoreLine c t.x) v)=
      QuotientGroup.mk' (center (cubicOddCore c t.x)) v := rfl

omit [Finite G] in
theorem cubicCentralProjection_surjective : Function.Surjective t.cubicCentralProjection := by
  intro a
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center (cubicOddCore c t.x)) a
  exact ⟨QuotientGroup.mk' (cubicCoreLine c t.x) v,rfl⟩

/-- Both quotient actions commute with the actual central projection. -/
theorem cubicCentralProjection_equivariant (a : cubicNormalizer c t.x)
    (v : cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :
    t.cubicCentralProjection (t.cubicAbelianizationAction a v)=
      t.cubicCentralQuotientAction a (t.cubicCentralProjection v) := by
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
  simp only [cubicAbelianizationAction_mk,cubicCentralProjection_mk]
  change _=quotientAut _ (t.cubicCoreAction a) (QuotientGroup.mk' _ v)
  rw [quotientAut_apply_mk]

theorem cubicAbelianizationAction_kernel (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicAbelianizationAction.ker=(cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x) := by
  apply le_antisymm
  · intro a ha
    rw [←t.cubicCentralQuotientAction_kernel hc]
    apply MulEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := t.cubicCentralProjection_surjective v
    rw [←t.cubicCentralProjection_equivariant]
    change t.cubicCentralProjection (t.cubicAbelianizationAction a w)=t.cubicCentralProjection w
    rw [show t.cubicAbelianizationAction a=1 from ha]
    rfl
  · intro a ha
    let D := cubicOddCore c t.x
    let q := QuotientGroup.mk' (cubicCoreLine c t.x)
    let : IsElementaryAbelian 3 (D ⧸ cubicCoreLine c t.x) := t.left_oddCore_quotient_elementary
    apply MulEquiv.ext
    intro v
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (cubicCoreLine c t.x) v
    change q ((⟨a,ha⟩:D)*v*(⟨a,ha⟩:D)⁻¹)=q v
    rw [map_mul,map_mul,map_inv,mul_comm (q (⟨a,ha⟩:D)),mul_inv_cancel_right]

omit [Finite G] in
theorem maximal_core_abelianization_card (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card (cubicOddCore c t.x ⧸ cubicCoreLine c t.x)=81 := by
  have h := t.left_oddCore_quotient_card
  rw [hc] at h
  omega

/-- The original center plane inside the full abelianization. -/
def cubicCenterPlane : Subgroup (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) :=
  (center (cubicOddCore c t.x)).map (QuotientGroup.mk' (cubicCoreLine c t.x))

omit [Finite G] in
theorem cubicCentralProjection_kernel : t.cubicCentralProjection.ker=t.cubicCenterPlane := by
  rw [cubicCentralProjection,QuotientGroup.ker_map,comap_id]
  rfl

theorem cubicCenterPlane_card (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card t.cubicCenterPlane=9 := by
  have hh := t.cubicCentralProjection.ker.card_mul_index
  rw [index_ker,t.cubicCentralProjection_kernel,
    MonoidHom.range_eq_top.mpr t.cubicCentralProjection_surjective,card_top,
    t.maximal_core_central_quotient_card hc,t.maximal_core_abelianization_card hc] at hh
  omega

theorem cubicCenterPlane_invariant (a : cubicNormalizer c t.x) :
    t.cubicCenterPlane.map (t.cubicAbelianizationAction a).toMonoidHom=t.cubicCenterPlane := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨v,hv,rfl⟩
    rw [←t.cubicCentralProjection_kernel] at hv ⊢
    change t.cubicCentralProjection v=1 at hv
    change t.cubicCentralProjection (t.cubicAbelianizationAction a v)=1
    rw [t.cubicCentralProjection_equivariant,hv,map_one]
  · exact le_of_eq (card_map_of_injective (t.cubicAbelianizationAction a).injective).symm

/-- Matrix coordinates on the full abelianization, rather than just D/Z(D). -/
noncomputable def cubicAbelianizationCoordinates (hc : Nat.card (cubicOddCore c t.x)=243) :
    MulAut (cubicOddCore c t.x ⧸ cubicCoreLine c t.x) ≃*
      Matrix.GeneralLinearGroup (Fin 4) (ZMod 3) := by
  letI := t.left_oddCore_quotient_elementary
  exact IsElementaryAbelian.mulAutLinearEquivOfCard _ (t.maximal_core_abelianization_card hc)

noncomputable def cubicFourLinearAction (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 3) :=
  (t.cubicAbelianizationCoordinates hc).toMonoidHom.comp t.cubicAbelianizationAction

theorem cubicFourLinearAction_kernel (hc : Nat.card (cubicOddCore c t.x)=243) :
    (t.cubicFourLinearAction hc).ker=(cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x) := by
  rw [cubicFourLinearAction,MonoidHom.ker_comp_of_injective _ _
    (t.cubicAbelianizationCoordinates hc).injective,t.cubicAbelianizationAction_kernel hc]

/-- The faithful four-dimensional representation of the same marked GL₂(3) actor. -/
noncomputable def cubicGLFourRepresentation (hc : Nat.card (cubicOddCore c t.x)=243) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →*
      Matrix.GeneralLinearGroup (Fin 4) (ZMod 3) :=
  (t.cubicFourLinearAction hc).comp ((inclusion t.cubicLevi_le_normalizer).comp
    (t.cubicLeviLinearEquiv hc).symm.toMonoidHom)

theorem cubicGLFourRepresentation_injective (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Injective (t.cubicGLFourRepresentation hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hk : inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a) ∈
      (t.cubicFourLinearAction hc).ker := ha
  rw [t.cubicFourLinearAction_kernel hc,←t.cubicLinearAction_kernel hc] at hk
  change t.cubicLeviLinearEquiv hc ((t.cubicLeviLinearEquiv hc).symm a)=1 at hk
  change a=1
  simpa only [MulEquiv.apply_symm_apply] using hk


end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
