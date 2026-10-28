module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Multiplicity.Sylow
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.PCoreInRestriction

/-! The actual projective outer action of LT, with its original quotient maps.
Source: Aschbacher--Smith 11.5.7, printed pp.781--782. -/

@[expose] public noncomputable section
open Subgroup Representation Matrix
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
  (a : SL(3, E.input.field.Carrier))

def rotatedModel : (L ⧸ pCore 2 L) ≃* SL(3, E.input.field.Carrier) :=
  m.groupEquiv.trans (MulAut.conj a)

/-- Conjugation on L/O₂(L), with its supplied model and literal scalar quotient. -/
def projectiveAction : (L ⊔ (T : Subgroup G) : Subgroup G) →*
    MulAut PSL(3, E.input.field.Carrier) :=
  (quotientAut (center SL(3, E.input.field.Carrier))).comp
    ((MulAut.congr (rotatedModel E m a)).toMonoidHom.comp
      (pCoreJoinAction 2 D.sylow_normalizes_component))

/-- The restriction to L is its actual inner projective action. -/
theorem projectiveAction_component (l : L) :
    projectiveAction E m a (inclusion le_sup_left l) =
      MulAut.conj (QuotientGroup.mk' (center SL(3, E.input.field.Carrier))
        (rotatedModel E m a (QuotientGroup.mk' (pCore 2 L) l))) := by
  ext x
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective
    (center SL(3, E.input.field.Carrier)) x
  change quotientAut (center SL(3, E.input.field.Carrier))
    (MulAut.congr (rotatedModel E m a)
      (pCoreJoinAction 2 D.sylow_normalizes_component (inclusion le_sup_left l)))
        (QuotientGroup.mk' _ s) = _
  rw [pCoreJoinAction_on_component, quotientAut_apply_mk]
  change QuotientGroup.mk' _
    (rotatedModel E m a (QuotientGroup.mk' (pCore 2 L) l *
      (rotatedModel E m a).symm s * (QuotientGroup.mk' (pCore 2 L) l)⁻¹)) = _
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

/-- Perfectness detects the original SL₃ action from its projective action. -/
theorem projectiveAction_kernel (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : projectiveAction E m a x = 1) :
    pCoreJoinAction 2 D.sylow_normalizes_component x = 1 := by
  let : Group.IsPerfect SL(3, E.input.field.Carrier) := Atlas.sl_perfect 3 (by decide)
  apply (MulAut.congr (rotatedModel E m a)).injective
  rw [map_one]
  apply MulAut.quotient_center_injective
  exact hx.trans (map_one _).symm

/-- In ambient terms, the projective kernel centralizes the original L/O₂(L). -/
theorem projectiveAction_kernel_centralizes
    (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : projectiveAction E m a x = 1) :
    (x : G) ∈ coreQuotientCentralizer L := by
  refine ⟨inclusion (sup_le L.le_normalizer D.sylow_normalizes_component) x,?_,rfl⟩
  exact projectiveAction_kernel E m a x hx

/-- The two-elements in the projective kernel lie in O₂(LT). The kernel
itself can contain odd central scalars and is not asserted to be a two-group. -/
theorem sylow_inf_projective_kernel_le_core :
    (T : Subgroup G) ⊓ ((projectiveAction E m a).ker.map
      (L ⊔ (T : Subgroup G)).subtype) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := (projectiveAction E m a).ker.map M.subtype
  let A := (T : Subgroup G) ⊓ B
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow M (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right)] at h
  have hQB : L.pCoreIn 2 ≤ M.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hMB : M ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    rintro x hx b ⟨y,hy,rfl⟩
    refine ⟨(⟨x,hx⟩ : M) * y * ⟨x,hx⟩⁻¹,?_,rfl⟩
    exact (inferInstance : (projectiveAction E m a).ker.Normal).conj_mem y hy ⟨x,hx⟩
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le (show A ≤ T from inf_le_left))
    (show A ≤ M from inf_le_left.trans le_sup_right)
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl r hr
    refine ⟨?_, (hMB (mem_sup_left hl) r).mp hr.2⟩
    have hrC : r ∈ coreQuotientCentralizer L := by
      obtain ⟨x,hx,rfl⟩ := hr.2
      exact projectiveAction_kernel_centralizes E m a x hx
    have hc : ⁅l,r⁆ ∈ M.pCoreIn 2 := by
      have h := coreQuotientCentralizer_commutator hrC hl
      have h' : ⁅r,l⁆⁻¹ ∈ L.pCoreIn 2 := (L.pCoreIn 2).inv_mem h
      exact hQB (by simpa only [commutatorElement_inv] using h')
    change l * r * l⁻¹ ∈ (T : Subgroup G)
    simpa only [commutatorElement_def, inv_mul_cancel_right] using
      (T : Subgroup G).mul_mem (hQT hc) hr.1
  · exact (le_inf (T : Subgroup G).le_normalizer
      (le_sup_right.trans hMB)).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.RadicalImage
