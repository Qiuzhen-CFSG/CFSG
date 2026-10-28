module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Quotients
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.AmbientLocalCores
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original projective SL₃ outer action

Conjugation in LT acts on the original L/O₂(L), then on its actual projective
quotient. Perfectness detects the full SL₃ action from this projective action.
The kernel can contain odd scalars; its intersection with the original Sylow
two-subgroup lies in O₂(LT). The commutator proof retains the literal quotient
maps and does not assume that the full natural normalizer is centric.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766. The quotient-action
construction follows Closure.Linear.Outside.Multiplicity.RadicalImage.Action,
specialized here to the original invariant flag.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

/-- The supplied component model after the coordinate conjugation. -/
def rotatedModel : (L ⧸ pCore 2 L) ≃* SL(3, S.field.Carrier) :=
  m.groupEquiv.trans (MulAut.conj a)

/-- Conjugation on L/O₂(L), with its supplied model and literal scalar quotient. -/
def projectiveAction : (L ⊔ (T : Subgroup G) : Subgroup G) →*
    MulAut PSL(3, S.field.Carrier) :=
  (quotientAut (center SL(3, S.field.Carrier))).comp
    ((MulAut.congr (rotatedModel D S m a)).toMonoidHom.comp
      (pCoreJoinAction 2 D.sylow_normalizes_component))

/-- The restriction to L is its actual inner projective action. -/
theorem projectiveAction_component (l : L) :
    projectiveAction D S m a (inclusion le_sup_left l) =
      MulAut.conj (QuotientGroup.mk' (center SL(3, S.field.Carrier))
        (rotatedModel D S m a (QuotientGroup.mk' (pCore 2 L) l))) := by
  ext x
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective
    (center SL(3, S.field.Carrier)) x
  change quotientAut (center SL(3, S.field.Carrier))
    (MulAut.congr (rotatedModel D S m a)
      (pCoreJoinAction 2 D.sylow_normalizes_component (inclusion le_sup_left l)))
        (QuotientGroup.mk' _ s) = _
  rw [pCoreJoinAction_on_component, quotientAut_apply_mk]
  change QuotientGroup.mk' _
    (rotatedModel D S m a (QuotientGroup.mk' (pCore 2 L) l *
      (rotatedModel D S m a).symm s * (QuotientGroup.mk' (pCore 2 L) l)⁻¹)) = _
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

/-- Perfectness detects the original SL₃ action from its projective action. -/
theorem projectiveAction_kernel (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : projectiveAction D S m a x = 1) :
    pCoreJoinAction 2 D.sylow_normalizes_component x = 1 := by
  let : Group.IsPerfect SL(3, S.field.Carrier) := Atlas.sl_perfect 3 (by decide)
  apply (MulAut.congr (rotatedModel D S m a)).injective
  rw [map_one]
  apply MulAut.quotient_center_injective
  exact hx.trans (map_one _).symm

/-- A kernel element commutes with the original component modulo its two-core. -/
theorem projectiveAction_kernel_commutator
    (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : projectiveAction D S m a x = 1) (l : L) :
    ⁅(x : G),(l : G)⁆ ∈ L.pCoreIn 2 := by
  have he := congrArg (fun b : MulAut (L ⧸ pCore 2 L) =>
    b (QuotientGroup.mk' (pCore 2 L) l)) (projectiveAction_kernel D S m a x hx)
  rw [pCoreJoinAction_mk] at he
  let y := L.normalizerMonoidHom
    (inclusion (sup_le L.le_normalizer D.sylow_normalizes_component) x) l
  change QuotientGroup.mk' (pCore 2 L) y = QuotientGroup.mk' (pCore 2 L) l at he
  have hh : y * l⁻¹ ∈ pCore 2 L :=
    (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mp (by
      change QuotientGroup.mk' (pCore 2 L) (y * l⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel])
  exact ⟨y*l⁻¹,hh,rfl⟩

/-- The two-elements in the projective kernel lie in O₂(LT). The kernel
itself can contain odd central scalars and is not asserted to be a two-group. -/
theorem sylow_inf_projective_kernel_le_core :
    (T : Subgroup G) ⊓ ((projectiveAction D S m a).ker.map
      (L ⊔ (T : Subgroup G)).subtype) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := (projectiveAction D S m a).ker.map M.subtype
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
    exact (inferInstance : (projectiveAction D S m a).ker.Normal).conj_mem y hy ⟨x,hx⟩
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le (show A ≤ T from inf_le_left))
    (show A ≤ M from inf_le_left.trans le_sup_right)
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl r hr
    refine ⟨?_, (hMB (mem_sup_left hl) r).mp hr.2⟩
    have hc : ⁅l,r⁆ ∈ M.pCoreIn 2 := by
      obtain ⟨x,hx,rfl⟩ := hr.2
      have h := projectiveAction_kernel_commutator D S m a x hx ⟨l,hl⟩
      have h' : ⁅(x : G),l⁆⁻¹ ∈ L.pCoreIn 2 := (L.pCoreIn 2).inv_mem h
      apply hQB
      change ⁅l,(x : G)⁆ ∈ L.pCoreIn 2
      rw [commutatorElement_inv] at h'
      exact h'
    change l * r * l⁻¹ ∈ (T : Subgroup G)
    simpa only [commutatorElement_def, inv_mul_cancel_right] using
      (T : Subgroup G).mul_mem (hQT hc) hr.1
  · exact (le_inf (T : Subgroup G).le_normalizer
      (le_sup_right.trans hMB)).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.SL3Core
