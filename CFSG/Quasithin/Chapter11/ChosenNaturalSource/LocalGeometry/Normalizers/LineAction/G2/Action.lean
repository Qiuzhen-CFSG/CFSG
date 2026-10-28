module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.SourceFlag
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original G₂ quotient action and its Sylow kernel

Conjugation by LT on L/O₂(L) is transported through the actual G₂ marking
and one inner alignment. A kernel element commutes with L modulo O₂(L).
Consequently the kernel's intersection with the original Sylow lies in
O₂(LT). This is the lifting step for the point-radical product in Comparison;
no splitting of the central kernel of the chosen module is used.

Source: Aschbacher--Smith 11.1.5 and 11.2.3, printed pp.765--766,768--769.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction
    (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
  (a : Atlas.G2.Model S.field.Carrier)
/-- The supplied component model after the coordinate conjugation. -/
def rotatedModel : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model S.field.Carrier :=
  m.groupEquiv.trans (MulAut.conj a)

/-- Conjugation on L/O₂(L), with its supplied G₂ model. -/
def quotientAction : (L ⊔ (T : Subgroup G) : Subgroup G) →*
    MulAut (Atlas.G2.Model S.field.Carrier) :=
  (MulAut.congr (rotatedModel D S m a)).toMonoidHom.comp
    (pCoreJoinAction 2 D.sylow_normalizes_component)

/-- The restriction to L is its actual inner G₂ action. -/
theorem quotientAction_component (l : L) :
    quotientAction D S m a (inclusion le_sup_left l) =
      MulAut.conj (rotatedModel D S m a (QuotientGroup.mk' (pCore 2 L) l)) := by
  change MulAut.congr (rotatedModel D S m a)
    (pCoreJoinAction 2 D.sylow_normalizes_component (inclusion le_sup_left l)) = _
  rw [pCoreJoinAction_on_component]
  apply MulEquiv.ext
  intro x
  change rotatedModel D S m a ((QuotientGroup.mk' (pCore 2 L) l) *
    (rotatedModel D S m a).symm x * (QuotientGroup.mk' (pCore 2 L) l)⁻¹) = _
  simp only [map_mul,map_inv,MulEquiv.apply_symm_apply,MulAut.conj_apply]

/-- Transport through the marking detects the original quotient action. -/
private theorem quotientAction_kernel (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : quotientAction D S m a x = 1) :
    pCoreJoinAction 2 D.sylow_normalizes_component x = 1 := by
  apply (MulAut.congr (rotatedModel D S m a)).injective
  exact hx.trans (map_one _).symm

/-- A kernel element commutes with the original component modulo its two-core. -/
private theorem quotientAction_kernel_commutator
    (x : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hx : quotientAction D S m a x = 1) (l : L) :
    ⁅(x : G),(l : G)⁆ ∈ L.pCoreIn 2 := by
  have he := congrArg (fun b : MulAut (L ⧸ pCore 2 L) =>
    b (QuotientGroup.mk' (pCore 2 L) l)) (quotientAction_kernel D S m a x hx)
  rw [pCoreJoinAction_mk] at he
  let y := L.normalizerMonoidHom
    (inclusion (sup_le L.le_normalizer D.sylow_normalizes_component) x) l
  change QuotientGroup.mk' (pCore 2 L) y = QuotientGroup.mk' (pCore 2 L) l at he
  have hh : y * l⁻¹ ∈ pCore 2 L :=
    (QuotientGroup.eq_one_iff (N := pCore 2 L) _).mp (by
      change QuotientGroup.mk' (pCore 2 L) (y * l⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel])
  exact ⟨y*l⁻¹,hh,rfl⟩

/-- The two-elements in the quotient-action kernel lie in O₂(LT). Only the original Sylow intersection is needed here. -/
theorem sylow_inf_quotient_kernel_le_core :
    (T : Subgroup G) ⊓ ((quotientAction D S m a).ker.map
      (L ⊔ (T : Subgroup G)).subtype) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let M := L ⊔ (T : Subgroup G)
  let B := (quotientAction D S m a).ker.map M.subtype
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
    exact (inferInstance : (quotientAction D S m a).ker.Normal).conj_mem y hy ⟨x,hx⟩
  apply le_pCoreIn_of_normalizes (T.isPGroup'.to_le (show A ≤ T from inf_le_left))
    (show A ≤ M from inf_le_left.trans le_sup_right)
  apply sup_le
  · apply le_normalizer_iff.mpr
    intro l hl r hr
    refine ⟨?_, (hMB (mem_sup_left hl) r).mp hr.2⟩
    have hc : ⁅l,r⁆ ∈ M.pCoreIn 2 := by
      obtain ⟨x,hx,rfl⟩ := hr.2
      have h := quotientAction_kernel_commutator D S m a x hx ⟨l,hl⟩
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

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
