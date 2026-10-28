module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual HS pair projected through its central cover

The source involution t acts faithfully on I and remains involutory after
quotienting by O₂(I) = Z(I). Restriction puts L in the fixed subgroup upstairs.
The central-kernel component theorem then puts its image in the full fixed
subgroup downstairs, without assuming surjectivity on fixed points. An
alternating component is centerless, so its image retains the original
alternating-group isomorphism. The quotient inherits simplicity and perfectness
from the source component; these are not separate model assumptions.

These results isolate the actual embedded A₆ or A₈ on which the two intrinsic
HS fixer calculations must operate. They do not assert either fixer bound.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.7(3h)
and 16.3.5, printed pp.1172–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims
open Subgroup Theory.GroupTheory PerfectCentralCovering
universe u v
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}
variable {S : Type v} [Group S]

/-- The actual embedded component in the specified quotient model. -/
def projected (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* S) : Subgroup S :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- The source involution acting on the actual covering component. -/
def coverInvolution (h : PairContext E L I t i) : MulAut I :=
  inducedAction E I h.normalizes ⟨t, h.t_mem⟩

/-- The actual source involution descended through the cover. -/
noncomputable def quotientInvolution (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : MulAut S :=
  (h.coreCover hG e).autMap (h.coreCover_kernel hG e) (coverInvolution h)

theorem quotientInvolution_order (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    orderOf (quotientInvolution h hG e) = 2 := by
  rw [quotientInvolution,
    orderOf_injective _ ((h.coreCover hG e).autMap_injective (h.coreCover_kernel hG e)),
    coverInvolution, orderOf_injective _ h.faithful,
    ← orderOf_injective E.subtype E.subtype_injective]
  exact h.setup.involution_t

omit [Finite G] in
/-- The smaller component is a component of the actual fixed subgroup upstairs. -/
theorem component_cover_fixed (h : PairContext E L I t i) :
    IsComponentIn (L.subgroupOf I) (coverInvolution h).fixedSubgroup := by
  have hLC : L ≤ I ⊓ involutionCentralizer t := le_inf h.proper.le h.setup.component.1
  have hcomp := (show IsComponentIn L (involutionCentralizer t) from
    h.setup.component).restrict hLC inf_le_right
  let e := I.normalizerFixedEquivCentralizer ⟨t, h.normalizes h.t_mem⟩
  have he : (L.subgroupOf (I ⊓ involutionCentralizer t)).map e.symm.toMonoidHom =
      (L.subgroupOf I).subgroupOf (coverInvolution h).fixedSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  refine ⟨?_, he ▸ hcomp.2.map_equiv e.symm⟩
  intro x hx
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  apply Subtype.ext
  change t * (x : G) * t⁻¹ = (x : G)
  have hc : (x : G) * t = t * (x : G) :=
    mem_centralizer_singleton_iff.mp (h.setup.component.1 hx)
  rw [← hc]
  exact mul_inv_cancel_right _ _

/-- A central quotient is injective on the centerless alternating component. -/
theorem projected_equiv (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* S) {n : ℕ} (hn : 4 ≤ n)
    (eL : L ≃* alternatingGroup (Fin n)) :
    Nonempty (projected h hG e ≃* alternatingGroup (Fin n)) := by
  let f := h.coreCover hG e
  let j : L →* S := f.toMonoidHom.comp (inclusion h.proper.le)
  have hj : Function.Injective j := by
    apply j.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hxI : (⟨(x : G), h.proper.le x.property⟩ : I) ∈ center I :=
      f.ker_le_center hx
    have hxL : x ∈ center L := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun z : I => (z : G)) (mem_center_iff.mp hxI
        ⟨(y : G), h.proper.le y.property⟩)
    have hz : eL x ∈ center (alternatingGroup (Fin n)) :=
      (centerCongr eL ⟨x, hxL⟩).property
    rw [alternatingGroup.center_eq_bot (by simpa using hn), mem_bot] at hz
    exact mem_bot.mpr (eL.injective (hz.trans (map_one eL).symm))
  have hr : j.range = projected h hG e := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨(x : G), h.proper.le x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), hx⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hr.symm).trans
    ((MonoidHom.ofInjective hj).symm.trans eL)⟩

/-- The projected subgroup stays a component of the full quotient fixed subgroup. -/
theorem component_quotient_fixed (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S)
    (hne : projected h hG e ≠ ⊥) :
    IsComponentIn (projected h hG e) (quotientInvolution h hG e).fixedSubgroup := by
  exact (component_cover_fixed h).map_fixed_of_central_ker
    (coverInvolution h) (quotientInvolution h hG e) (h.coreCover hG e).toMonoidHom
    (h.coreCover hG e).surjective (h.coreCover hG e).ker_le_center
    (fun x => ((h.coreCover hG e).autMap_apply (h.coreCover_kernel hG e)
      (coverInvolution h) x).symm) hne

/-- Source quasisimplicity and E1 supply simplicity of the actual quotient model. -/
theorem quotient_simple (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : IsSimpleGroup S := by
  let := h.component.quasisimple
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)).trans e).symm.isSimpleGroup

/-- The model also inherits perfectness from the source component. -/
theorem quotient_perfect (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : Group.IsPerfect S := by
  let := h.component.quasisimple
  exact Group.IsPerfect.ofSurjective (f := (h.coreCover hG e).toMonoidHom)
    (h.coreCover hG e).surjective

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.HigmanSims
