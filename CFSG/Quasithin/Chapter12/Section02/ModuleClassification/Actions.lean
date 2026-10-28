module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Source
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# The two literal acting quotients of a chosen Section 12.2 module

The action on the original Irr⁺ subspace factors through L/O₂(L). Its kernel
is exactly the relative centralizer C_L(V), so quotienting by that centralizer
provides the faithful actor required in 12.2.2(3d,e). All projection formulas
use the original conjugation action, without changing the chosen module.

Source: Aschbacher--Smith, Theorem 12.2.2(3), printed p.795.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The action of the literal quotient by the original component two-core. -/
def quotientAction : Representation (ZMod 2) (L ⧸ pCore 2 L) D.space :=
  QuotientGroup.lift (pCore 2 L) D.chosenAction D.chosenAction_core

@[simp] theorem quotientAction_mk (l : L) :
    D.quotientAction (QuotientGroup.mk' (pCore 2 L) l) = D.chosenAction l := rfl

omit [Finite G] in
/-- The kernel on the chosen space is the actual relative centralizer. -/
theorem chosenAction_ker :
    D.chosenAction.ker = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨w, hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
    have he := congrArg (fun z : D.space => (z.val.toMul.val : G))
      (LinearMap.congr_fun (show D.chosenAction l = 1 from hl) w.toAdd)
    have hw' : (w.toAdd.val.toMul.val : G) = v :=
      (D.spaceEquiv_apply w.toAdd).symm.trans (congrArg Subtype.val hw)
    change (l : G) * (w.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
      (w.toAdd.val.toMul.val : G) at he
    rw [hw'] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hl
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
    have hv : (v.val.toMul.val : G) ∈ V :=
      D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ hv).symm

include D in
omit [Finite G] in
/-- Normality is relative to L, as required for L/C_L(V). -/
theorem actionCentralizer_normal : ((centralizer (V : Set G)).subgroupOf L).Normal :=
  D.chosenAction_ker ▸ D.chosenAction.normal_ker

/-- The faithful action of the literal relative-centralizer quotient. -/
def faithfulAction : letI := D.actionCentralizer_normal
    Representation (ZMod 2) (L ⧸ (centralizer (V : Set G)).subgroupOf L) D.space := by
  letI := D.actionCentralizer_normal
  exact QuotientGroup.lift _ D.chosenAction D.chosenAction_ker.ge

omit [Finite G] in
@[simp] theorem faithfulAction_mk (l : L) : letI := D.actionCentralizer_normal
    D.faithfulAction (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) =
      D.chosenAction l := rfl

omit [Finite G] in
/-- No kernel is introduced when passing to L/C_L(V). -/
theorem faithfulAction_injective : Function.Injective D.faithfulAction := by
  let := D.actionCentralizer_normal
  apply D.faithfulAction.ker_eq_bot_iff.mp
  apply bot_unique
  intro q hq
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) q
  exact (QuotientGroup.eq_one_iff l).mpr (D.chosenAction_ker.le hq)

omit [Finite G] in
/-- Trivial action on V remains trivial on its literal fixed-space quotient. -/
theorem actionCentralizer_le_centralAction_ker :
    (centralizer (V : Set G)).subgroupOf L ≤ D.chosenCentralAction.ker := by
  intro l hl
  have he : D.chosenAction l = 1 := D.chosenAction_ker.ge hl
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
    rw [he]
    rfl

/-- The action in the alternating rows: L/C_L(V) on V/C_V(L). -/
def faithfulCentralAction : letI := D.actionCentralizer_normal
    Representation (ZMod 2) (L ⧸ (centralizer (V : Set G)).subgroupOf L)
      D.chosenCentralQuotient := by
  letI := D.actionCentralizer_normal
  exact QuotientGroup.lift _ D.chosenCentralAction D.actionCentralizer_le_centralAction_ker

omit [Finite G] in
@[simp] theorem faithfulCentralAction_mk (l : L) : letI := D.actionCentralizer_normal
    D.faithfulCentralAction
      (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) =
      D.chosenCentralAction l := rfl

/-- The quotient by the two-core maps onto the faithful quotient, using the
original projection on every component element. -/
def coreToFaithful : letI := D.actionCentralizer_normal
    (L ⧸ pCore 2 L) →* (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
  letI := D.actionCentralizer_normal
  exact QuotientGroup.map _ _ (MonoidHom.id L)
    (D.chosenAction_core.trans D.chosenAction_ker.le)

@[simp] theorem coreToFaithful_mk (l : L) : letI := D.actionCentralizer_normal
    D.coreToFaithful (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l := rfl

/-- Both source quotients induce exactly the same original module action. -/
theorem faithfulAction_comp_coreToFaithful : letI := D.actionCentralizer_normal
    D.faithfulAction.comp D.coreToFaithful = D.quotientAction := by
  let := D.actionCentralizer_normal
  apply MonoidHom.ext
  intro q
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  rfl

/-- On the source's simple-quotient branches the two-core action is faithful. -/
theorem quotientAction_injective (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    Function.Injective D.quotientAction := by
  apply D.quotientAction.ker_eq_bot_iff.mp
  apply bot_unique
  intro q hq
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  apply (QuotientGroup.eq_one_iff l).mpr
  exact (D.centralizer_eq_core_of_simple hs).le (D.chosenAction_ker.le hq)

/-- The canonical comparison of the two acting quotients is onto. -/
theorem coreToFaithful_surjective : Function.Surjective D.coreToFaithful := by
  let := D.actionCentralizer_normal
  intro q
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) q
  exact ⟨QuotientGroup.mk' (pCore 2 L) l,rfl⟩

/-- In the simple-quotient branches the canonical quotient comparison is
an isomorphism, rather than an unrelated group marking. -/
def coreToFaithfulEquiv (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    letI := D.actionCentralizer_normal
    (L ⧸ pCore 2 L) ≃* (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
  letI := D.actionCentralizer_normal
  apply MulEquiv.ofBijective D.coreToFaithful
  refine ⟨?_,D.coreToFaithful_surjective⟩
  intro a b he
  apply D.quotientAction_injective hs
  have hh := congrArg D.faithfulAction he
  change (D.faithfulAction.comp D.coreToFaithful) a =
    (D.faithfulAction.comp D.coreToFaithful) b at hh
  rwa [D.faithfulAction_comp_coreToFaithful] at hh

@[simp] theorem coreToFaithfulEquiv_mk (hs : IsSimpleGroup (L ⧸ pCore 2 L)) (l : L) :
    letI := D.actionCentralizer_normal
    D.coreToFaithfulEquiv hs (QuotientGroup.mk' (pCore 2 L) l) =
      QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l := rfl

/-- A marking of the literal two-core action gives the ambient conjugation
model used by the Chapter 6 and Chapter 13 consumers. -/
theorem conjugationModel_of_quotientAction
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) A W} (e : ActionEquiv D.quotientAction σ) :
    Chapter6.Source.IsConjugationModel L V σ := by
  let f := D.spaceEquiv.symm.trans e.linearEquiv.toAddEquiv.toMultiplicative
  refine ⟨e.groupEquiv,f,?_⟩
  intro l v
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have he := e.intertwines (QuotientGroup.mk' (pCore 2 L) l) w
  change (D.spaceEquiv (Multiplicative.ofAdd
    (e.linearEquiv.symm (σ (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
      (e.linearEquiv w)))) : G) = _
  rw [← he,e.linearEquiv.symm_apply_apply,D.spaceEquiv_apply]
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg (fun z : V => (z : G)) (D.spaceEquiv.apply_symm_apply v))
  change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
  rw [hw]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
