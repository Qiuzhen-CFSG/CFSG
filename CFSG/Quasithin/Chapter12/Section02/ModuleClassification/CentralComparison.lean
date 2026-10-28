module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Comparison
/-!
# Transport of the original fixed quotient and recovery of its actor

The actual original projection has kernel C_L(V), so it identifies that
quotient with the B.5 component without any simplicity assumption. The
central-quotient equivalence intertwines the original two-core projection;
its pullback transfers irreducibility even before the projection is injective.
Source: Aschbacher--Smith B.5.1 and 12.2.2, printed pp.99--103 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)
include c

theorem centralEquiv_intertwines (s : MovedSection ρ K)
    (q : L ⧸ pCore 2 L) (v : s.space.toSubmodule ⧸ s.central.toSubmodule) :
    c.centralEquiv s ((MovedSection.action ρ s) (c.projection q) v) =
      D.centralQuotientAction q (c.centralEquiv s v) := by
  induction q using QuotientGroup.induction_on with
  | H l =>
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change c.centralEquiv s (Submodule.Quotient.mk
        (s.space.toRepresentation (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v)) = _
      rw [c.centralEquiv_mk,c.centralEquiv_mk]
      change Submodule.Quotient.mk (ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) v.val) =
        Submodule.Quotient.mk (D.chosenAction l v.val)
      exact congrArg Submodule.Quotient.mk
        (LinearMap.congr_fun (c.action (QuotientGroup.mk' (pCore 2 L) l)) v.val)



theorem centralAction_injective (s : MovedSection ρ K)
    (hf : Function.Injective ((MovedSection.action ρ s).comp K.subtype))
    (hp : Function.Injective c.projection) : Function.Injective D.centralQuotientAction := by
  intro a b hab
  apply hp
  apply hf
  apply LinearMap.ext
  intro v
  apply (c.centralEquiv s).injective
  change c.centralEquiv s ((MovedSection.action ρ s) (c.projection a) v) =
    c.centralEquiv s ((MovedSection.action ρ s) (c.projection b) v)
  exact (c.centralEquiv_intertwines s a v).trans
    ((LinearMap.congr_fun hab _).trans (c.centralEquiv_intertwines s b v).symm)

noncomputable def quotientMarking (s : MovedSection ρ K)
    (hp : Function.Injective c.projection) :
    ActionEquiv D.centralQuotientAction ((MovedSection.action ρ s).comp K.subtype) where
  groupEquiv := MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩
  linearEquiv := (c.centralEquiv s).symm
  intertwines q v := by
    apply (c.centralEquiv s).symm_apply_eq.mpr
    exact (congrArg (D.centralQuotientAction q)
      ((c.centralEquiv s).apply_symm_apply v)).symm.trans
      (c.centralEquiv_intertwines s q ((c.centralEquiv s).symm v)).symm

@[expose] noncomputable def originalProjection : L →* K :=
  c.projection.comp (QuotientGroup.mk' (pCore 2 L))

theorem originalProjection_ker : c.originalProjection.ker =
    (centralizer (V : Set G)).subgroupOf L := by
  rw [← D.chosenAction_ker]
  ext l
  change c.projection (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ D.chosenAction l = 1
  constructor
  · intro h
    have he := c.action (QuotientGroup.mk' (pCore 2 L) l)
    rw [h, OneMemClass.coe_one, map_one] at he
    exact he.symm
  · intro h
    apply c.faithful
    change ρ (c.projection (QuotientGroup.mk' (pCore 2 L) l)) = (ρ.comp K.subtype) 1
    rw [c.action, map_one]
    exact h

@[expose] noncomputable def faithfulEquiv : letI := D.actionCentralizer_normal
    (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* K := by
  let := D.actionCentralizer_normal
  exact (QuotientGroup.quotientMulEquivOfEq c.originalProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.originalProjection
      (c.surjective.comp (QuotientGroup.mk'_surjective _)))

@[simp] theorem faithfulEquiv_mk (l : L) : letI := D.actionCentralizer_normal
    c.faithfulEquiv (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) =
      c.projection (QuotientGroup.mk' (pCore 2 L) l) := rfl


noncomputable def wholeMarking (s : MovedSection ρ K)
    (hp : Function.Injective c.projection) :
    ActionEquiv D.quotientAction (s.space.toRepresentation.comp K.subtype) where
  groupEquiv := MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩
  linearEquiv := (c.spaceEquiv s).symm
  intertwines q v := by
    apply (c.spaceEquiv s).injective
    rw [LinearEquiv.apply_symm_apply]
    change D.quotientAction q v = ρ (c.projection q) ((c.spaceEquiv s).symm v).val
    rw [c.action]
    exact congrArg (D.quotientAction q) ((c.spaceEquiv s).apply_symm_apply v).symm

noncomputable def pulledCentralMarking (s : MovedSection ρ K) :
    ActionEquiv D.centralQuotientAction (((MovedSection.action ρ s).comp K.subtype).comp c.projection) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := (c.centralEquiv s).symm
  intertwines q v := by
    apply (c.centralEquiv s).symm_apply_eq.mpr
    exact (congrArg (D.centralQuotientAction q)
      ((c.centralEquiv s).apply_symm_apply v)).symm.trans
      (c.centralEquiv_intertwines s q ((c.centralEquiv s).symm v)).symm


end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
