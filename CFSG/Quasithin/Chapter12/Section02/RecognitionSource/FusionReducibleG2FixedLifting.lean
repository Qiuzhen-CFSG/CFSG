module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Model
public import Theory.Representation.G2NaturalExtensions.DerivedFixedSpaces

/-!
# Fixed lifting on the original chosen G₂ module

The natural quotient of a chosen module is a commutator-generated central
cover. The universal Weyl cover and its norm imply that an element fixing a
natural image fixes its original lift. We retain the actual actor L/O₂(L)
and identify this conclusion with centralization in the ambient group.
The last theorem uses the literal Weyl coordinates of the 12.4 source row.

Source: Aschbacher--Smith B.4.6(7), I.2.3 and 12.4.2, pp.88,413,812.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterB.QuasisimpleSource Atlas.G2.Natural

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

private theorem chosen_mem_centralizer_iff_quotient_fixed
    (D : ChosenModule T L V) (l : L) (v : V) :
    (v : G) ∈ centralizer ({(l : G)} : Set G) ↔
      D.quotientAction (QuotientGroup.mk' (pCore 2 L) l)
        (D.spaceEquiv.symm v).toAdd = (D.spaceEquiv.symm v).toAdd := by
  let w := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  rw [D.quotientAction_mk]
  constructor
  · intro hc
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
    rw [hw]
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp hc).symm
  · intro hc
    have hh := congrArg (fun u : D.space => (u.val.toMul.val : G)) hc
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _ at hh
    rw [hw] at hh
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A fixed point on the marked natural quotient lifts to a fixed vector on
the chosen module, without a full G₂ action or a fixed-space vanishing premise. -/
theorem g2_chosen_fixed_of_natural_fixed
    (D : ChosenModule T L V)
    (e : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype))
    (q : L ⧸ pCore 2 L) (v : D.space)
    (hv : derivedAction (ZMod 2) (e.groupEquiv q)
      (e.linearEquiv (Submodule.Quotient.mk v)) =
        e.linearEquiv (Submodule.Quotient.mk v)) :
    D.quotientAction q v = v := by
  have hf := Extensions.derived_fixed_of_natural_fixed
    (G2WeylModel.projection D e) (G2WeylModel.isCover D e)
    (e.groupEquiv q) v hv
  rwa [G2WeylModel.action_apply] at hf

/-- The natural quotient detects the literal centralizer of each original
component element on V, including its central fixed kernel. -/
theorem g2_chosen_mem_centralizer_iff_natural_fixed
    (D : ChosenModule T L V)
    (e : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype))
    (l : L) (v : V) :
    (v : G) ∈ centralizer ({(l : G)} : Set G) ↔
      derivedAction (ZMod 2)
        (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (e.linearEquiv (Submodule.Quotient.mk (D.spaceEquiv.symm v).toAdd)) =
      e.linearEquiv (Submodule.Quotient.mk (D.spaceEquiv.symm v).toAdd) := by
  rw [chosen_mem_centralizer_iff_quotient_fixed]
  constructor
  · intro hc
    have hh := (G2WeylModel.projection D e).isIntertwining
      (G2WeylModel.action D e) (OrthogonalCover.binaryNatural (ZMod 2))
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) (D.spaceEquiv.symm v).toAdd
    rw [G2WeylModel.action_apply, hc] at hh
    exact hh.symm
  · exact g2_chosen_fixed_of_natural_fixed D e _ _

/-- The same centralizer detector in the original 12.4 Weyl marking, with
its canonical natural projection and its derived actor unchanged. -/
theorem g2_weyl_chosen_mem_centralizer_iff_natural_fixed
    (D : ChosenModule T L V)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (l : L) (v : V) :
    (v : G) ∈ centralizer ({(l : G)} : Set G) ↔
      derivedAction (ZMod 2)
        (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (mk (ZMod 2) (e.linearEquiv (D.spaceEquiv.symm v).toAdd)) =
      mk (ZMod 2) (e.linearEquiv (D.spaceEquiv.symm v).toAdd) := by
  rw [chosen_mem_centralizer_iff_quotient_fixed]
  constructor
  · intro hc
    rw [derivedAction_apply, action_mk]
    change mk (ZMod 2) (OrthogonalCover.action (ZMod 2)
      (e.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
      (e.linearEquiv (D.spaceEquiv.symm v).toAdd)) = _
    rw [← e.intertwines, hc]
  · intro hv
    apply e.linearEquiv.injective
    rw [e.intertwines]
    exact Extensions.traceZero_fixed_of_natural_fixed _ _ hv

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
