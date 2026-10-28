module

public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Basic
public import Theory.GroupAction.PointwiseFixerResidual
public import Theory.GroupAction.FixedResidualFixerTransport
public import Theory.SpecificGroups.Alternating.CommutingFourSixObstruction

/-!
# The model automorphism inputs for the terminal subgroup

This module connects the pointwise fixer of the marked A₄ in a recognized
model to the literal action of M₁ on H = O²(C_G(E)). The two intrinsic
model facts remain explicit: the fixer is a two-group for A₆ and trivial
for PSL₃(2). The first gives residual centralization and the actual
quasithin contradiction; the second gives full M₁-centralization.

The model facts must be proved separately, and the dihedral recognition
must construct the isomorphism. Source: Aschbacher–Smith, proof of 13.9.1,
printed p.974 (PDF p.991).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup

open Subgroup

variable {G : Type*} [Group G]

/-- The source's residual action restriction from the precise model fixer. -/
theorem residual_centralizes_of_model_fixer
    {X : Type*} [Group X] (E M₁ M₂ : Subgroup G)
    (hE : E = M₁.pCoreIn 2)
    (hcomm : M₁ ≤ centralizer (residual M₂ : Set G))
    (eH : terminal E ≃* X)
    (hfix : IsPGroup 2 (fixingSubgroup (MulAut X)
      ((residual M₂).subgroupOf (terminal E) |>.map eH.toMonoidHom : Set X))) :
    residual M₁ ≤ centralizer (terminal E : Set G) := by
  apply embedded_pResidual_le_centralizer_of_isPGroup_fixer 2 M₁ (terminal E)
    (residual M₂) (normalizes_terminal_of_core E M₁ hE) hcomm
  exact hfix.of_equiv
    (MulAut.fixerEquivMap eH ((residual M₂).subgroupOf (terminal E))).symm

/-- The PSL₃(2) model fixer gives centralization of all of M₁. -/
theorem centralizes_of_model_fixer_eq_bot
    {X : Type*} [Group X] (E M₁ M₂ : Subgroup G)
    (hE : E = M₁.pCoreIn 2)
    (hcomm : M₁ ≤ centralizer (residual M₂ : Set G))
    (eH : terminal E ≃* X)
    (hfix : fixingSubgroup (MulAut X)
      ((residual M₂).subgroupOf (terminal E) |>.map eH.toMonoidHom : Set X) = ⊥) :
    M₁ ≤ centralizer (terminal E : Set G) := by
  apply le_centralizer_of_fixer_eq_bot M₁ (terminal E) (residual M₂)
    (normalizes_terminal_of_core E M₁ hE) hcomm
  apply eq_bot_iff.mpr
  intro a ha
  have hh := mem_map_of_mem (MulAut.congr eH).toMonoidHom ha
  rw [MulAut.map_fixer, hfix] at hh
  apply (MulAut.congr eH).injective
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_one, mem_bot] using hh

/-- In the A₆ case, the model fixer and the earlier A₄ factor produce the
rank-three contradiction. No centralization conclusion is assumed. -/
theorem false_of_alternating_six_model_fixer [Finite G]
    (hG : IsQuasithin G) (E M₁ M₂ : Subgroup G)
    (hE : E = M₁.pCoreIn 2)
    (hcomm : M₁ ≤ centralizer (residual M₂ : Set G))
    (e₁ : residual M₁ ≃* alternatingGroup (Fin 4))
    (eH : terminal E ≃* alternatingGroup (Fin 6))
    (hfix : IsPGroup 2 (fixingSubgroup (MulAut (alternatingGroup (Fin 6)))
      ((residual M₂).subgroupOf (terminal E) |>.map eH.toMonoidHom :
        Set (alternatingGroup (Fin 6))))) : False :=
  Theory.Quasithin.not_quasithin_of_commuting_a4_a6 (residual M₁) (terminal E)
    e₁ eH (residual_centralizes_of_model_fixer E M₁ M₂ hE hcomm eH hfix) hG

end CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup
