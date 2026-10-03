module

public import Stellmacher.Recognition.LargeTerminalFourFixedLocalData
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The native action on the residual abelianization

The second local group normalizes the first residual. Its conjugation
therefore induces automorphisms of the literal quotient R/R′. We retain
an evaluation formula on representatives, so orbit arguments can be
transported back to conjugation in the ambient group.

Source: Thompson, N-groups VI, printed p.630, the action on the fifteen
nonidentity residual cosets.
-/

namespace Stellmacher.Recognition
open Subgroup
universe u

/-- Conjugation by the actual second local group on the residual quotient. -/
public noncomputable def LargeTerminalContext.residualQuotientAction
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ctx.second →* MulAut (ctx.firstResidual ⧸ commutator ctx.firstResidual) :=
  (quotientAut (commutator ctx.firstResidual)).comp
    (ctx.firstResidual.normalizerMonoidHom.comp
      (inclusion ctx.second_le_residual_normalizer))

/-- The quotient action sends a representative to its ambient conjugate. -/
public theorem LargeTerminalContext.residualQuotientAction_apply_mk
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (g : ctx.second) (r r' : ctx.firstResidual)
    (hr : (r' : G) = (MulAut.conj (g : G)) (r : G)) :
    ctx.residualQuotientAction g (QuotientGroup.mk' (commutator ctx.firstResidual) r) =
      QuotientGroup.mk' (commutator ctx.firstResidual) r' := by
  change quotientAut (commutator ctx.firstResidual)
    (ctx.firstResidual.normalizerMonoidHom
      ⟨(g : G), ctx.second_le_residual_normalizer g.property⟩)
    (QuotientGroup.mk' (commutator ctx.firstResidual) r) = _
  rw [quotientAut_apply_mk]
  congr 1
  exact Subtype.ext hr.symm

end Stellmacher.Recognition
