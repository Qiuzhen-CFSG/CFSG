module

public import Theory.Representation.RankThreeAbelianAutomizer

/-!
# Abelian automizers in special linear groups

The faithful natural SL representation extends to an algebraic closure
without changing its dimension. The existing character-weight automizer
theorem therefore embeds the automizer of a cross-characteristic abelian
subgroup into the symmetric group of the degree.

Source: Aschbacher–Smith, A.3.21(c), printed pp.55–56.
-/

namespace Representation
open scoped MatrixGroups

/-- The automizer bound for the genuine special linear matrix group. -/
public theorem specialLinear_abelian_automizer_embeds_perm
    {F : Type*} [Field F] (n : ℕ) (A : Subgroup SL(n, F))
    [IsMulCommutative A] (horder : (Nat.card A : F) ≠ 0) :
    ∃ j : A.normalizerMonoidHom.range →* Equiv.Perm (Fin n),
      Function.Injective j := by
  let E := AlgebraicClosure F
  let rho := (specialLinearNatural (k := F) n).extendScalars E
  have hrho : Function.Injective rho :=
    (extendScalars_faithful_iff E _).mp (specialLinearNatural_injective n)
  have horder' : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply automizer_embeds_perm_of_abelian rho A hrho horder' n
  simp only [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin, le_refl]

end Representation
