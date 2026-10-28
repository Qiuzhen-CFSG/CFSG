module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Contracts
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Rank
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The square-automorphism rank input to G.9.3

The general finite-group theorem supplies the exact square-automorphism contract.
Combining it with the existing faithful action on the component product bounds
the original actor without requiring it to preserve the individual factors.
Only the separate model-specific bound on the factor's automorphism rank remains
an input to the actor corollary.

Source: Aschbacher--Smith, G.9.3, printed p.356 (PDF p.367).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents

universe u v

/-- The generic square-automorphism input, with all its premises discharged
under the precise centerless-quasisimple contract. -/
theorem FactorReduction.square_automorphism_rank_theorem :
    FactorReduction.SquareAutomorphismRankTheorem.{u} := by
  intro S _ _ _ hZ hr
  exact Theory.GroupTheory.AutomorphismSquare.rank_bound hZ hr

/-- The original actor has the required rank bound after the factor's own
model-specific automorphism-rank comparison. The square estimate is proved. -/
theorem actor_rank_bound_of_factor_automorphism_rank
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
    {A L L₂ H : Subgroup G} {m : ℕ}
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : Theory.GroupTheory.IsComponent G L₂)
    (hH : H = L ⊔ L₂) (hne : L ≠ L₂) (e : L ≃* L₂)
    (hZ : Subgroup.center L = ⊥) (hpos : 0 < primeRank 2 L)
    (hfactor : primeRank 2 (MulAut L) ≤ primeRank 2 L) :
    m ≤ 2 * primeRank 2 L := by
  let : Theory.GroupTheory.IsQuasisimple L := h.component.2
  have hinner := Theory.GroupTheory.primeRank_le_of_injective 2 MulAut.conj
    (MulAut.conj_injective_of_center_eq_bot hZ)
  exact actor_rank_bound_of_square_bound h hL₂ hH hne e hZ
    (FactorReduction.square_automorphism_rank_theorem L hZ (lt_of_lt_of_le hpos hinner))
    hfactor

end CFSG.Quasithin.ChapterG.Section09.TwoComponents
