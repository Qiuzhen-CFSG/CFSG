module

public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenCentralizers

/-!
# Centralizer bounds for the doubled A₇ action

At a maximal escaping subspace satisfying the original O^{2′} condition,
E.6.11 gives a faithful cyclic actor of order 2ⁿ − 1. For n = 2 or 3,
the odd-prime displacement bound excludes it. For n = 4 or 5, the full
seven-letter automizer excludes orders 15 and 31. Residual monotonicity
therefore controls every such subspace of corank below six.

At a minimum with corank below four, the involution parameter m = 4
supplies the O^{2′} condition. Together with the earlier hyperplane result,
this gives r ≥ 4 directly for this row. The two-group-image branch of
E.6.27 and the mixed-centralizer geometry of 7.5.5 remain separate source
obligations; this file does not infer r ≥ 6 from these inputs alone.
Source: Aschbacher–Smith E.6.4, E.6.11 and E.6.23; 7.5.5, p.701.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterE.Section06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M W U : Subgroup G}

private theorem cyclic_codim_le_corank [IsElementaryAbelian 2 W]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hU : U ≠ ⊥) (hUW : U ≤ W) {x : Automizer W}
    (hx : x ∈ inducedAutomizer W (M ⊓ centralizer (U : Set G))) :
    fixedCodim (automizerRepresentation W) (zpowers x) ≤ subgroupCorank W U := by
  apply (fixedCodim_mono (automizerRepresentation W) (zpowers_le.mpr hx)).trans
  rw [fixedCodim_inducedAutomizer W _ (h.localCentralizer_le_normalizer hU hUW)]
  exact subgroupCorank_antitone (le_inf hUW (le_centralizer_iff.mpr inf_le_right))

/-- The original O^{2′} condition is enough to control every centralizer
below corank six. Enlarge within Γ, then exclude its cyclic source actor. -/
theorem doubledSeven_small_oddCentralizer [IsElementaryAbelian 2 W]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (e : Automizer W ≃* Equiv.Perm (Fin 7)) (hr : 1 < globalR W)
    (hodd : ∀ x : Automizer W, (orderOf x).Prime → orderOf x ≠ 2 →
      4 ≤ fixedCodim (automizerRepresentation W) (zpowers x))
    (hU : U ≠ ⊥) (hUW : U ≤ W) (hcor : subgroupCorank W U < 6)
    (hres : oddCentralizerCondition M W U) : centralizer (U : Set G) ≤ M := by
  by_contra he
  obtain ⟨Y,hUY,hYW,hY,hmax⟩ := exists_maximal_escape hUW he
  have hYne : Y ≠ ⊥ := fun hb => hU (le_bot_iff.mp (hb ▸ hUY))
  have hΓ : Y ∈ obstructionFamily M W :=
    ⟨hYW,hYne,hY,InvariantSubspaces.oddCentralizerCondition_mono hUY hres⟩
  have hmin : globalR W ≤ (subgroupCorank W Y : ℕ∞) :=
    globalR_le_corank hYW (fun hh => hY (hh.trans h.normalizer_le))
  have hlo : 1 < subgroupCorank W Y := by exact_mod_cast hr.trans_le hmin
  have hhi := (subgroupCorank_antitone hUY).trans_lt hcor
  obtain ⟨x,hx,horder⟩ := doubledSeven_maximal_cyclic_action h hΓ hmax hlo
  by_cases hsmall : subgroupCorank W Y < 4
  · have hcases : subgroupCorank W Y = 2 ∨ subgroupCorank W Y = 3 := by omega
    have hp : (orderOf x).Prime := by
      rw [horder]
      rcases hcases with hc | hc <;> rw [hc] <;> norm_num
    have hne : orderOf x ≠ 2 := by
      rw [horder]
      rcases hcases with hc | hc <;> rw [hc] <;> norm_num
    have hb := (hodd x hp hne).trans (cyclic_codim_le_corank h hYne hYW hx)
    omega
  · have hx' : orderOf (e x) = 2 ^ subgroupCorank W Y - 1 :=
      (orderOf_injective e.toMonoidHom e.injective x).trans horder
    have hcases : subgroupCorank W Y = 4 ∨ subgroupCorank W Y = 5 := by omega
    rcases hcases with hc | hc
    · rw [hc] at hx'
      exact doubledSeven_no_fifteen (e x) hx'
    · rw [hc] at hx'
      exact doubledSeven_no_thirtyOne (e x) hx'

/-- The initial doubled-A₇ bound follows from the row's odd-prime
displacements and the source hyperplane bound, on the full minimum of r. -/
theorem doubledSeven_four_le_globalR [IsElementaryAbelian 2 W]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hm : localM W = 4) (hr : 1 < globalR W)
    (hodd : ∀ x : Automizer W, (orderOf x).Prime → orderOf x ≠ 2 →
      4 ≤ fixedCodim (automizerRepresentation W) (zpowers x)) :
    4 ≤ globalR W := by
  by_contra hn
  have hs : globalR W < (localM W : ℕ∞) := by simpa [hm] using lt_of_not_ge hn
  obtain ⟨U,hU,hmin⟩ := h.exists_minimal_obstruction hs
  have hlo : 1 < subgroupCorank W U := by
    exact_mod_cast (show (1 : ℕ∞) < (subgroupCorank W U : ℕ∞) from by rwa [hmin])
  have hhi : subgroupCorank W U < 4 := by
    have h' : (subgroupCorank W U : ℕ∞) < 4 := by
      rw [hmin]
      exact lt_of_not_ge hn
    exact_mod_cast h'
  obtain ⟨x,hx,ho⟩ := doubledSeven_minimum_cyclic_action h hU hmin hlo
  have hcases : subgroupCorank W U = 2 ∨ subgroupCorank W U = 3 := by omega
  have hp : (orderOf x).Prime := by
    rw [ho]
    rcases hcases with hc | hc <;> rw [hc] <;> norm_num
  have hne : orderOf x ≠ 2 := by
    rw [ho]
    rcases hcases with hc | hc <;> rw [hc] <;> norm_num
  have hb := (hodd x hp hne).trans (cyclic_codim_le_corank h hU.2.1 hU.1 hx)
  omega
end CFSG.Quasithin.Chapter7.NormalizedSource
