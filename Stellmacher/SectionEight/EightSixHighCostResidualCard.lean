module
public import Stellmacher.SectionEight.EightSixSelectedCoatomCostSquare
public import Stellmacher.SectionEight.EightSixSelectedUniformCost
public import Stellmacher.SectionEight.EightSixSelectedCoatomDisplacementBound
/-!
# Exact residual order in the high-cost branch

For the actual selected large-index local configuration, suppose every
outside A actor has original cost at least eight. Then the selected cost
is sixteen and Y=[Qnext,O²(E)] has order 512. The entire selected telescope
and Q=O₂(L) are retained; no group model or provisional numerical premise
is assumed.

The coatom cardinality and large-index condition provide b in A0 outside
Qnext. The actual V2 restriction bound gives its displacement at most
sixteen. Central-coatom square-power counting gives its cost 2^(2*n), and
the high-cost lower bound forces exactly sixteen. The proved uniform-cost
identity transfers this value to the selected minimum. Finally the actual
residual-square formula gives |Y|=2*16²=512.

This proves Stellmacher (8.6), assertion (17), printed pp.44–45 of
`refs/files/stellmacher-n-group.pdf`. The full-core equality, extraspecial
recognition and subsequent quotient classification remain separate results.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_high_cost_residual_card
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover):
    eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 16 ∧
      Nat.card (⁅QAt ctx.Γ ctx.criticalPath.firstStep,twoResidualIn E⁆ : Subgroup G) = 512 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  have hA0A : A0 ≤ A := geom.coatom_eq ▸ inf_le_left
  have hAprevious : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
  have hA0not : ¬ A0 ≤ QAt Γ cp.firstStep := by
    intro hA0R
    have hA0D : A0 ≤ A ⊓ D := le_inf hA0A (hD ▸ le_inf (hA0A.trans hAprevious) hA0R)
    have hbound := Subgroup.card_le_of_le hA0D
    have hcount : Nat.card A = 2 * Nat.card A0 := geom.coatom_card
    have hpos : 0 < Nat.card A0 := Nat.card_pos
    change 4 * Nat.card (A ⊓ D : Subgroup G) ≤ Nat.card A at hlarge
    omega
  obtain ⟨b,hb,hbout⟩ := SetLike.not_le_iff_exists.mp hA0not
  have hselected := eight_six_selected_fixed_core_containment ctx hcenter hquot hlength
    hcard previous D L Q hprev hD hL hQ data E A0 actor geom hcore hedge ha hout hlarge hmin
  have htransfer := (eight_six_selected_cost_residual_transfer ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL hselected.1 b (hA0A hb)).1
  have hupper : eightSixCommutatorCost ctx.Γ ctx.criticalPath b ≤ 16 := by
    rw [htransfer]
    exact eight_six_selected_coatom_displacement_le_sixteen ctx hcenter hquot hlength hcard
      previous D L Q hprev data E A0 actor geom hcore hedge hD hL hhigh hlarge hselected.2 b hb
  have hlower := hhigh b (hA0A hb) hbout
  obtain ⟨n,hn⟩ := eight_six_selected_coatom_cost_square ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ b hb
  have hnlow : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hn <;> omega
  have hnupper : n ≤ 2 := by
    by_contra h
    have hle : 2 ^ (2 * 3) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hle
    omega
  have hntwo : n = 2 := by omega
  have hbsixteen : eightSixCommutatorCost ctx.Γ ctx.criticalPath b = 16 := by
    simpa only [hntwo, show 2 ^ (2 * 2) = (16 : ℕ) from rfl] using hn
  have hsame := eight_six_selected_all_actor_costs ctx hcenter hquot hlength hcard
    previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ
    b (hA0A hb) hbout
  have hactor : eightSixCommutatorCost ctx.Γ ctx.criticalPath actor = 16 :=
    hsame.symm.trans hbsixteen
  refine ⟨hactor,?_⟩
  have hc := eight_six_selected_residual_card_eq_twice_cost_square ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore hedge hD hL ha hout hlarge hmin hQ
  rw [hactor] at hc
  norm_num at hc
  exact hc
end Stellmacher.SectionEight
