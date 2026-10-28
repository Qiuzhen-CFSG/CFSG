module
public import Stellmacher.SectionTen.TenOneSmallResidualQuotientCard

/-!
# The actual residual four-quotient action

In the small Section Ten configuration, the residual-core quotient R/V is
an elementary four-group with its literal first-stabilizer conjugation
action. This producer retains the quotient normality and core-normalization
proofs, the exact action formula, the first core in the kernel, and an action
range with more than two elements. The invariant-subgroup dichotomy on a
four-element group therefore applies directly to its geometric subgroups.

The existing small-quotient results supply normality, elementarity, order,
and the core-kernel bound. If the action range had at most two elements,
it would be a two-group, forcing the first two-residual into the kernel.
The exact conjugation formula would then contradict its already proved
noncentral action on the residual core modulo V.

This supplies the irreducible residual-quotient input to the center
identification in Stellmacher (10.1)(a), Journal of Algebra 190 (1997),
printed p.60. No faithful or irreducible action is assumed.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_residual_quotient_action
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let Q := QAt ctx.Γ ctx.criticalPath.firstStep
    let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
    let V := VAt ctx.Γ ctx.criticalPath.firstStep
    ∃ hN : (V.subgroupOf R).Normal,
      let _ := hN
      ∃ hPR : P ≤ Subgroup.normalizer (R : Set G),
        IsElementaryAbelian 2 (R ⧸ V.subgroupOf R) ∧
        Nat.card (R ⧸ V.subgroupOf R) = 4 ∧
        ∃ action : P →* MulAut (R ⧸ V.subgroupOf R),
          (∀ actor : P, ∀ point : R,
            action actor (QuotientGroup.mk' (V.subgroupOf R) point) =
              QuotientGroup.mk' (V.subgroupOf R)
                ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
                  (Subgroup.mem_normalizer_iff.mp (hPR actor.property) point).mp point.property⟩) ∧
          Q.subgroupOf P ≤ action.ker ∧ 2 < Nat.card action.range := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  have hE : E = twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) :=
    stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
  have hVR : V ≤ R := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  obtain ⟨hN, helementary, hRQ⟩ := ten_one_small_residual_quotient_elementary
    ctx middle hpath hsmall hmodel
  let _ := hN
  let W := R ⧸ V.subgroupOf R
  have hWcard : Nat.card W = 4 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVR).toEquiv] at hcount
    have hRcard : Nat.card R = 32 := ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
    change Nat.card V = 8 at hsmall
    rw [hRcard, hsmall] at hcount
    change 32 = Nat.card W * 8 at hcount
    omega
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action P R V hPR hPV hN
  have hQkernel : Q.subgroupOf P ≤ action.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P R V Q hN hPR hRQ
      action haction
  have hlarge : 2 < Nat.card action.range := by
    by_contra! hbound
    have hpositive : 0 < Nat.card action.range := Nat.card_pos
    have hcases : Nat.card action.range = 1 ∨ Nat.card action.range = 2 := by omega
    have himageTwo : IsPGroup 2 action.range := by
      rcases hcases with hone | htwo
      · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa using hone)
      · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa using htwo)
    have hquot : IsPGroup 2 (P ⧸ action.ker) :=
      himageTwo.of_equiv (QuotientGroup.quotientKerEquivRange action).symm
    have hres : twoResidualSubgroup P ≤ action.ker := by
      rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
      exact BenderSuzuki.External.hktPResidual_le action.ker inferInstance hquot
    have hEK : E ≤ action.ker.map P.subtype := by
      rw [hE, twoResidualIn, twoResidualAmbient]
      exact Subgroup.map_mono hres
    apply ten_one_first_core_action_not_le_module ctx middle hpath
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro actor hactor vector hvector
    obtain ⟨a, ha, rfl⟩ := hEK hactor
    let vectorR : R := ⟨vector, hvector⟩
    have hfix : action a (QuotientGroup.mk' (V.subgroupOf R) vectorR) =
        QuotientGroup.mk' (V.subgroupOf R) vectorR := by
      rw [show action a = 1 from ha]
      rfl
    rw [haction] at hfix
    have hmem := QuotientGroup.eq_iff_div_mem.mp hfix
    change (a : G) * vector * (a : G)⁻¹ / vector ∈ V at hmem
    change ⁅(a : G), vector⁆ ∈ V
    simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
  exact ⟨hN, hPR, helementary, hWcard, action, haction, hQkernel, hlarge⟩
end Stellmacher.SectionTen

