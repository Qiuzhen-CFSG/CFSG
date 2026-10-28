module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.Local
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SectionCentralizers
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# From conjugation to the genuine component section kernel

A two-perfect group acts innerly whenever the actual outer automorphism
group is a two-group: its conjugation homomorphism has trivial image in
Aut(L)/Inn(L). We construct the conjugation action from the ambient normalizer
and return a witness in the published kernel on L/O₂(L).

This is the final elementary step of the PSL₃(2) branch in the rank-one
paragraph of Aschbacher--Smith 15.3.37, printed p.1135. The model's outer-group
calculation is an explicit input, not inferred from an unrelated action.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] {Y L : Subgroup G}

theorem inner_witness_of_conjugation_inner {y : G}
    (hy : y ∈ normalizer (L : Set G))
    (ha : L.normalizerMonoidHom ⟨y, hy⟩ ∈ MulAut.innerSubgroup L) :
    ∃ l ∈ L, l⁻¹ * y ∈ Chapter4.sectionCentralizer L := by
  obtain ⟨l, hl⟩ := ha
  have hc : l.val⁻¹ * y ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have he := congrArg (fun a : MulAut L => (a ⟨x, hx⟩ : G)) hl
    change l.val * x * l.val⁻¹ = y * x * y⁻¹ at he
    calc
      x * (l.val⁻¹ * y) = l.val⁻¹ * (l.val * x * l.val⁻¹) * y := by group
      _ = l.val⁻¹ * (y * x * y⁻¹) * y := by rw [he]
      _ = (l.val⁻¹ * y) * x := by group
  refine ⟨l, l.property, ?_⟩
  have hle : centralizer (L : Set G) ≤ Chapter4.sectionCentralizer L := by
    apply le_commutatorPreimage (Subgroup.centralizer_le_normalizer _)
    exact (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le.trans bot_le
  exact hle hc

theorem inner_of_twoPerfect_of_outer_twoGroup
    (hn : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y)
    (ho : IsPGroup 2 (MulAut.Outer L)) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Y L := by
  let a : Y →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let f : Y →* MulAut.Outer L := (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp a
  have hf : f = 1 := hp.hom_eq_one_of_isPGroup ho f
  intro y hy
  apply inner_witness_of_conjugation_inner (hn hy)
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hf ⟨y, hy⟩

variable [Finite G] {Yplus S M I : Subgroup G}

theorem Setup.inner_of_outer_twoGroup (h : Setup Yplus S M I L)
    (ho : IsPGroup 2 (MulAut.Outer L)) :
    ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L :=
  inner_of_twoPerfect_of_outer_twoGroup (le_sup_left.trans h.normalizes_component)
    (h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) ho

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
