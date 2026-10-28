module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.ParabolicConstruction
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs

/-!
# A minimal parabolic detects inner action in binary five-space

A solvable Sylow overgroup with three-part nine is a flag deleting two
nonadjacent nodes. Its intrinsic core quotient has order 36, and its core
lies in each minimal parabolic at either deleted node. An automorphism
whose displacements lie in one such minimal parabolic preserves it.
The graph-automorphism theorem rules out such preservation in dimension
five, so this automorphism is inner.

Source: Aschbacher–Smith, 15.3.24, printed pp.1129–1130 of refs/quasithin.pdf;
the flag-action calculation is the same as in 13.8.25, pp.959–960.
-/

@[expose] public section
open Subgroup BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
open BinaryLinear.SmallParabolicLevi.TwoNodes BinaryLinear.InvariantNodeActions
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective

theorem inner_of_minimal_displacement (b : FiveBasis) (i : Fin 4)
    (a : MulAut (LinearGroup 5))
    (h : ∀ x ∈ minimalParabolic b i, a x * x⁻¹ ∈ minimalParabolic b i) :
    a ∈ MulAut.innerSubgroup _ := by
  have hp : (minimalParabolic b i).map a.toMonoidHom = minimalParabolic b i := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨y, hy, rfl⟩
      change a y ∈ minimalParabolic b i
      simpa only [inv_mul_cancel_right] using (minimalParabolic b i).mul_mem (h y hy) hy
    · rw [card_map_of_injective a.injective]
  by_contra ha
  have hm := outer_preserves_minimalParabolic_middle (by decide : 2 ≤ 4)
    (by decide : 4 ≤ 4) b i a ha hp
  omega

/-- The solvable base has an actual two-node flag marking and intrinsic core quotient of order 36. -/
theorem solvable_base_marking (T : Sylow 2 (LinearGroup 5))
    (B : Subgroup (LinearGroup 5)) (hTB : (T : Subgroup _) ≤ B)
    (hs : Group.IsSolvable B) (h3 : (Nat.card B).factorization 3 = 2) :
    ∃ (b : FiveBasis) (i j : Fin 4), i ≠ j ∧
      (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      (T : Subgroup (LinearGroup 5)) = flagStabilizer b Set.univ ∧
      B = flagStabilizer b ({i,j} : Set (Fin 4))ᶜ ∧
      Nat.card (B ⧸ pCore 2 B) = 36 ∧
      minimalParabolic b i ≤ B ∧ B.pCoreIn 2 ≤ minimalParabolic b i := by
  obtain ⟨b, hb⟩ := BinaryLinear.FiveFlagGeometry.sylow_eq_flagStabilizer T
  obtain ⟨cuts, hc⟩ := overgroup_eq_flag b B (hb ▸ hTB)
  obtain ⟨i, j, hij, hgap, he⟩ := cuts_eq_compl_pair_of_solvable_three_part b cuts
    (hc ▸ hs) (hc ▸ h3)
  have hB : B = flagStabilizer b ({i,j} : Set (Fin 4))ᶜ := hc.trans (congrArg _ he)
  have hp : minimalParabolic b i ≤ B := by
    rw [hB]
    exact flagStabilizer_antitone b (by intro k hk; exact fun hki => hk (Or.inl hki))
  refine ⟨b, i, j, hij, hgap, hb, hB, ?_, hp, ?_⟩
  · rw [hB]
    let e := (flagDiagonalQuotientEquiv b ({i,j} : Set (Fin 4))ᶜ).trans
      (pairFactorsEquiv i j hgap)
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  · let U : Sylow 2 B := T.subtype hTB
    have hU : (U : Subgroup B) = (T : Subgroup (LinearGroup 5)).subgroupOf B := rfl
    have hcore := map_mono (f := B.subtype) (pCore_isPGroup.le_sylow_of_normal U)
    change B.pCoreIn 2 ≤ (U : Subgroup B).map B.subtype at hcore
    rw [hU, map_subgroupOf_eq_of_le hTB, hb] at hcore
    exact hcore.trans (flagStabilizer_antitone b (Set.subset_univ _))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction
end
