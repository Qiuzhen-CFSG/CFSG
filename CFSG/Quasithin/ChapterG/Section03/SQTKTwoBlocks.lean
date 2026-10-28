module

public import CFSG.Quasithin.ChapterG.Section03.SQTKSpanningBlocks
import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
import Theory.SpecificGroups.Classical.BinaryLinearThreeRank
import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The dimension of an actual G.3 block with a companion

A binary block of dimension at least four has three-rank at least two.
Its literal C-component lift is then normal in the original SQTK group.
Surjectivity makes the block normal in the actual image actor, contradicting
its conjugacy with a distinct independent block. Thus every block in a
family of two or more blocks has dimension three.

Source: Aschbacher--Smith 1.2.1 and 12.7.16, printed pp.504 and844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
universe u
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H : Type u} [Group H] [Finite H]

private theorem block_rank_two {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (hn : 4 ≤ Module.finrank (ZMod 2) W) :
    2 ≤ primeRank 3 (BinaryLinear.GL W) := by
  let n := Module.finrank (ZMod 2) W
  let e : W ≃ₗ[ZMod 2] OuterCyclic.Space n := LinearEquiv.ofFinrankEq _ _ (by
    simp only [OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin]
    rfl)
  let E := (SmallParabolicLevi.linearGroupCongr e).trans (OuterCyclic.slEquivLinear n).symm
  rw [primeRank_equiv 3 E]
  exact Theory.SpecificGroups.Classical.BinaryLinearThreeRank.two_le_primeRank hn

private theorem rank_two_lifts {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hr : 2 ≤ primeRank 3 B) :
    2 ≤ primeRank 3 A := by
  by_contra hn
  let P : Sylow 3 A := Classical.choice inferInstance
  have hc := P.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (show primeRank 3 A ≤ 1 by omega)
  have hB := P.primeRank_le_one_of_surjective hc f hf
  omega

/-- A companion block forces the literal full linear action to have degree three. -/
theorem sqtk_spanning_block_dimension_three
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (Q : Subgroup (BinaryLinear.GL V)) (q : H →* Q) (hq : Function.Surjective q)
    (x : V) (hf : FullAction Q (MulAction.orbit Q x))
    (hd : Decomposition Q (MulAction.orbit Q x))
    (hl : LocalStructure Q (MulAction.orbit Q x))
    (hspan : Submodule.span (ZMod 2) (MulAction.orbit Q x) = ⊤)
    (i j : OrbitBlock Q (MulAction.orbit Q x)) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (blockSpace Q (MulAction.orbit Q x) i) = 3 := by
  let Δ := MulAction.orbit Q x
  let B := blockGroup Q Δ i
  let D := blockGroup Q Δ j
  have hBQ : B ≤ Q := generated_le Q i.val
  have hDQ : D ≤ Q := generated_le Q j.val
  obtain ⟨e,_,_,_⟩ := spanning_block_models hf hd hspan
  obtain ⟨⟨hlow,_⟩,C,hC,hCq⟩ := sqtk_spanning_block_lifts hH Q q hq x hf hd hl hspan i
  by_contra hdim
  have hr : 2 ≤ primeRank 3 B := by
    rw [primeRank_equiv 3 (e i)]
    exact block_rank_two (by omega)
  have hrC : 2 ≤ primeRank 3 C := by
    apply rank_two_lifts (q.subgroupMap C) (q.subgroupMap_surjective C)
    rw [hCq,primeRank_equiv 3 (subgroupOfEquivOfLe hBQ)]
    exact hr
  let : C.Normal := Chapter1.Section02.rank_two_component_normal hH hC hrC
  have hnormal : (B.subgroupOf Q).Normal := by
    rw [←hCq]
    exact Subgroup.Normal.map inferInstance q hq
  obtain ⟨g,hg,he⟩ := hd.groups_conjugate i j
  have hBD : B = D := by
    have hm : B.map (MulAut.conj g).toMonoidHom = B := by
      apply le_antisymm
      · rintro y ⟨b,hb,rfl⟩
        exact hnormal.conj_mem (⟨b,hBQ hb⟩ : Q) hb (⟨g,hg⟩ : Q)
      · intro b hb
        have hmem : g⁻¹*b*g ∈ B :=
          hnormal.conj_mem (⟨b,hBQ hb⟩ : Q) hb (⟨g,hg⟩ : Q)⁻¹
        refine ⟨g⁻¹*b*g,hmem,?_⟩
        simp [mul_assoc]
    exact hm.symm.trans he
  have hdis := hd.group_independent.pairwiseDisjoint hij
  change Disjoint B D at hdis
  rw [←hBD] at hdis
  have hbot : B = ⊥ := disjoint_self.mp hdis
  have hr0 : primeRank 3 B ≤ 1 := by
    have hh := primeRank_le_card (G := B) 3
    simpa only [hbot,card_bot] using hh
  omega

end CFSG.Quasithin.ChapterG.Section03
