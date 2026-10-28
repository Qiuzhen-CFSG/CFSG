module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.FirstLocal
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizerTransfer
/-!
# The actor-preserving J₄ escape from an even block centralizer

The opposite block in the original paired configuration supplies an even
centralizer in the faithful component quotient. Its actual normalizer Sylow
therefore fixes an involution. The native J₄ placement puts both the block and
that Sylow inside a characteristic-two involution centralizer. In the first
class the extraspecial-core obstruction is already proved. The second-class
local obstruction remains the explicit input to this conditional assembly;
the original block layer and its order sixteen are preserved in that input.

Source: Aschbacher--Smith 2.4.25, printed p.543. The original evenness producer
and second native leaf have independent owners; neither is inferred from a
full ambient Sylow bound.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
open Janko4 Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem not_local_alternating_five_of_equiv
    {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]
    (e : G ≃* D) (A : Subgroup G) (hA : ChapterC.IsAlternatingBlock A 5)
    (hc : Nat.card ((ChapterC.blockU A).map A.subtype) = 16)
    (hD : ∀ B : Subgroup D, ChapterC.IsAlternatingBlock B 5 →
      Nat.card ((ChapterC.blockU B).map B.subtype) = 16 →
      ∀ S : Sylow 2 D, B ∉ ChapterA.Section03.localCComponents S)
    (S : Sylow 2 G) : A ∉ ChapterA.Section03.localCComponents S := by
  intro hl
  have hB := ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
    (A.equivMapOfInjective e.toMonoidHom e.injective) hA
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  have hU : (ChapterC.blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype =
      ((ChapterC.blockU A).map A.subtype).map e.toMonoidHom := by
    rw [← ChapterC.RankOne.Solvable.blockU_map_equiv (A.equivMapOfInjective e.toMonoidHom e.injective), map_map, map_map]
    rfl
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  apply hD (A.map e.toMonoidHom) hB (by rw [hU,card_map_of_injective e.injective]; exact hc)
    (S.mapSurjective (f := e.toMonoidHom) hes)
  rw [Sylow.coe_mapSurjective]
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom

/-- The actual even block-centralizer and normalizer Sylow select a literal
characteristic-two escape. The second native centralizer leaf remains explicit. -/
theorem even_centralizer_escape_of_second
    (hsecond : ∀ A : Subgroup Second.ambientCentralizer,
      ChapterC.IsAlternatingBlock A 5 →
      Nat.card ((ChapterC.blockU A).map A.subtype) = 16 →
      ∀ S : Sylow 2 Second.ambientCentralizer,
        A ∉ ChapterA.Section03.localCComponents S)
    (B : Subgroup Model) (hB : ChapterC.IsAlternatingBlock B 5)
    (hc : Nat.card ((ChapterC.blockU B).map B.subtype) = 16)
    (heven : 2 ∣ Nat.card (centralizer (B : Set Model)))
    (P : Sylow 2 (normalizer (B : Set Model))) :
    ∃ N : Subgroup Model, B ≤ N ∧
      (P : Subgroup (normalizer (B : Set Model))).map
        (normalizer (B : Set Model)).subtype ≤ N ∧
      N ∈ Chapter1.He Model ∧ ∀ Q : Sylow 2 N,
        B.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  obtain ⟨z,_,hBZ,hPZ,hchar,hcases⟩ :=
    even_centralizer_normalizer_sylow_placement B P heven
  let N := centralizer ({z} : Set Model)
  have hBN : ChapterC.IsAlternatingBlock (B.subgroupOf N) 5 :=
    ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv
      (subgroupOfEquivOfLe hBZ).symm hB
  have hcBN : Nat.card ((ChapterC.blockU (B.subgroupOf N)).map (B.subgroupOf N).subtype) = 16 := by
    rw [card_map_of_injective (B.subgroupOf N).subtype_injective]
    have heU := ChapterC.RankOne.Solvable.blockU_map_equiv (subgroupOfEquivOfLe hBZ)
    rw [card_map_of_injective B.subtype_injective] at hc
    rw [← heU, card_map_of_injective (subgroupOfEquivOfLe hBZ).injective] at hc
    exact hc
  refine ⟨N,hBZ,hPZ,Chapter1.mem_He_iff.mpr hchar,?_⟩
  intro Q
  rcases hcases with h | h
  · obtain ⟨e⟩ := h
    exact not_local_alternating_five_of_equiv e _ hBN hcBN (fun A hA _ S => first_not_local_alternating_five A hA S) Q
  · obtain ⟨e⟩ := h
    exact not_local_alternating_five_of_equiv e _ hBN hcBN hsecond Q
end CFSG.Quasithin.Chapter2.AlternatingTerminal.JankoFour
