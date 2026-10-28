module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveEvenCentralizer
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.FirstLocal
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LargeSporadic.JankoFour.SecondLocal
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# The original full-Sylow deleted-five exclusion in J₄

A full Sylow normalizing a deleted alternating-five block forces the block
centralizer to have even order: otherwise its join with the block has order
dividing 322560, contrary to the checked J₄ Sylow order 2²¹. The same Sylow
therefore fixes an involution in that centralizer. Both the original block
and the original Sylow lie in its literal involution centralizer.

Actual involution fusion identifies this centralizer with one of the two
certified models. Their existing extraspecial-core and order-five
displacement obstructions exclude the transported local C-component.
The quotient, subgroup and Sylow transports retain the supplied embeddings;
no maximal-local catalogue or extra source-placement hypothesis is used.

Source: Aschbacher–Smith A.3.14(10), printed p.49, and the original
positive-center branch of 10.2.1, printed p.743. The two native centralizer
calculations were developed for 2.4.25, printed p.543.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterC
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem not_local_deleted_of_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H)
    (hbad : ∀ (A : Subgroup H), IsAlternatingBlock A 5 →
      ∀ S : Sylow 2 H, A ∉ localCComponents S)
    (S : Sylow 2 G) (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  apply hbad (B.map e.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap B) hB)
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom

/-- J₄ has no actual deleted-five local block normalized by its full Sylow. -/
theorem alternatingFiveDeleted_not_j4_native
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : IsAlternatingBlock B 5) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model)) : False := by
  have heven := hB.even_centralizer_of_normalizing_sylow_card S B hn (by
    rw [Janko4.OuterReduction.OddIndex.ambient_sylow_card S]
    decide)
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup Janko4.Model) S.isPGroup' hn heven
  let N := centralizer ({z} : Set Janko4.Model)
  have hBN : B ≤ N := le_sup_left.trans h
  have hSN : (S : Subgroup Janko4.Model) ≤ N := le_sup_right.trans h
  have hB' : IsAlternatingBlock (B.subgroupOf N) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBN).symm hB
  have hl' : B.subgroupOf N ∈ localCComponents (S.subtype hSN) := local_restrict hl hBN
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second z hz with h | h
  · obtain ⟨e⟩ := h
    exact not_local_deleted_of_equiv e
      Chapter2.AlternatingTerminal.JankoFour.first_not_local_alternating_five
      (S.subtype hSN) (B.subgroupOf N) hB' hl'
  · obtain ⟨e⟩ := h
    exact not_local_deleted_of_equiv e
      Chapter2.AlternatingTerminal.JankoFour.second_not_local_alternating_five
      (S.subtype hSN) (B.subgroupOf N) hB' hl'

/-- The native exclusion transported through the specified carrier equivalence,
preserving the actual block and full Sylow. -/
theorem alternatingFiveDeleted_not_j4 {H : Type*} [Group H] [Finite H]
    (e : H ≃* Janko4.Model) (S : Sylow 2 H) (B : Subgroup H)
    (hB : IsAlternatingBlock B 5) (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup H) ≤ normalizer (B : Set H)) : False := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  apply alternatingFiveDeleted_not_j4_native
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (B.map e.toMonoidHom)
    (RankOne.Solvable.isAlternatingBlock_of_equiv (e.subgroupMap B) hB)
  · exact Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom
  · exact (map_mono hn).trans (B.le_normalizer_map e.toMonoidHom)
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
