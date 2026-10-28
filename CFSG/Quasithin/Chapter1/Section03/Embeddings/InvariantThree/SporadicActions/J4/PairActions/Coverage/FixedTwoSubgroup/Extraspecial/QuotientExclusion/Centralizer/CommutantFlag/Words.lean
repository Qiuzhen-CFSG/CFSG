module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Extraspecial.QuotientExclusion.Centralizer.Reduction

/-!
# Ten literal words in the third lower-central subgroup of the J₄ two-subgroup

Every selected word is [gₖ,[gᵢ,gⱼ]], with the actual fifteen generators of
`OddIndex.twoSubgroup`. Membership follows directly from the definition of
subgroup commutators. No polycyclic presentation or order calculation is used.
These words are used for the matrix route to the sporadic case of
Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
open Janko4.OuterReduction.OddIndex
open scoped commutatorElement

set_option maxRecDepth 10000
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Indices 0–10 are kernel generators; indices 11–14 are the four Sylow lifts. -/
def generatorIndex (i : Fin 15) : Fin 11 ⊕ Fin 4 :=
  if h : i.val < 11 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 11, by omega⟩

/-- A linear indexing of the existing generators, without changing their words. -/
def generator (i : Fin 15) : Janko4.Model :=
  twoGenerator (generatorIndex i)

theorem generator_mem (i : Fin 15) : generator i ∈ twoSubgroup :=
  twoGenerator_mem (generatorIndex i)

/-- Each entry is (k,i,j), specifying [gₖ,[gᵢ,gⱼ]]. -/
def tripleIndices : Fin 10 → Fin 15 × Fin 15 × Fin 15 :=
  ![(12, 14, 3), (12, 13, 2), (3, 14, 11), (14, 13, 12), (12, 13, 1),
    (14, 14, 13), (5, 14, 12), (0, 14, 11), (12, 14, 13), (11, 14, 12)]

/-- The selected elements of the actual J₄ carrier. -/
def tripleWord (a : Fin 10) : Janko4.Model :=
  ⁅generator (tripleIndices a).1,
    ⁅generator (tripleIndices a).2.1, generator (tripleIndices a).2.2⁆⁆

/-- The literal words belong to D = [T,[T,T]], independently of their matrices. -/
theorem tripleWord_mem (a : Fin 10) : tripleWord a ∈ fixedTwoThirdCommutator :=
  Subgroup.commutator_mem_commutator (generator_mem _)
    (Subgroup.commutator_mem_commutator (generator_mem _) (generator_mem _))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.ThirdFlag
