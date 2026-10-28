module
public import Theory.Representation.BinaryPermutation.FivePairExtension
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# Faithfulness of the two five-letter cores

The odd-degree core-to-natural equivalence transfers the genuine faithful
five-letter action. Faithfulness of each coordinate proves faithfulness of
the paired action used to descend the original source quotient.
-/

public section
namespace BinaryPermutation.FivePair
open FiveCentralExtension

theorem core_injective : Function.Injective (coreRepresentation (Fin 5)) := by
  intro g h hgh
  apply naturalRepresentation_injective (Fin 5) (by decide)
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := (coreEquivNatural (Fin 5) (by decide)).surjective v
  rw [←coreEquivNatural_equivariant,←coreEquivNatural_equivariant,hgh]

theorem action_injective : Function.Injective action := by
  intro g h hgh
  apply Prod.ext
  · apply core_injective
    apply LinearMap.ext
    intro v
    exact congrArg Prod.fst (LinearMap.congr_fun hgh (v,0))
  · apply core_injective
    apply LinearMap.ext
    intro v
    exact congrArg Prod.snd (LinearMap.congr_fun hgh (0,v))
end BinaryPermutation.FivePair
