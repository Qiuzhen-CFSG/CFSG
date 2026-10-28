module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Data

/-!
# Small checks connecting the cached tables to the literal action

Each block covers eight vertices. The concrete block modules discharge every
field by kernel reduction, with proof elaboration serialized to bound memory.
The checks use the original transversal permutations and all eleven basis pairs.
-/
@[expose] public section
namespace Janko4.TwoRank.Finite
open LocalStructure.SylowCore.FiniteBoundCertificate
open LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image

structure BlockValid (k : Fin 24) : Prop where
  codes : ∀ o : Fin 8, code (vertex (blockVertex k o)) = blockVertex k o
  points : ∀ (o : Fin 8) (p : Fin 24),
    point (blockVertex k o) p = perm (vertex (blockVertex k o)) p
  rows : ∀ o : Fin 8, row (blockVertex k o) = NormalWeights.rows (vertex (blockVertex k o))
  compatible : ∀ (o : Fin 8) (j : Fin 24) (q : Fin 8),
    (∀ p : Fin 3,
      point (blockVertex k o) (point (blockVertex j q) (p.castLE (by decide))) =
      point (blockVertex j q) (point (blockVertex k o) (p.castLE (by decide)))) →
      Finite.compatible (blockVertex k o) (blockVertex j q) = true
  low : ∀ (o : Fin 8) (b : Fin 64),
    Finite.low (blockVertex k o) b.val = maskImage (row (blockVertex k o)) b.val ^^^ b.val
  high : ∀ (o : Fin 8) (a : Fin 32),
    Finite.high (blockVertex k o) a.val =
      maskImage (row (blockVertex k o)) (a.val * 64) ^^^ (a.val * 64)
end Janko4.TwoRank.Finite
