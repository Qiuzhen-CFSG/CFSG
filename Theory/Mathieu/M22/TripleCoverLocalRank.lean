module
public import Theory.Alternating.TripleSevenLocalRank.CentralSix
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates

/-!
# Local cubic rank in genuine triple covers of M₂₂

The checked splitting of the native hexad stabilizer supplies an injective
A₆ section in the actual degree-22 group. Its inverse image under the
specified central quotient has central kernel of order three. The local
rank obstruction for arbitrary cubic A₆ extensions therefore produces
an actual two-local of three-rank at least two in the covering group.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36. The hexad construction
is the actual carrier geometry of 2.3.9(7)(f), printed p.525. Neither a
quotient rank inequality nor a rank conclusion is assumed.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu
open scoped Pointwise

/-- The actual A₆ section of the native hexad stabilizer. -/
def hexadAlternatingSixEmbedding : alternatingGroup (Fin 6) →* M22 :=
  (MulAction.stabilizer M22 m22Hexad123).subtype.comp (m22HexadSection m22Hexad123_mem)

theorem hexadAlternatingSixEmbedding_injective : Function.Injective hexadAlternatingSixEmbedding :=
  (MulAction.stabilizer M22 m22Hexad123).subtype_injective.comp
    (m22HexadSection_injective m22Hexad123_mem)

theorem triple_cover_twoLocalThreeRank_ge_two {L : Type*} [Group L] [Finite L]
    (e : L ⧸ center L ≃* M22) (hc : Nat.card (center L) = 3) :
    2 ≤ twoLocalPrimeRank 3 L := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    ext x
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ x ∈ center L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact GLS3.Chapter5.OddCentralCovers.twoLocalThreeRank_ge_two_of_embedded_six f hf hk.le (hk ▸ hc)
    hexadAlternatingSixEmbedding hexadAlternatingSixEmbedding_injective

end Sporadic.Mathieu
