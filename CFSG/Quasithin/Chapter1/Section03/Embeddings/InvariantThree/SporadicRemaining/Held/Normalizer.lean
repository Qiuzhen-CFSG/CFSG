module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.GroupTheory.PCoreRestriction

/-!
# Held interval normalizers on an isomorphic original carrier

The concrete Held pair calculation controls the full automorphism normalizer
of each subgroup between the residual two-core and the full Sylow, of index
at most two. This extension transports that result through an actual group
isomorphism. It retains the source irreducibility, the embedded two-residual
and its own two-core, and discharges full automorphism realization and the
permutation-normalizer quotient bound using their proved model theorems.

Source: the corrected Held branch of Aschbacher--Smith 1.3.4 and the
normalizer argument of 10.2.5, printed pp.509--511 and 747--748.
The original Chapter 10 application is BinaryThreeAction/Held.lean.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
variable {Q : Type*} [Group Q] [Finite Q]

/-- The actual Held calculation transports through an arbitrary marked group
isomorphism, preserving the full Sylow, irreducibility, two-core and index. -/
theorem preserves_residual_of_equiv
    {S : Sylow 2 Q} {P X U : Subgroup Q}
    (h : PairInput S P) (hI : ¬ PairReducible (S : Subgroup Q) P)
    (e : Q ≃* Held.He)
    (hres : (pResidual 2 (P ⊔ (S : Subgroup Q) : Subgroup Q)).map
      (P ⊔ (S : Subgroup Q)).subtype = X)
    (hcore : X.pCoreIn 2 ≤ U) (hUS : U ≤ (S : Subgroup Q))
    (hindex : U.relIndex (S : Subgroup Q) ≤ 2)
    (a : MulAut Q) (ha : U.map a.toMonoidHom = U) : X.map a.toMonoidHom = X := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let P' := P.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  have hp : PairInput S' P' := pairInput_of_equiv h e
  have hirr : ¬ PairReducible (S' : Subgroup Held.He) P' :=
    fun hr => hI (SporadicActions.pairReducible_of_map e S P hr)
  have hX : Held.LocalPairs.residual (S' : Subgroup Held.He) P' = X.map e.toMonoidHom := by
    change (pResidual 2 (P.map e.toMonoidHom ⊔ (S : Subgroup Q).map e.toMonoidHom :
      Subgroup Held.He)).map (P.map e.toMonoidHom ⊔ (S : Subgroup Q).map e.toMonoidHom).subtype = _
    rw [← Subgroup.map_sup,← map_embedded_pResidual,hres]
  have hc : Held.LocalPairs.twoCore (S' : Subgroup Held.He) P' ≤ U' := by
    change (Held.LocalPairs.residual (S' : Subgroup Held.He) P').pCoreIn 2 ≤ _
    rw [hX,← map_pCoreIn_of_injective 2 X e.toMonoidHom e.injective]
    exact map_mono hcore
  have hi : U'.relIndex (S' : Subgroup Held.He) ≤ 2 := by
    change (U.map e.toMonoidHom).relIndex ((S : Subgroup Q).map e.toMonoidHom) ≤ 2
    rw [relIndex_map_map_of_injective _ _ e.injective]
    exact hindex
  have hn := intervalNormalizer Held.Realization.normalizer_surjective
    Held.permutationNormalizerQuotient_card_le_two hp hirr U' hc (map_mono hUS) hi
  have he : (MulAut.congr e a).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hau : MulAut.congr e a ∈ Held.LocalPairs.automorphismNormalizer U' := by
    change (U.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom = U.map e.toMonoidHom
    rw [Subgroup.map_map,he,← Subgroup.map_map,ha]
  have hx := hn hau
  change (Held.LocalPairs.residual (S' : Subgroup Held.He) P').map
    (MulAut.congr e a).toMonoidHom = Held.LocalPairs.residual (S' : Subgroup Held.He) P' at hx
  rw [hX,Subgroup.map_map,he,← Subgroup.map_map] at hx
  exact Subgroup.map_injective e.injective hx

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
