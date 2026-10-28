module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.IntervalNormalizer.Inner.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.LocalActions.Exhaustion

/-!
# Local Held core inclusion and quotient normalizer control

A simultaneous conjugacy inside M transports the local two-core and the
actual quotient images. The commutator calculation at the representative
then puts O₂(M) inside O₂(O²(RS)). A four-point orbit in a six-point action
controls the quotient normalizer of every subgroup between that two-core
and RS, hence in particular the requested index-at-most-two interval in S.

The conditional reductions are retained below. The final `local_calculations`
theorem discharges their representative commutators, action homomorphisms,
orbit equalities, stabilizer-preimage equalities and exhaustive conjugacy
using the checked literal calculations. It retains the original
irreducibility input and needs no automorphism-model premise. Ambient
normalizer containment is a separate calculation, combined with these local
outputs by the parent Inner assembly.

Sources: Aschbacher–Smith, printed pp.509–511 and 747–748; GLS3 Table 5.3p;
the literal ATLAS candidates in PairCoverage.LocalActions.Candidates.
-/

public section

open Subgroup
open scoped Pointwise
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

/-- Conditional assembly from one actual simultaneous local conjugacy and
geometric witnesses at its representative. -/
theorem local_calculations_of_conjugate_sixPointAction
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (S₀ R₀ : Subgroup Held.He) (g : localOvergroup i)
    (hS : (S : Subgroup Held.He).map (MulAut.conj g.val).toMonoidHom = S₀)
    (hR : R.map (MulAut.conj g.val).toMonoidHom = R₀)
    (hcomm : ⁅localTwoCore i, R₀⁆ = localTwoCore i)
    (f : LocalQuotient i →* Equiv.Perm (Fin 6)) (B : Set (Fin 6)) (x : Fin 6)
    (hB : B.ncard = 4)
    (hK : (MulAction.stabilizer (Equiv.Perm (Fin 6)) B).comap f = localImage i (R₀ ⊔ S₀))
    (horbit : MulAction.orbit ((localImage i (Held.LocalPairs.twoCore S₀ R₀)).map f) x = B) :
    localTwoCore i ≤ Held.LocalPairs.twoCore S R ∧
      ∀ U : Subgroup Held.He, Held.LocalPairs.twoCore S R ≤ U →
        U ≤ R ⊔ (S : Subgroup Held.He) →
        normalizer (localImage i U : Set (LocalQuotient i)) ≤
          localImage i (R ⊔ (S : Subgroup Held.He)) := by
  constructor
  · apply localTwoCore_le_pair_twoCore_of_commutator i S R h hplace
    apply local_commutator_eq_of_conj i g R
    rwa [hR]
  · intro U hQU hUK
    apply local_normalizer_le_of_conj i g U _ (hUK.trans hplace) hplace
    rw [Subgroup.map_sup, hS, hR]
    apply local_normalizer_le_of_sixPointAction i S₀ R₀ _ f B x hB hK horbit
    · have hc := map_mono (f := (MulAut.conj g.val).toMonoidHom) hQU
      rwa [Held.LocalPairs.twoCore_map, hS, hR] at hc
    · have hc := map_mono (f := (MulAut.conj g.val).toMonoidHom) hUK
      rwa [Subgroup.map_sup, hS, hR] at hc

/-- The exact task conclusions follow from exhaustive simultaneous conjugacy
and the finite list of genuine six-point geometric witnesses. -/
theorem local_calculations_of_representative_geometry
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hcover : ∃ j : Fin 2, ∃ g : Held.He, g ∈ localOvergroup i ∧
      (S : Subgroup Held.He).map (MulAut.conj g).toMonoidHom = LocalActions.candidateTwo i j ∧
      R.map (MulAut.conj g).toMonoidHom = LocalActions.candidateOdd i j)
    (hcomm : ∀ j : Fin 2,
      ⁅localTwoCore i, LocalActions.candidateOdd i j⁆ = localTwoCore i)
    (hgeometry : ∀ j : Fin 2,
      ∃ f : LocalQuotient i →* Equiv.Perm (Fin 6), ∃ B : Set (Fin 6), ∃ x : Fin 6,
      B.ncard = 4 ∧
      (MulAction.stabilizer (Equiv.Perm (Fin 6)) B).comap f =
        localImage i (LocalActions.candidateOdd i j ⊔ LocalActions.candidateTwo i j) ∧
      MulAction.orbit ((localImage i
        (Held.LocalPairs.twoCore (LocalActions.candidateTwo i j)
          (LocalActions.candidateOdd i j))).map f) x = B) :
    localTwoCore i ≤ Held.LocalPairs.twoCore S R ∧
      ∀ U : Subgroup Held.He, Held.LocalPairs.twoCore S R ≤ U → U ≤ S → U.relIndex S ≤ 2 →
        normalizer (localImage i U : Set (LocalQuotient i)) ≤
          localImage i (R ⊔ (S : Subgroup Held.He)) := by
  obtain ⟨j, g, hg, hS, hR⟩ := hcover
  obtain ⟨f, B, x, hB, hK, horbit⟩ := hgeometry j
  obtain ⟨hc, hn⟩ := local_calculations_of_conjugate_sixPointAction i S R h hplace
    _ _ ⟨g, hg⟩ hS hR (hcomm j) f B x hB hK horbit
  exact ⟨hc, fun U hQU hUS _ => hn U hQU (hUS.trans le_sup_right)⟩

/-- Both local outputs under the original placed-pair hypotheses. Exhaustive
simultaneous conjugacy and all four representative geometries are proved;
no additional model or catalogue premise remains. -/
theorem local_calculations
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (_hI : ¬ PairReducible (S : Subgroup Held.He) R) :
    localTwoCore i ≤ Held.LocalPairs.twoCore S R ∧
      ∀ U : Subgroup Held.He, Held.LocalPairs.twoCore S R ≤ U → U ≤ S → U.relIndex S ≤ 2 →
        normalizer (localImage i U : Set (LocalQuotient i)) ≤
          localImage i (R ⊔ (S : Subgroup Held.He)) :=
  local_calculations_of_representative_geometry i S R h hplace
    (LocalActions.pair_conjugate i S R h hplace)
    (RepresentativeGeometry.localTwoCore_commutator i)
    (RepresentativeGeometry.geometry i)

/-- The local two-core lies in O₂(O²(RS)), with both cores embedded in Held. -/
theorem localTwoCore_le_pair_twoCore
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R) :
    localTwoCore i ≤ Held.LocalPairs.twoCore S R :=
  (local_calculations i S R h hplace hI).1

/-- The interval normalizer calculation in the actual quotient M/O₂(M). -/
theorem localQuotient_normalizer_le_pairProduct
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He) (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (U : Subgroup Held.He) (hQU : Held.LocalPairs.twoCore S R ≤ U)
    (hUS : U ≤ S) (hindex : U.relIndex S ≤ 2) :
    normalizer (localImage i U : Set (LocalQuotient i)) ≤
      localImage i (R ⊔ (S : Subgroup Held.He)) :=
  (local_calculations i S R h hplace hI).2 U hQU hUS hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
