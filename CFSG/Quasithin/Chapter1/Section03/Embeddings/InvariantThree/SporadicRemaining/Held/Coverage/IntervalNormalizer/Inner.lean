module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.IntervalNormalizer.Inner.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Held.Coverage.IntervalNormalizer.Inner.Local

/-!
# Assembly of inner Held interval normalizers

The source pair input supplies the odd complement and the actual simple Held
carrier. The literal local calculation supplies both the embedded two-core
inclusion and the quotient normalizer bound, while the independent ambient
calculation places every interval subgroup normalizer inside the local
overgroup. Their shared reduction gives the required inner normalizer control.
Full automorphism assembly remains in the parent module.

Sources: Aschbacher–Smith, printed pp.509–511 and 747–748; GLS3, Table 5.3p.
-/

public section

open Subgroup
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs

/-- The concrete inner Held calculation for a locally placed irreducible pair.

For every subgroup in the two-core interval of `S`, with relative index at
most two, its normalizer in the actual Held carrier normalizes the pair
residual. The ambient and quotient bounds are discharged by the literal
max3/max4 and six-point calculations, respectively.
-/
theorem inner_intervalNormalizer
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (h : PairInput S R)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hI : ¬ PairReducible (S : Subgroup Held.He) R)
    (U : Subgroup Held.He)
    (hQU : Held.LocalPairs.twoCore S R ≤ U)
    (hUS : U ≤ S)
    (hindex : U.relIndex S ≤ 2) :
    normalizer (U : Set Held.He) ≤
      normalizer (Held.LocalPairs.residual S R : Set Held.He) := by
  exact inner_intervalNormalizer_of_local_calculations i S R h hplace
    (localTwoCore_le_pair_twoCore i S R h hplace hI)
    (fun _ U hCU hUS hindex =>
      Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.normalizer_le
        i S (le_sup_right.trans hplace) U hCU hUS hindex)
    (fun U hQU hUS hindex =>
      localQuotient_normalizer_le_pairProduct i S R h hplace hI U hQU hUS hindex)
    U hQU hUS hindex

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.HeldPairs
