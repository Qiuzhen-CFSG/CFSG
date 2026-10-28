module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking

/-!
# The compatible eight-point marking after the enlargement sieve

The binary graph alternative gives an actual identification K ≃ SL₄(2).
Compose it with the exceptional SL₄(2) ≃ PSL₄(2) ≃ A₈ comparison. The
relative component L of K∩C_G(z), together with L < K and L ≃ A₆, selects the
transposition class in the actual normalizer action. The resulting single
equivalence K⟨z⟩ ≃ S₈ sends z to `(0 1)`, K to A₈, and L to the even
permutations fixing 0 and 1 individually.

The component argument only needs the normalization and model equivalences
from the graph alternative; it proves the action marking without a separate
inverse-transpose computation. The case sieve remains the responsibility
of the preceding source argument.

Source: Aschbacher–Smith, 16.3.11(3) and the setup for 16.3.12, combined
manuscript of 1 March 2004, printed p.1181 (PDF p.1198).
-/

namespace CFSG.Quasithin.Chapter16.EnlargementSieve
open Subgroup

/-- The genuine proper relative component in the binary graph case determines
one compatible A₈–A₆ transposition marking of the actual extension. -/
public theorem markedEightSix_of_binaryFourGraphAlternative
    {G : Type*} [Group G] {K L : Subgroup G} {z : G}
    (hgraph : BinaryFourGraphAlternative K L z) (hz : orderOf z = 2)
    (hLK : L < K)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z)) :
    Nonempty (MarkedEightSix K L z) := by
  obtain ⟨hzN, e, _, _, ⟨eL⟩⟩ := hgraph
  let eK : K ≃* alternatingGroup (Fin 8) :=
    (e.trans Atlas.Order20160A8.sl4TwoEquivPSL).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hcardL : Nat.card L = 360 := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  obtain ⟨f, hfz, hfK, hfL⟩ :=
    Theory.SpecificGroups.SymmetricEight.ComponentMarking.exists_marked_equiv
      eK hzN hz hLK hL hcardL
  exact ⟨{ smaller_le := hLK.le
           equiv := f
           involution_image := hfz
           larger_image := hfK
           smaller_image := hfL }⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve
