module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.Bridge
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance.Certificates

/-!
# Invariance of the concrete Rudvalis orbital

Both ATLAS generators preserve the relation defined by transporting the forest
component rooted at one. The finite calculation uses packed rows and certified
bit-routing circuits. Each circuit is checked against its actual permutation,
and all 4060 row identities are kernel-checked in bounded blocks.

The packed relation has the correct row at zero. Its independently proved
generator invariance then identifies it with `adj` using the actual word
`toBase (transDepth x) x`. Thus the table is certified against the published
relation without assuming invariance of the full stabilizer's forest classes.

Source: GLS3, Table 5.3r, printed p.279, the action of degree 4060 with
subdegrees 1, 1755 and 2304. The ATLAS permutation data and inverse-action
convention are documented in `Model.PermutationData`. This proves generator
invariance; the separate normalizer calculation also requires rigidity.
-/

namespace Rudvalis.OuterNormalizer

namespace InvarianceCertificate

/-- The binary relation read from the packed witness matrix. -/
@[expose] public def cachedAdj (x y : Fin 4060) : Prop := (row x).testBit y.val = true

public instance (x y : Fin 4060) : Decidable (cachedAdj x y) :=
  inferInstanceAs (Decidable (_ = _))

private theorem cached_a (x y : Fin 4060) :
    cachedAdj (aPerm x) (aPerm y) ↔ cachedAdj x y := by
  change (row (Data.aMap x)).testBit (Data.aMap y).val = true ↔
    (row x).testBit y.val = true
  rw [← sound aCircuit y.val (Data.aMap y).val (row (Data.aMap x)) (allFacts y).1,
    (allFacts x).2.2.1]

private theorem cached_b (x y : Fin 4060) :
    cachedAdj (bPerm x) (bPerm y) ↔ cachedAdj x y := by
  change (row (Data.bMap x)).testBit (Data.bMap y).val = true ↔
    (row x).testBit y.val = true
  rw [← sound bCircuit y.val (Data.bMap y).val (row (Data.bMap x)) (allFacts y).2.1,
    (allFacts x).2.2.2]

set_option maxRecDepth 30000 in
private theorem cached_zero : ∀ y, cachedAdj 0 y ↔ PrimitiveData.root y = 1 := by
  apply Data.allFin
  decide +kernel

/-- Kernel certification that the cached table is exactly the relation defined
using the transitivity words and the stabilizer forest. -/
public theorem cachedAdj_iff_adj (x y : Fin 4060) : cachedAdj x y ↔ adj x y :=
  eq_adj cachedAdj cached_a cached_b cached_zero x y

end InvarianceCertificate

open InvarianceCertificate

/-- The actual first ATLAS generator preserves the published relation. -/
public theorem aPerm_mem_relationAut : aPerm ∈ relationAut := by
  intro x y
  exact (cachedAdj_iff_adj _ _).symm.trans ((cached_a x y).trans (cachedAdj_iff_adj x y))

/-- The actual second ATLAS generator preserves the published relation. -/
public theorem bPerm_mem_relationAut : bPerm ∈ relationAut := by
  intro x y
  exact (cachedAdj_iff_adj _ _).symm.trans ((cached_b x y).trans (cachedAdj_iff_adj x y))

end Rudvalis.OuterNormalizer
