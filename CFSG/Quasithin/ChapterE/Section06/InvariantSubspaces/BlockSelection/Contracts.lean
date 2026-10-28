module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.ThreeAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The source input and remaining obligations for block selection

`BlockFamily` records only the central-product and generation part of
E.6.7(1). Its subnormality is relative to H. `E67Decomposition` retains
the set product, Thompson commutators, and all of clauses (2),(3).
The latter use actual quotient Borels and conjugation commutators. Binary
dimensions of elementary displacement groups are expressed by their orders.

`FixedNineInput` is the intrinsic model obligation in the faithful-three
branch of E.6.14. It does not assume that the actor normalizes either
block. Proving it requires the block permutation argument and the
fixed-three calculation in the actual block models. The residual and
Sylow-overgroup obligations are separate from this count argument.
None of these three remaining obligations is asserted as a theorem here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7
and proof of E.6.14, printed pp.246 and 251 (PDF pp.257 and 262).
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G]

/-- The portion of E.6.7(1) used to count the blocks. This is not the full
source conclusion. No normality in the ambient group is imposed. -/
structure BlockFamily (H M : Subgroup G) where
  count : ℕ
  count_le_two : count ≤ 2
  block : Fin count → Subgroup G
  le : ∀ i, block i ≤ H
  type : ∀ i, ChapterC.IsChiZeroBlock (block i)
  subnormal : ∀ i, ((block i).subgroupOf H).IsSubnormal
  commuting : ∀ i j, i ≠ j → block j ≤ centralizer (block i : Set G)
  generated : H = (H ⊓ M) ⊔ ⨆ i, block i

/-- All three clauses of E.6.7 for the intermediate group H. The subgroup
W is the source's U, and Q is supplied as a parameter to keep the source
conclusion independent of its eventual Sylow construction. The Borel
is the full preimage under an actual quotient isomorphism. -/
structure E67Decomposition (Q M V W H : Subgroup G) extends BlockFamily H M where
  product : (H : Set G) = ((H ⊓ M : Subgroup G) : Set G) *
    ((⨆ i, block i : Subgroup G) : Set G)
  thompson : ∀ i, block i = ⁅block i, Stellmacher.elementaryAbelianMaxJ Q⁆
  alternating : ∀ i n, ChapterC.IsAlternatingBlock (block i) n →
    subgroupCorank V (V ⊓ centralizer (block i : Set G)) = 1 ∧
      ((block i) ⊓ M).relIndex (block i) = n ∧ globalR V = 1
  rankOne : ∀ i n, ChapterC.IsL2EvenBlock (block i) n →
    ∃ X : Subgroup G, X ≤ block i ⊓ M ∧ IsCyclic X ∧ Nat.card X = 2 ^ n - 1 ∧
      V = (V ⊓ centralizer (block i : Set G)) ⊔ ⁅V, X⁆ ∧
      Disjoint (V ⊓ centralizer (block i : Set G)) ⁅V, X⁆ ∧
      Nat.card ↥⁅V, X⁆ = 2 ^ n ∧
      (((block i) ⊓ M : Subgroup G) : Set G) =
        (((block i) ⊓ Q : Subgroup G) : Set G) * (X : Set G) ∧
      L2BlockBorel (block i) (M.subgroupOf (block i)) n ∧
      n ≤ subgroupCorank V W

/-- Exact E.6.7 input, applied to every intermediate characteristic-two
subgroup. Its proof from Hypothesis E.6.1 belongs to the E.6.7 owner.
No single-block, residual, normalizer, or maximal-overgroup conclusion
is included in this source input. -/
def E67Input (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ W ∈ obstructionFamily M V, ∀ H : Subgroup G,
    sylowCentralizer (T : Subgroup G) V ≤ H → H ≤ centralizer (W : Set G) →
    HasCharacteristicTwo H →
      Nonempty (E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V W H)

/-- A precise remaining intrinsic model obligation. H is normal only in N;
the two blocks are subnormal only in H. Their actor need not be assumed
to normalize them. The output is an actual pointwise fixed elementary nine. -/
def FixedNineInput (G : Type*) [Group G] : Prop :=
  ∀ (N H L₁ L₂ : Subgroup G), H ≤ N →
    (H.subgroupOf N).Normal → HasCharacteristicTwo H → primeRank 3 N ≤ 2 →
    L₁ ≤ H → L₂ ≤ H →
    ChapterC.IsChiZeroBlock L₁ → ChapterC.IsChiZeroBlock L₂ →
    (L₁.subgroupOf H).IsSubnormal → (L₂.subgroupOf H).IsSubnormal →
    L₂ ≤ centralizer (L₁ : Set G) →
    ∀ x ∈ N, orderOf x = 3 →
      ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
        E ≤ H ∧ E ≤ centralizer ({x} : Set G)

/-- The residual step after the number of blocks has been proved to be one.
ThreeCondition is retained: counting the selected factors alone does not
eliminate other three-elements in H. This is a remaining proof obligation,
not part of the E.6.7 input. -/
def SingleResidualInput (T : Sylow 2 G) (M V : Subgroup G) : Prop :=
  ∀ W ∈ obstructionFamily M V,
    HasCharacteristicTwo (centralizer (W : Set G)) → ThreeCondition W →
    ∀ d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V W
      (centralizer (W : Set G)), d.count = 1 →
      ∀ i, d.block i = (primeToResidual 3 (centralizer (W : Set G))).map
        (centralizer (W : Set G)).subtype

/-- The intrinsic Sylow-overgroup calculation for a normal chi-zero block.
Normality is relative to H. In the assembly it follows from the proved
residual identity, and is not added to E.6.7. -/
def BlockSylowMaximalInput (G : Type*) [Group G] : Prop :=
  ∀ Q H L : Subgroup G, HasCharacteristicTwo H → Chapter1.IsSylowIn 2 Q H →
    L ≤ H → (L.subgroupOf H).Normal → ChapterC.IsChiZeroBlock L →
      Order.HasUniqueMaximalOver Q (L ⊔ Q)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
