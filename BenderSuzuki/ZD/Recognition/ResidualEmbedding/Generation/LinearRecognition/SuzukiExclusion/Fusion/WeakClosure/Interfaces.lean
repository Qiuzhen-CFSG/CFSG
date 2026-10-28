module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts

/-!
# Intermediate statements for Suzuki complements and quotient normalizers

These definitions specify the remaining outputs of GLS4, Chapter 2,
Lemmas 14.7 and 14.9. The quotient is always the literal quotient of M
by its distinguished closure. No inhabitant of these predicates is
asserted here; the enclosing WeakClosure proof must construct them.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The elementary complement of T in S, invariant under the actual K and Y. -/
@[expose] public def InvariantElementaryComplement
    (g : LocalGeometry Z M z t m) (Y : Subgroup G) : Prop :=
  ∃ A : Subgroup G, A ≤ g.S ∧ IsElementaryAbelian 2 A ∧ Disjoint g.T A ∧
    (g.S : Set G) = (g.T : Set G) * (A : Set G) ∧
    residualCommutator M t ⊔ Y ≤ normalizer (A : Set G)

/-- Elementary abelianness of the image of S in the literal quotient M/M°. -/
@[expose] public def ElementaryQuotient (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : Prop :=
  let A := closure (Z ∩ (M : Set G))
  letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  IsElementaryAbelian 2 ((g.S.subgroupOf M).map (QuotientGroup.mk' (A.subgroupOf M)))

/-- The normalizer of the image of S preserves the image of U. -/
@[expose] public def QuotientNormalizerInvariant (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) : Prop :=
  let A := closure (Z ∩ (M : Set G))
  letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  normalizer ((g.S.subgroupOf M).map pi : Set (M ⧸ A.subgroupOf M)) ≤
    normalizer ((g.U.subgroupOf M).map pi : Set (M ⧸ A.subgroupOf M))

end BenderSuzuki.ZD.SuzukiExclusion
