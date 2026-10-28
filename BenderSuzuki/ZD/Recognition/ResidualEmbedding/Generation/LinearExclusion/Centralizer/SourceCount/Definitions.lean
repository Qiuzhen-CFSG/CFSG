module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces

/-!
# The original normalizer in the source centralizer count

We retain the literal subgroups U = O₂(C_G(L)), V = O₂(M), and
R₁ = N_V(AU), with subtype images in G. `NormalizerData` is an explicit
intermediate contract for the normalizer-growth part of Lemma 15.6. Its
normality is relative to M; its order still contains the unknown |U|.
Neither the order of J nor the order of its normal closure is assumed.

Source: GLS IV, Chapter 2, Lemma 15.6 and (15F),
refs/KGroup/GLS4/Chapter2.tex, lines 2718–2736.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G]

/-- The actual two-core of the centralizer, as a subgroup of G. -/
@[expose] public def twoCore (M : Subgroup G) (z t : G) : Subgroup G :=
  (pCore 2 (centralizer (residualGenerated M z t : Set G))).map
    (centralizer (residualGenerated M z t : Set G)).subtype

/-- The actual two-core of the point stabilizer, as a subgroup of G. -/
@[expose] public def pointCore (M : Subgroup G) : Subgroup G :=
  (pCore 2 M).map M.subtype

/-- The source subgroup N_V(AU); normality is not part of this definition. -/
@[expose] public def sourceNormalizer (Z : Set G) (M : Subgroup G) (z t : G) :
    Subgroup G :=
  pointCore M ⊓ Subgroup.normalizer
    ((closure (Z ∩ (M : Set G)) ⊔ twoCore M z t : Subgroup G) : Set G)

/-- The normalizer-growth and elementary-section conclusions, before the
involution census. The last clause is freeness of K on the nonidentity
cosets of AU in R₁, expressed using the original elements of G. -/
public structure NormalizerData [Finite G] {Z : Set G} {M : Subgroup G}
    {z t : G} {n : ℕ} (d : Context Z M z t n) : Prop where
  relative_normal : ((sourceNormalizer Z M z t).subgroupOf M).Normal
  card : Nat.card (sourceNormalizer Z M z t) = (2 ^ n) ^ 2 * Nat.card (twoCore M z t)
  square_mem : ∀ x ∈ sourceNormalizer Z M z t, x ^ 2 ∈ closure (Z ∩ (M : Set G))
  torus_free : ∀ k ∈ residualCommutator M t, k ≠ 1 →
    ∀ x ∈ sourceNormalizer Z M z t,
      x ∉ closure (Z ∩ (M : Set G)) ⊔ twoCore M z t →
      MulAut.conj k x * x⁻¹ ∉ closure (Z ∩ (M : Set G)) ⊔ twoCore M z t

end BenderSuzuki.ZD.LinearExclusion.SourceCount
