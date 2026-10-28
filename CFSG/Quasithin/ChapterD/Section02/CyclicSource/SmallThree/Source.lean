module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.SourceGeometry
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Generation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.TwoFactorEndpoint

/-!
# The original D.2.25 small-three local generation

The actual order-three support witness gives the canonical normal E₉ and its
two complementary binary planes. The two-plane normalizer and the exclusion
of elementary four-subgroups give an involution supplement. Generation by the
original starred involutions supplies the full commutator identity. Thus the
original kernel, involution and module give the concrete local-generation
input to the cyclic classification, retaining all source hypotheses.

Source: Aschbacher–Smith D.2.25 and D.2.17(3), printed p.190.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The complete small-three branch, on the literal source group and module. -/
theorem Hypotheses.small_three_localGeneration (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hne : ∃ X : Subgroup G, X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2) :
    Nonempty (LocalGeneration ρ) := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  let : IsElementaryAbelian 3 Y := canonical_elementary ρ h.faithful
  obtain ⟨d,_,hY,_⟩ := h.smallThree_two_supportFactors ρ hH f honto hfive hq hne
  change Nat.card Y = 9 at hY
  obtain ⟨_,t,ht,hgen,hcodim⟩ := SmallThree.two_factor_endpoint ρ h.faithful
    Y d hY h.generated hq h.rank_one
  apply h.toCoreHypotheses.localGeneration_of_three_kernel Y
    (fun he => by rw [he,Subgroup.card_bot] at hY; omega)
    (h.smallThree_moved ρ hfive hq hne) t ht hgen hcodim.le
end CFSG.Quasithin.ChapterD.CyclicSource
