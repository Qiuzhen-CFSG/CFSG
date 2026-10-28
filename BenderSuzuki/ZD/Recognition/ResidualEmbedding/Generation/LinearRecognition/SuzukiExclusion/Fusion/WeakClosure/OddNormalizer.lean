module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.Centralizers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.FrobeniusExclusion
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.ActionConsequences
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.NativeAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.OddNormalizer.Fitting

/-!
# The odd Suzuki quotient normalizer

The faithful conjugation action of N_M(S)/S on the actual image of S in
M/M° is constructed from the local geometry and centralizer embedding.
Equation (14G) and the torus centralizer calculation then give the Fitting
alternatives. The nontrivial intersection fixes the order-two image of U;
the trivial intersection would give an abelian Frobenius kernel, excluded
by the binary degree bound and the exceptional q = 8 divisor sieve.

This proves invariance under the full normalizer of S-bar in M/M°, and
the literal Burnside consumer gives weak closure. The enclosing weak-closure
assembly retains the three explicit earlier premises: |U| = 2, elementary
abelianness of S-bar in this branch, and the exceptional divisor bound.
Source: GLS4, Chapter 2, Lemma 14.9,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2600–2620.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- The odd-normalizer argument of Lemma 14.9 in the literal quotient M/M°.
The action and its Fitting argument are discharged here; the enclosing source
assembly supplies the order-two, elementary-quotient and exceptional premises. -/
public theorem Context.quotientNormalizerInvariant_of_odd_normalizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294) :
    QuotientNormalizerInvariant d g := by
  obtain ⟨a⟩ := OddNormalizer.actionData d g hsemi f hf s hU he
  exact a.normalizerInvariant_of_fitting d g hsemi s hU he hD8

/-- Burnside weak closure in the elementary-quotient branch of Lemma 14.9,
with the odd-normalizer invariance premise proved from its source inputs. -/
public theorem Context.quotientFusion_of_odd_normalizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hsemi : TorusSemiregular M t)
    (f : centralizer (residualGenerated M z t : Set G) →* residualGenerated M z t)
    (hf : Function.Injective f) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (he : ElementaryQuotient d g)
    (hD8 : m = 1 → Nat.card (residualPairStabilizer M t) ∣ 294) :
    QuotientFusion d g :=
  quotientFusion_of_elementary_normalizer d g s he
    (d.quotientNormalizerInvariant_of_odd_normalizer g hsemi f hf s hU he hD8)

end BenderSuzuki.ZD.SuzukiExclusion
