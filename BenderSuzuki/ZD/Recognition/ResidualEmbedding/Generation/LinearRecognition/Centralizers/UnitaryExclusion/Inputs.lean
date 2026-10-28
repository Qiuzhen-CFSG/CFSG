module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.TwoKernelAbelianBounds

/-!
# Local proof obligations for the unitary exclusion

The second distinguished centralizer is the closure of the distinguished
elements centralizing an actual cyclic subgroup. The geometric interface
records Lemma 13.2, including the intersection and the noninner action.
The remaining interfaces separate Lemmas 13.3–13.4 from the numerical facts
about actual unitary covers used in the last paragraph of Section 13.

These are propositions to be proved, not claims that the source results
are available. `UnitaryExclusion` retains their final discharge.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Section 13, and Chapter 4, 3.4–3.6.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source's second distinguished centralizer, for a subgroup rather
than a single element. Its normality is relative to that centralizer. -/
@[expose] public def distinguishedCentralizer (Z : Set G) (B : Subgroup G) : Subgroup G :=
  closure (Z ∩ (centralizer (B : Set G) : Set G))

/-- The cyclic subgroup and second centralizer of Lemma 13.2. We use `B`
for the cyclic group, reserving `A` for the distinguished subgroup in `M`. -/
public structure SecondCentralizerData
    (Z : Set G) (M : Subgroup G) (z t u : G) (n : ℕ) where
  torus : Subgroup G
  cyclic : IsCyclic torus
  card_torus : Nat.card torus = 2 ^ n + 1 ∨ Nat.card torus = (2 ^ n + 1) / 3
  torus_le_local : torus ≤ centralizerClosure Z u
  torus_le_pair : torus ≤ residualPairStabilizer M t
  torus_centralizes : torus ≤ centralizer (residualGenerated M z t : Set G)
  local_torus_centralizer : centralizerClosure Z u ⊓ centralizer (torus : Set G) =
    residualGenerated M z t ⊔ torus
  second_cover : IsUnitaryCentralizerCoverAt n (distinguishedCentralizer Z torus)
  intersection : distinguishedCentralizer Z torus ⊓ centralizerClosure Z u =
    residualGenerated M z t
  fixed : distinguishedCentralizer Z torus ⊓ centralizer ({u} : Set G) =
    residualGenerated M z t
  normalizes : u ∈ normalizer (distinguishedCentralizer Z torus : Set G)
  noninner : ¬ ∃ a ∈ distinguishedCentralizer Z torus,
    ∀ x ∈ distinguishedCentralizer Z torus, MulAut.conj u x = MulAut.conj a x

/-- The consequence of Lemma 13.3 actually consumed by conjugation on `Lᵤ`.
It bounds every two-subgroup of the literal ambient centralizer. -/
@[expose] public def CentralizerTwoBound (Z : Set G) (u : G) : Prop :=
  ∀ P : Subgroup G, P ≤ centralizer (centralizerClosure Z u : Set G) →
    IsPGroup 2 P → Nat.card P ≤ 2

/-- The subgroup constructed as `T₀U` after Lemma 13.4. Its producer must
construct the commuting homocyclic subgroups, their common involutions and
their product; these rank and order fields are not source assumptions. -/
public structure LargeAbelianData (M : Subgroup G) (n : ℕ) where
  subgroup : Subgroup G
  le_pointStabilizer : subgroup ≤ M
  two_group : IsPGroup 2 subgroup
  abelian : IsMulCommutative subgroup
  rank : primeRank 2 subgroup = 2 * n
  card : Nat.card subgroup = (2 ^ n) ^ 3

/-- Only the two intrinsic automorphism facts used by the endgame. This
contract concerns the actual special or projective cover, never a family tag. -/
public structure AutomorphismBounds (H : Type u) [Group H] (n : ℕ) : Prop where
  rank : primeRank 2 (MulAut H) ≤ n + 1
  exceptional_order : n = 2 → ∀ B : Subgroup (MulAut H),
    IsPGroup 2 B → IsMulCommutative B → 3 ≤ primeRank 2 B → Nat.card B ≤ 16

end BenderSuzuki.ZD.UnitaryExclusion
