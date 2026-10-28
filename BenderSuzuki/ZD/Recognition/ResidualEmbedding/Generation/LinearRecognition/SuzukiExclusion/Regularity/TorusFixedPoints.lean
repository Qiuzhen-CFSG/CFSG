module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.SourceSylow
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Regularity.TorusFixedPoints.PrimeWeakClosure

/-!
# Assembly of the torus fixed-point argument

Every nonidentity element of the residual torus fixes exactly the two
distinguished cosets. `Reduction` supplies prime-order extraction, invariant
Sylow selection and the final rank-one normalizer action. `SourceSylow`
proves the fixed-intersection identity (12G) and promotes the local Sylow
subgroup to an ambient Sylow subgroup. `PrimeWeakClosure` proves (12H)
using the centralizing branch and the elementary-plane coprime-generation
contradiction. Their assembly below discharges every extra premise of the
fixed-point argument.

Source: GLS4, Chapter 2, Proposition 12.13,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2290–2320.
-/

namespace BenderSuzuki.ZD.SuzukiExclusion
open Theory.GroupTheory PFAppendixIII Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Connect the independent (12G) and (12H) producers to the literal coset conclusion. -/
public theorem Context.torus_semiregular_of_sylowData (d : Context Z M z t m)
    (hSylow : ∀ (p : ℕ), p.Prime → ∀ x ∈ residualCommutator M t,
      orderOf x = p → Nonempty (TorusSylowData M t x p))
    (hweak : ∀ (p : ℕ), p.Prime → ∀ x ∈ residualCommutator M t,
      orderOf x = p → ∀ S : TorusSylowData M t x p,
        ∀ g : G, rightConjugateElem x g ∈ (S.P : Subgroup G) →
          g ∈ normalizer (zpowers x : Set G)) : TorusSemiregular M t := by
  apply d.torus_semiregular_of_weakClosure
  intro p hp x hx hxorder
  obtain ⟨S⟩ := hSylow p hp x hx hxorder
  exact ⟨S.P, S.le_pair, hweak p hp x hx hxorder S⟩

/-- Proposition 12.13: every nonidentity torus element fixes exactly the two
distinguished cosets in the actual quotient action. -/
public theorem Context.torus_semiregular (d : Context Z M z t m) :
    TorusSemiregular M t := by
  apply d.torus_semiregular_of_sylowData
  · intro p hp x hx hxorder
    exact d.exists_torusSylowData hx hp hxorder
  · intro p hp x hx hxorder S
    exact d.torus_prime_weakClosure hx hp hxorder S

end BenderSuzuki.ZD.SuzukiExclusion
