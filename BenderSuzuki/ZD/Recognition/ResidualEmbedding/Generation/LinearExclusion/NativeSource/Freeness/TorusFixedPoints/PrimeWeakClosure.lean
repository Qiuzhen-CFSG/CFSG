module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints.PrimeWeakClosure.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints.PrimeWeakClosure.PlaneOrbits

/-!
# Prime torus weak closure

`PrimeWeakClosure.Reduction` proves the centralizing branch of (12H),
its centralizer-Sylow adjustment, the elementary plane of order p²,
and the coprime-generation contradiction for that plane. The cyclic-extension
line-orbit theorem discharges the remaining premise of that reduction.
Thus every conjugator taking the prime torus element into the supplied
ambient Sylow subgroup normalizes its cyclic subgroup. Applying the
rank-one normalizer argument gives its exact two fixed cosets.

Only the source Sylow data (12G) remain explicit. Their existence and the
final assembly of Proposition 12.13 belong to `TorusFixedPoints`.

Source: GLS4, Chapter 2, Proposition 12.13, equation (12H),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2305--2320.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- Equation (12H): the prime torus line is weakly closed in the supplied ambient Sylow subgroup. -/
public theorem Context.torus_prime_weakClosure
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p) :
    ∀ g : G, rightConjugateElem x g ∈ (S.P : Subgroup G) →
      g ∈ normalizer (zpowers x : Set G) := by
  apply d.torus_prime_weakClosure_of_plane_orbits hx hp hxorder S
  intro y hy hyorder hnon
  exact d.torus_noncentralizing_line_orbits hx hp hxorder S hy hyorder hnon

/-- Weak closure gives the exact fixed cosets of the prime torus element, conditional only on (12G). -/
public theorem Context.torus_fixedPoints_of_sylowData
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p) :
    ∀ beta : G ⧸ M, x • beta = beta ↔
      beta = QuotientGroup.mk 1 ∨ beta = QuotientGroup.mk t :=
  d.torus_fixedPoints_of_weakClosure hx hp hxorder S.P S.le_pair
    (d.torus_prime_weakClosure hx hp hxorder S)

end BenderSuzuki.ZD.LinearExclusion
