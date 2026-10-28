module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness.TorusFixedPoints.PrimeWeakClosure.Reduction
public import Theory.GroupTheory.PGroup.CyclicPrimeExtensionOrbits

/-!
# Conjugacy of the noncentralizing torus plane's lines

The torus intersection C = K ∩ P is cyclic and is normalized by P, since
P lies in the two-point stabilizer. Apply cyclic prime-extension conjugacy
to C and the actual prime-order elements x and y. This supplies precisely
the orbit premise in the weak-closure reduction, with conjugators in K ∩ P.
The final theorem applies that reduction to its literal Sylow data.

Source: GLS4, Chapter 2, Proposition 12.13, equation (12H),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2305–2320.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- Every element outside the torus line in the noncentralizing plane has
a conjugate in the other line, with conjugator in the actual torus intersection. -/
public theorem Context.torus_noncentralizing_line_orbits
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p)
    {y : G} (hy : y ∈ (S.P : Subgroup G)) (hyorder : orderOf y = p)
    (hnon : ¬ residualCommutator M t ⊓ (S.P : Subgroup G) ≤
      centralizer ({y} : Set G)) :
    ∀ u ∈ (zpowers x ⊔ zpowers y : Subgroup G), u ≠ 1 →
      u ∈ zpowers x ∨ ∃ k ∈ residualCommutator M t ⊓ (S.P : Subgroup G),
        MulAut.conj k u ∈ zpowers y := by
  let : Fact p.Prime := ⟨hp⟩
  let C := residualCommutator M t ⊓ (S.P : Subgroup G)
  let : IsCyclic (residualCommutator M t) := d.torus_structure.2.1
  let : IsCyclic C := Subgroup.isCyclic_of_le (show C ≤ residualCommutator M t from inf_le_left)
  have hC : IsPGroup p C := S.P.isPGroup'.to_le inf_le_right
  have hyC : y ∈ normalizer (C : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    exact and_congr
      (mem_normalizer_iff.mp (d.pair_normalizes_torus (S.le_pair hy)) a)
      (mem_normalizer_iff.mp ((S.P : Subgroup G).le_normalizer hy) a)
  intro u hu _
  exact C.cyclic_prime_extension_orbits hC ⟨hx, S.mem⟩
    (hxorder ▸ pow_orderOf_eq_one x) hyC hyorder hnon hu

/-- The line-orbit theorem discharges the sole extra premise of the (12H) reduction. -/
public theorem Context.torus_prime_weakClosure_via_cyclic_extension
    {x : G} (hx : x ∈ residualCommutator M t) {p : ℕ} (hp : p.Prime)
    (hxorder : orderOf x = p) (S : TorusSylowData M t x p) :
    ∀ g : G, rightConjugateElem x g ∈ (S.P : Subgroup G) →
      g ∈ normalizer (zpowers x : Set G) := by
  apply d.torus_prime_weakClosure_of_plane_orbits hx hp hxorder S
  intro y hy hyorder hnon
  exact d.torus_noncentralizing_line_orbits hx hp hxorder S hy hyorder hnon

end BenderSuzuki.ZD.LinearExclusion
