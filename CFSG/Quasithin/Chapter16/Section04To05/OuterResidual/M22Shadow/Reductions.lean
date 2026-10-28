module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.Setup
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Two ambient obstructions in the M₂₂ shadow argument

A subgroup lying in both L′ and C_G(L′) embeds in the cyclic center of
L′, and therefore has two-rank at most one. This supplies the contradiction
in the R₀ argument once its two core placements have been proved.

An outer automorphism cannot be induced by an element of the derived
normalizer when the outer group is abelian. Consequently the covered M₂₂
case with center C₄ is impossible once symmetry and the covering calculation
put z in [Q,Q]. These are conditional steps, not a proof of symmetry or of
Lemma 16.4.7. The core placements, cover calculation, and action construction
remain obligations of the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed p.1186.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

private theorem rank_le_one_of_cyclic_center [Finite G]
    (Q L : Subgroup G) [IsCyclic (center L)]
    (hQ : Q ≤ L) (hC : Q ≤ centralizer (L : Set G)) : primeRank 2 Q ≤ 1 := by
  let f : Q →* center L := {
    toFun q := ⟨⟨q, hQ q.property⟩, mem_center_iff.mpr (fun l =>
      Subtype.ext (mem_centralizer_iff.mp (hC q.property) l l.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun c : center L => (c.val : G)) hab)
  let : IsCyclic Q := isCyclic_of_injective f hf
  let P : Sylow 2 Q := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic inferInstance

/-- The rank-three core cannot lie in both L′ and K′ when Z(L′) is cyclic.
The M₂₂ covering calculation supplies the rank premise in either cover case. -/
theorem residualCore_not_le_centralizer [Finite G]
    (L L' : Subgroup G) (r : G) [IsCyclic (center L')]
    (hrank : 3 ≤ primeRank 2 (residualCore L r))
    (hL' : residualCore L r ≤ L') :
    ¬ residualCore L r ≤ centralizer (L' : Set G) := by
  intro hC
  have hh := rank_le_one_of_cyclic_center (residualCore L r) L' hL' hC
  omega

/-- Abelian outer automorphism groups kill the derived normalizer under the
actual conjugation action. Normality here is relative to the normalizer. -/
theorem outer_not_mem_normalizer_commutator
    (L : Subgroup G) [IsMulCommutative (MulAut.Outer L)]
    {x : G} (hx : x ∈ normalizer (L : Set G))
    (ho : L.normalizerMonoidHom ⟨x, hx⟩ ∉ MulAut.innerSubgroup L) :
    x ∉ ⁅normalizer (L : Set G), normalizer (L : Set G)⁆ := by
  intro hd
  rw [← map_subtype_commutator] at hd
  obtain ⟨y, hy, he⟩ := hd
  let f : normalizer (L : Set G) →* MulAut.Outer L :=
    (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp L.normalizerMonoidHom
  have hf : f y = 1 := Abelianization.commutator_subset_ker f hy
  have hi : L.normalizerMonoidHom y ∈ MulAut.innerSubgroup L :=
    (QuotientGroup.eq_one_iff _).mp hf
  have hyx : y = ⟨x, hx⟩ := Subtype.ext he
  exact ho (hyx ▸ hi)

/-- The C₄-center contradiction after symmetry is established. The conditional
commutator membership is the exact cover fact used from I.2.2(6a), rather
than an assumed exclusion of that cover. -/
theorem center_card_ne_four_of_outer_symmetry
    (L L' : Subgroup G) (r z : G)
    (hz : z ∈ normalizer (L' : Set G))
    (hout : L'.normalizerMonoidHom ⟨z, hz⟩ ∉ MulAut.innerSubgroup L')
    (houter : Nat.card (MulAut.Outer L') = 2)
    (hQ : residualCore L r ≤ normalizer (L' : Set G))
    (hcover : Nat.card (center L) = 4 → z ∈ ⁅residualCore L r, residualCore L r⁆) :
    Nat.card (center L) ≠ 4 := by
  let : IsCyclic (MulAut.Outer L') := isCyclic_of_prime_card houter
  let : IsMulCommutative (MulAut.Outer L') := inferInstance
  intro hfour
  exact outer_not_mem_normalizer_commutator L' hz hout
    ((commutator_mono hQ hQ) (hcover hfour))

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
