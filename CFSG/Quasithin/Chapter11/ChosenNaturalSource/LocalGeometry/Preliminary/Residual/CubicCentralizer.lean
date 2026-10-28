module
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Centralizer obstructions for the nonfaithful D.3.9 actor

A cubic centralizing a component of full three-rank lies in that component.
It therefore cannot be moved by a second subgroup centralizing the component.
If the component centre has order at most three, a commuting perfect subgroup
has order prime to three: first bound its three-rank by one, then use cyclic
Sylow transfer and rank addition. All centres and relative subgroups are retained.

These local arguments exclude the cubic alternative of D.3.9(2b), and the
component alternative of (2a) when its produced component has a cubic.
Multiplicity.ActorKernel applies both to the original chosen full-orbit action.
They do not construct D.3.9's actor or establish a bound on natural multiplicity.
Source: Aschbacher--Smith D.3.9, printed pp.199--201, and A.3.20, p.55,
in the preliminary argument for 11.0.4, p.760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
namespace CubicCentralizer
variable {H : Type*} [Group H] [Finite H]

/-- In three-rank two, a cubic centralizing a full-rank subgroup belongs to it. -/
theorem cubic_mem_of_centralizes (K : Subgroup H)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    {x : H} (hx : x ^ 3 = 1) (hc : x ∈ centralizer (K : Set H)) : x ∈ K := by
  by_contra hn
  have hx1 : x ≠ 1 := fun he => hn (he ▸ K.one_mem)
  have hKeq : primeRank 3 K = 2 := le_antisymm
    ((Theory.GroupTheory.primeRank_le_of_injective 3 K.subtype K.subtype_injective).trans hr) hK
  obtain ⟨B,hB,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hB
  let E := B.map K.subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map K.subtype
  have hEL : E ≤ K := map_subtype_le B
  have hE : Nat.card E = 3 ^ 2 := by
    rw [card_map_of_injective K.subtype_injective,hcard,hKeq]
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join E x
    (orderOf_eq_prime hx hx1) (fun he => hn (hEL he))
    (fun e he => mem_centralizer_singleton_iff.mpr (hc e (hEL he))) hE
  omega

/-- The same containment for a subgroup of exponent three. -/
theorem cubicSubgroup_le (K X : Subgroup H)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hX : ∀ x : X, x ^ 3 = 1) (hc : X ≤ centralizer (K : Set H)) : X ≤ K := by
  intro x hx
  exact cubic_mem_of_centralizes K hK hr
    (congrArg Subtype.val (hX ⟨x,hx⟩)) (hc hx)

/-- Two subgroups centralizing the full-rank subgroup commute when one
has exponent three. -/
theorem cubicSubgroup_commutator_eq_bot (K X A : Subgroup H)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hX : ∀ x : X, x ^ 3 = 1) (hXK : X ≤ centralizer (K : Set H))
    (hAK : A ≤ centralizer (K : Set H)) : ⁅X,A⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact le_centralizer_iff.mp
    (hAK.trans (centralizer_le (cubicSubgroup_le K X hK hr hX hXK)))

/-- The moved cyclic-three alternative in D.3.9(2b) contradicts full rank. -/
theorem no_moved_cyclicThree (K X A : Subgroup H)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hcard : Nat.card X = 3) (hXK : X ≤ centralizer (K : Set H))
    (hAK : A ≤ centralizer (K : Set H)) (hm : X = ⁅X,A⁆) : False := by
  have he : X = ⊥ := hm.trans (cubicSubgroup_commutator_eq_bot K X A hK hr
    (fun x => hcard ▸ pow_card_eq_one' (x := x)) hXK hAK)
  rw [he] at hcard
  simp at hcard

/-- The cubic centre is retained: a commuting factor has three-rank at most
one because two rank-two factors could intersect in at most three elements. -/
theorem centralizing_rank_le_one (K J : Subgroup H)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hz : Nat.card (center K) ≤ 3) (hc : J ≤ centralizer (K : Set H)) :
    primeRank 3 J ≤ 1 := by
  let f : (J ⊓ K : Subgroup H) →* center K := {
    toFun x := ⟨⟨x,x.property.2⟩,mem_center_iff.mpr
      (fun k => Subtype.ext (hc x.property.1 k k.property))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center K => ((z : K) : H)) he)
  have hi : Nat.card (J ⊓ K : Subgroup H) ≤ 3 :=
    (Nat.card_le_card_of_injective f hf).trans hz
  by_contra! hn
  have hh := three_le_primeRank_of_cubic_intersection J K hc hi (by omega) hK
  omega

/-- A perfect subgroup centralizing this full-rank component has order prime
to three. Cyclic Sylow transfer excludes three from its centre before rank
addition, so no centre-free hypothesis is imposed on either factor. -/
theorem perfect_centralizer_coprime (K J : Subgroup H) [Group.IsPerfect J]
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hz : Nat.card (center K) ≤ 3) (hc : J ≤ centralizer (K : Set H)) :
    Nat.Coprime 3 (Nat.card J) := by
  have hJ := centralizing_rank_le_one K J hK hr hz hc
  let P : Sylow 3 J := default
  let : IsCyclic P := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hJ
  have hZ : Nat.Coprime 3 (Nat.card (center J)) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    have he := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
      (QuotientGroup.mk' (center J))
      (by rw [QuotientGroup.ker_mk']) P (inferInstance : IsMulCommutative P)
    rwa [QuotientGroup.ker_mk'] at he
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime K J
    (le_centralizer_iff.mp hc) hZ
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  apply PrimeRank.eq_zero_iff_not_dvd_card.mp
  omega

/-- The component alternative in D.3.9(2a) is impossible as soon as its
produced component has a cubic. No normality of that component in H is assumed. -/
theorem no_component_three (K J : Subgroup H) (hJ : IsComponent H J)
    (hK : 2 ≤ primeRank 3 K) (hr : primeRank 3 H ≤ 2)
    (hz : Nat.card (center K) ≤ 3) (hc : J ≤ centralizer (K : Set H))
    (hthree : 3 ∣ Nat.card J) : False := by
  let := hJ.2
  exact Nat.prime_three.coprime_iff_not_dvd.mp
    (perfect_centralizer_coprime K J hK hr hz hc) hthree

end CubicCentralizer
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
