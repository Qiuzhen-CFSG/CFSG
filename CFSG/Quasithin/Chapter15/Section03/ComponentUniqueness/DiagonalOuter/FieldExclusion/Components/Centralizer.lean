module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Rank

/-!
# Three-elements of a rank-two component centralizer

An element of order three centralizing a subgroup of three-rank two lies
in that subgroup when the ambient three-rank is at most two. Otherwise
it joins an elementary nine to give an elementary subgroup of order 27.
It consequently lies in the embedded odd center. This proves the full
relative-centralizer alternative from the odd-center and cover model facts,
including uniqueness of the subgroup of order three.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
A.3.18, printed p.52, observation (*), applied on p.1137. The model and
odd-center alternatives remain explicit inputs here.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion

theorem centralizing_three_mem {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hrank : primeRank 3 G ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    {x : G} (hx : orderOf x = 3) (hc : x ∈ centralizer (K : Set G)) : x ∈ K := by
  by_contra hnot
  obtain ⟨E, he, hcard⟩ := CoverReduction.LocalCover.exists_elementary_nine hKrank
  let := he
  let A := E.map K.subtype
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map _
  have ha : Nat.card A = 3 ^ 2 :=
    (Nat.card_congr (equivMapOfInjective E _ K.subtype_injective).toEquiv).symm.trans hcard
  have hfix : A ≤ centralizer ({x} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hc a (map_subtype_le _ ha))
  have hb := IsElementaryAbelian.primeRank_ge_of_fixed_join A x hx
    (fun ha => hnot (map_subtype_le _ ha)) hfix ha
  omega

theorem centralizing_three_mem_oddCenter {G : Type*} [Group G]
    {K : Subgroup G} {x : G} (hx : orderOf x = 3)
    (hxK : x ∈ K) (hc : x ∈ centralizer (K : Set G)) : x ∈ oddCenterIn K := by
  let z : center K := ⟨⟨x, hxK⟩, mem_center_iff.mpr
    (fun k => Subtype.ext (hc k k.property))⟩
  have hz : orderOf z = 3 := by
    simpa only [z, Subgroup.orderOf_mk] using hx
  have hp : Nat.Coprime 2 (Nat.card (zpowers z)) := by
    rw [Nat.card_zpowers, hz]
    decide
  have hle : zpowers z ≤ pPrimeCore 2 (center K) := le_sSup ⟨inferInstance, hp⟩
  exact mem_map.mpr ⟨z, hle (mem_zpowers z), rfl⟩

theorem relative_centralizing_three_mem_oddCenter
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hrank : primeRank 3 H ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    {x : G} (hx : orderOf x = 3) (hxH : x ∈ H)
    (hc : x ∈ centralizer (K : Set G)) : x ∈ oddCenterIn K := by
  have hk : 2 ≤ primeRank 3 (K.subgroupOf H) := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hKH)]
    exact hKrank
  have hxc : (⟨x, hxH⟩ : H) ∈ centralizer (K.subgroupOf H : Set H) := by
    intro k hk
    exact Subtype.ext (hc k hk)
  have hxo : orderOf (⟨x, hxH⟩ : H) = 3 := by
    simpa only [Subgroup.orderOf_mk] using hx
  have hxK : x ∈ K := centralizing_three_mem hrank hk hxo hxc
  exact centralizing_three_mem_oddCenter hx hxK hc


theorem oddCenterIn_le_relative_centralizer
    {G : Type*} [Group G] {H K : Subgroup G} (hKH : K ≤ H) :
    oddCenterIn K ≤ H ⊓ centralizer (K : Set G) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨hKH z.val.property, ?_⟩
  intro k hk
  exact congrArg Subtype.val (mem_center_iff.mp z.property ⟨k, hk⟩)

theorem order_three_subgroup_le_oddCenter
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hrank : primeRank 3 H ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    (P : Subgroup G) (hP : P ≤ H ⊓ centralizer (K : Set G)) (hc : Nat.card P = 3) :
    P ≤ oddCenterIn K := by
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  have hxo : orderOf (⟨x, hx⟩ : P) = 3 := by
    have hd : orderOf (⟨x, hx⟩ : P) ∣ 3 := hc ▸ orderOf_dvd_natCard _
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact (hx1 (congrArg Subtype.val (orderOf_eq_one_iff.mp h))).elim
    · exact h
  apply relative_centralizing_three_mem_oddCenter hKH hrank hKrank
    (show orderOf x = 3 by simpa only [Subgroup.orderOf_mk] using hxo)
    (hP hx).1 (hP hx).2

theorem centralizer_prime_to_three_of_oddCenter
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hrank : primeRank 3 H ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    (hc : Nat.Coprime 3 (Nat.card (oddCenterIn K))) :
    Nat.Coprime 3 (Nat.card (H ⊓ centralizer (K : Set G) : Subgroup G)) := by
  apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ centralizer (K : Set G))) 3 hd
  have hxo : orderOf (x : G) = 3 :=
    (orderOf_injective (H ⊓ centralizer (K : Set G)).subtype Subtype.val_injective x).trans hx
  have hxZ := relative_centralizing_three_mem_oddCenter hKH hrank hKrank hxo
    x.property.1 x.property.2
  have hz : orderOf (⟨(x : G), hxZ⟩ : oddCenterIn K) = 3 := by
    simpa only [Subgroup.orderOf_mk] using hxo
  have hdiv : 3 ∣ Nat.card (oddCenterIn K) := hz ▸ orderOf_dvd_natCard _
  exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hc) hdiv

theorem unique_order_three_subgroup_of_oddCenter
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hrank : primeRank 3 H ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    (hc : Nat.card (oddCenterIn K) = 3)
    (P : Subgroup G) (hP : P ≤ H ⊓ centralizer (K : Set G)) (hPc : Nat.card P = 3) :
    P = oddCenterIn K := by
  exact eq_of_le_of_card_ge (order_three_subgroup_le_oddCenter hKH hrank hKrank P hP hPc)
    (by omega)

theorem fieldComponentCentralizerAlternative_of_oddCenter
    {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hrank : primeRank 3 H ≤ 2) (hKrank : 2 ≤ primeRank 3 K)
    (hmodel : Nat.Coprime 3 (Nat.card (oddCenterIn K)) ∨
      (ExceptionalFieldCover K ∧ Nat.card (oddCenterIn K) = 3)) :
    FieldComponentCentralizerAlternative H K := by
  rcases hmodel with hc | ⟨hcover, hc⟩
  · exact Or.inl (centralizer_prime_to_three_of_oddCenter hKH hrank hKrank hc)
  · exact Or.inr ⟨hcover, hc, oddCenterIn_le_relative_centralizer hKH,
      unique_order_three_subgroup_of_oddCenter hKH hrank hKrank hc⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
