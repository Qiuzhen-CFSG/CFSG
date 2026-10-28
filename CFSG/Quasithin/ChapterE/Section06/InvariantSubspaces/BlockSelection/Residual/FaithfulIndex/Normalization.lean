module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements

/-!
# Three-power actors normalize a block in three-rank at most two

Suppose distinct conjugates of the block under a three-power actor commute.
If the actor moves the block, its square also moves it, since two is prime
to its order. Three conjugates of a three-element then give an elementary
group of order twenty-seven: two generate a nine centralizing the original
block, whose center has order prime to three. This contradicts the rank bound.

This extends the cubic-actor argument in `FixedNine.Permutation` to the
whole Sylow three-subgroup, without assuming that it normalizes the block.
The commutation premise remains explicit for the owner of C.1.9.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9 and
the proof of E.6.14, printed pp.123 and 251.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- Commuting distinct conjugates and the rank bound force a three-power actor
to normalize the block. -/
theorem normalizes_threePower_of_conjugate_commutation {N L : Subgroup G}
    (hLN : L ≤ N) (hrank : primeRank 3 N ≤ 2)
    (hL : ChapterC.IsChiZeroBlock L) {x : G} (hxN : x ∈ N)
    (hx : ∃ k, orderOf x ∣ 3 ^ k)
    (hcomm : ∀ y ∈ zpowers x, L.map (MulAut.conj y) ≠ L →
      L.map (MulAut.conj y) ≤ centralizer (L : Set G)) :
    x ∈ normalizer (L : Set G) := by
  by_contra hn
  have hc := hcomm x (mem_zpowers x) (fun he => hn (mem_normalizer_iff_map_conj_eq.mpr he))
  let f : MulAut G := MulAut.conj x
  have hn2 : x ^ 2 ∉ normalizer (L : Set G) := by
    intro hx2
    obtain ⟨k, hk⟩ := hx
    have hcop : Nat.Coprime 2 (orderOf x) :=
      ((by decide : Nat.Coprime 2 3).pow_right k).coprime_dvd_right hk
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    exact hn (hm ▸ (normalizer (L : Set G)).pow_mem hx2 m)
  have hc2 := hcomm (x ^ 2) (pow_mem (mem_zpowers x) 2)
    (fun he => hn2 (mem_normalizer_iff_map_conj_eq.mpr he))
  obtain ⟨a, ha⟩ := exists_order_three hL
  have haG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  have hbG : orderOf (f a) = 3 := (f.orderOf_eq a).trans haG
  have hbL : f a ∈ L.map f.toMonoidHom := mem_map_of_mem _ a.property
  obtain ⟨hE₀, hcard₀⟩ := nine_of_commuting_threes hL.chi.short hc
    a.property hbL haG hbG
  let E₀ : Subgroup G := zpowers (a : G) ⊔ zpowers (f a)
  let E : Subgroup G := E₀.map f.toMonoidHom
  let : IsElementaryAbelian 3 E₀ := hE₀
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map f.toMonoidHom
  have hcard : Nat.card E = 3 ^ 2 :=
    (Nat.card_congr (f.subgroupMap E₀).toEquiv).symm.trans hcard₀
  have hbC : f a ∈ centralizer (L : Set G) := hc hbL
  have hcC : f (f a) ∈ centralizer (L : Set G) := by
    have hm := hc2 (mem_map_of_mem (MulAut.conj (x ^ 2)).toMonoidHom a.property)
    change (MulAut.conj (x ^ 2)) (a : G) ∈ centralizer (L : Set G) at hm
    simpa only [f, MulAut.conj_apply, pow_two, mul_inv_rev, mul_assoc] using hm
  have hEC : E ≤ centralizer (L : Set G) := by
    change (zpowers (a : G) ⊔ zpowers (f a)).map f.toMonoidHom ≤ _
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hbC) (zpowers_le.mpr hcC)
  have haE : (a : G) ∉ E := by
    intro hm
    apply not_mem_center_of_order_three hL.chi.short ha
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp (hEC hm) l l.property)
  have hfix : E ≤ centralizer ({(a : G)} : Set G) := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hEC he) a a.property).symm
  obtain ⟨hJ, hJcard⟩ := IsElementaryAbelian.fixed_join_card E (a : G) haG
    (E.disjoint_zpowers_of_prime_order_not_mem a haG haE) hfix hcard
  have hfN : ∀ z ∈ N, f z ∈ N := fun z hz =>
    N.mul_mem (N.mul_mem hxN hz) (N.inv_mem hxN)
  have hEN : E ≤ N := by
    apply map_le_iff_le_comap.mpr
    exact sup_le (zpowers_le.mpr (hfN a (hLN a.property)))
      (zpowers_le.mpr (hfN (f a) (hfN a (hLN a.property))))
  have hJN : E ⊔ zpowers (a : G) ≤ N :=
    sup_le hEN (zpowers_le.mpr (hLN a.property))
  let := hJ
  let : IsElementaryAbelian 3 ((E ⊔ zpowers (a : G)).subgroupOf N) :=
    IsElementaryAbelian.subgroupOf hJN
  have hbound := IsElementaryAbelian.primeRank_ge_of_card
    ((E ⊔ zpowers (a : G)).subgroupOf N)
    ((Nat.card_congr (subgroupOfEquivOfLe hJN).toEquiv).trans hJcard)
  omega

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
