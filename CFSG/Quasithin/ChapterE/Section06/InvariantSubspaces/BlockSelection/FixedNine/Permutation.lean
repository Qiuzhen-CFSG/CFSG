module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements

/-!
# A cubic actor fixes a block when its distinct conjugate commutes

If a chi-zero block commutes with its distinct conjugate by a cubic actor,
choose a three-element a in the block. The conjugates a, aˣ, aˣ² commute.
The first two generate an elementary nine; its conjugate also has order nine
and centralizes the original block. It cannot contain a, because the center
of a short group is a two-group. Adjoining a therefore gives an elementary
subgroup of order twenty-seven, contradicting the ambient three-rank bound.

This proves the permutation restriction needed in the proof of E.6.14
(Aschbacher–Smith, printed p.251/PDF p.262). The separate commutation premise
is to be supplied by C.1.9, with its extra A₃ hypothesis retained.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

theorem normalizes_of_conjugate_commutation {N L : Subgroup G}
    (hLN : L ≤ N) (hrank : primeRank 3 N ≤ 2)
    (hL : ChapterC.IsChiZeroBlock L) {x : G} (hxN : x ∈ N)
    (hx : orderOf x = 3)
    (hcomm : L.map (MulAut.conj x) ≠ L →
      L.map (MulAut.conj x) ≤ centralizer (L : Set G)) :
    x ∈ normalizer (L : Set G) := by
  by_contra hn
  have hc := hcomm (fun he => hn (mem_normalizer_iff_map_conj_eq.mpr he))
  let f : MulAut G := MulAut.conj x
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hf : f ^ 3 = 1 := by
    change (MulAut.conj x) ^ 3 = 1
    rw [← map_pow, hx3, map_one]
  have hf3 (z : G) : f (f (f z)) = z := by
    have h := congrArg (fun a : MulAut G => a z) hf
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using h
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
    apply mem_centralizer_iff.mpr
    intro l hl
    have hh := mem_centralizer_iff.mp (hc (mem_map_of_mem f.toMonoidHom hl))
      a a.property
    have hh' := congrArg (fun z => f (f z)) hh
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, hf3] using hh'.symm
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
