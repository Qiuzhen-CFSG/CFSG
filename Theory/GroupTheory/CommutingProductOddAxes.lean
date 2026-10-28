module
public import Theory.GroupTheory.OddCentralizerProduct
/-!
# Odd quotient axes in commuting products

An odd subgroup in one quotient axis lies in the corresponding actual factor
when the kernel in the other commuting factor has exponent two. Decompose
inside the commuting product and take square roots in the odd subgroup to
remove that kernel component. The relative version retains the literal map
from the prescribed ambient join.

The original torus-axis application is Aschbacher--Smith 10.2.3(4), p.746.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]
/-- An odd quotient axis lifts into the actual commuting factor. -/
theorem odd_subgroup_le_commuting_factor_of_quotient_axis
    (L K P : Subgroup G) [Finite P] (hodd : Odd (Nat.card P))
    (hcomm : K ≤ centralizer (L : Set G)) (hgen : L ⊔ K = ⊤)
    (q : G →* A) (hLq : L ≤ q.ker) (hPq : P ≤ q.ker)
    (hcore : ∀ k ∈ K ⊓ q.ker, k ^ 2 = 1) : P ≤ L := by
  let E := K ⊓ q.ker
  apply odd_subgroup_le_of_commuting_square_one_factor L E P hodd
    (inf_le_left.trans hcomm) hcore
  intro x hx
  have hm : x ∈ (L : Set G) * K := by
    rw [←coe_mul_of_right_le_normalizer_left L K
      (hcomm.trans (centralizer_le_normalizer _)),hgen]
    trivial
  obtain ⟨l,hl,k,hk,rfl⟩ := hm
  have hqk : k ∈ q.ker := by
    have hh := hPq hx
    change q (l*k)=1 at hh
    rw [map_mul,show q l=1 from hLq hl,one_mul] at hh
    exact hh
  exact (L ⊔ E).mul_mem ((show L ≤ L ⊔ E from le_sup_left) hl) ((show E ≤ L ⊔ E from le_sup_right) ⟨hk,hqk⟩)
end Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]
/-- The same lift with the original map on a specified join retained. -/
theorem odd_subgroup_le_commuting_factor_of_relative_axis
    (L K P R : Subgroup G) [Finite G] (hodd : Odd (Nat.card P))
    (hcomm : K ≤ centralizer (L : Set G)) (hgen : L ⊔ K = R)
    (hPR : P ≤ R) (q : R →* A)
    (hLq : ∀ l : L, q ⟨l,hgen ▸ (show L ≤ L ⊔ K from le_sup_left) l.property⟩ = 1)
    (hPq : ∀ p : P, q ⟨p,hPR p.property⟩ = 1)
    (hcore : ∀ k : K,
      q ⟨k,hgen ▸ (show K ≤ L ⊔ K from le_sup_right) k.property⟩ = 1 → (k:G)^2=1) :
    P ≤ L := by
  have hLR : L ≤ R := hgen ▸ le_sup_left
  have hKR : K ≤ R := hgen ▸ le_sup_right
  have hgen' : L.subgroupOf R ⊔ K.subgroupOf R = ⊤ := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLR,map_subgroupOf_eq_of_le hKR,
      ←MonoidHom.range_eq_map,range_subtype,hgen]
  have hc : K.subgroupOf R ≤ centralizer (L.subgroupOf R : Set R) := by
    intro k hk l hl
    exact Subtype.ext (hcomm hk l hl)
  have hp := odd_subgroup_le_commuting_factor_of_quotient_axis
    (L.subgroupOf R) (K.subgroupOf R) (P.subgroupOf R)
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hPR).toEquiv]) hc hgen' q
    (fun l hl => hLq ⟨l,hl⟩) (fun p hp => hPq ⟨p,hp⟩) (fun k hk =>
      Subtype.ext (hcore ⟨k,hk.1⟩ hk.2))
  intro p hpP
  exact hp (show (⟨p,hPR hpP⟩ : R) ∈ P.subgroupOf R from hpP)
end Subgroup
