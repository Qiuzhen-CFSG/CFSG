module

public import Theory.GroupTheory.CComponent.ThreeResidual

/-!
# The inner-action obstruction for a triple cover

Let L be normal in a finite group of three-rank at most two. Suppose L
contains an elementary nine, its center has exponent dividing three,
its outer automorphism group is a two-group, and L has no element of
order nine. Every ambient element killed by three then belongs to L.

An order-three automorphism is inner. Its implementing element has cube
in the center, hence ninth power one and therefore cube one. Dividing
by it leaves a centralizing element killed by three. If this element
were outside L, it would enlarge the elementary nine to an elementary
27, contradicting the rank bound.

This isolates the exceptional-cover argument in Aschbacher–Smith,
combined manuscript (1 March 2004), A.3.18, printed pp.51–52.
-/

public section

open Subgroup
namespace Theory.GroupTheory.HexacodeTheta

private theorem elementaryNine_of_rank {G : Type*} [Group G] [Finite G]
    (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let _ := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

/-- The exponent-three obstruction excludes outside order-three actors. -/
theorem order_three_mem_of_normal {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal]
    (hz : ∀ z ∈ center L, z ^ 3 = 1)
    (hexp : ∀ z : L, z ^ 9 = 1 → z ^ 3 = 1)
    (ho : IsPGroup 2 (MulAut.Outer L))
    (hrL : 2 ≤ primeRank 3 L) (hr : primeRank 3 G ≤ 2)
    {x : G} (hx : x ^ 3 = 1) : x ∈ L := by
  let a : MulAut L := MulAut.conjNormal x
  let q := QuotientGroup.mk' (MulAut.innerSubgroup L)
  have ha : a ^ 3 = 1 := by
    change MulAut.conjNormal x ^ 3 = 1
    rw [← map_pow, hx, map_one]
  have hq : q a = 1 := by
    apply (ho.powEquiv (by decide : Nat.Coprime 2 3)).injective
    change q a ^ 3 = (1 : MulAut.Outer L) ^ 3
    rw [← map_pow, ha, map_one, one_pow]
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff a).mp hq
  have hlc : l ^ 3 ∈ center L := by
    have he : MulAut.conj (l ^ 3) = 1 := by rw [map_pow, hl, ha]
    apply mem_center_iff.mpr
    intro z
    have hh := MulEquiv.congr_fun he z
    change l ^ 3 * z * (l ^ 3)⁻¹ = z at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hl3 : l ^ 3 = 1 := hexp l (by
    simpa only [← pow_mul] using hz (l ^ 3) hlc)
  let c : G := x * (l : G)⁻¹
  have hc : c ∈ centralizer (L : Set G) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer L]
    change MulAut.conjNormal (x * (l : G)⁻¹) = 1
    rw [map_mul, map_inv, MulAut.conjNormal_val, hl]
    exact mul_inv_cancel a
  have hcl : Commute c (l : G) :=
    (mem_centralizer_iff.mp hc l l.property).symm
  have hclx : c * (l : G) = x := by simp [c, mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have he := hcl.mul_pow 3
    have hlG : (l : G) ^ 3 = 1 := congrArg Subtype.val hl3
    rw [hclx, hx, hlG, mul_one] at he
    exact he.symm
  by_contra hxL
  have hcL : c ∉ L := by
    intro hh
    exact hxL (hclx ▸ L.mul_mem hh l.property)
  have hcne : c ≠ 1 := fun he => hcL (he ▸ L.one_mem)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hcne
  obtain ⟨A, hA, hcard⟩ := elementaryNine_of_rank hrL
  let _ := hA
  let E := A.map L.subtype
  let _ : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  have hEL : E ≤ L := map_subtype_le A
  have hfix : E ≤ centralizer ({c} : Set G) := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc z (hEL hz))
  have hcardE : Nat.card E = 3 ^ 2 := by
    simpa only [E, card_map_of_injective L.subtype_injective] using hcard
  have hbad := IsElementaryAbelian.primeRank_ge_of_fixed_join E c hco
    (fun h => hcL (hEL h)) hfix hcardE
  omega

end Theory.GroupTheory.HexacodeTheta
