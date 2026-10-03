module
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Normalizers of four subgroups with a central involution

Let `U` be a Klein four subgroup containing a nonidentity central element `z`,
and let `b` be another nonidentity element of `U`. If `C(b)` is contained in
`U` and `U` is properly contained in its normalizer, then `[N(U):U] = 2`.
No finiteness assumption on the ambient group is needed.

Conjugation by the normalizer fixes `z` and permutes `b` and `z*b`. The
centralizer hypothesis identifies the elements fixing `b` with `U`. An
element outside `U` swaps these two involutions, so multiplying by it brings
every other normalizer element into `U`. The two-coset criterion proves the
index. This is the elementary normalizer argument used for ABG Chapter II,
§1, Lemma 1(ii), article page 9; the result itself is independent of the
quasi-dihedral presentation.
-/

namespace Subgroup
variable {G : Type*} [Group G]

private theorem four_cases (U : Subgroup G) [IsKleinFour U]
    (z b : G) (hz : z ∈ U) (hb : b ∈ U) (hz1 : z ≠ 1) (hb1 : b ≠ 1) (hbz : b ≠ z)
    {x : G} (hx : x ∈ U) : x = 1 ∨ x = z ∨ x = b ∨ x = z * b := by
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  by_cases hxb : x = b
  · exact Or.inr (Or.inr (Or.inl hxb))
  right; right; right
  exact congrArg (fun y : U => (y : G))
    (IsKleinFour.eq_mul_of_ne_all (x := (⟨z,hz⟩ : U)) (y := (⟨b,hb⟩ : U))
      (z := (⟨x,hx⟩ : U)) (by simpa using hz1) (by simpa using hb1)
      (by simpa using hbz.symm) (by simpa using hx1) (by simpa using hxz)
      (by simpa using hxb))

private theorem index_of_swap (U : Subgroup G) [IsKleinFour U] (z b t : G)
    (hz : z ∈ U) (hb : b ∈ U) (hz1 : z ≠ 1) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hzc : z ∈ Subgroup.center G)
    (hC : Subgroup.centralizer ({b} : Set G) ≤ U)
    (ht : t ∈ Subgroup.normalizer (U : Set G)) (htb : t*b*t⁻¹ = z*b) :
    U.relIndex (Subgroup.normalizer (U : Set G)) = 2 := by
  let N := Subgroup.normalizer (U : Set G)
  have hzconj (g : G) : g*z*g⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hzc g, mul_assoc, mul_inv_cancel, mul_one]
  have hz2 : z*z = 1 := congrArg (fun y : U => (y : G)) (IsKleinFour.mul_self (⟨z,hz⟩ : U))
  have hUC : U ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    let : IsMulCommutative U := IsKleinFour.isMulCommutative
    exact congrArg (fun y : U => (y : G)) (mul_comm' (⟨x,hx⟩ : U) (⟨b,hb⟩ : U))
  have htout : t ∉ U := by
    intro htU
    have htcomm := Subgroup.mem_centralizer_singleton_iff.mp (hUC htU)
    have he : z*b = b := by rw [← htb, htcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hz1 (mul_right_cancel (b := b) (by simpa using he))
  change (U.subgroupOf N).index = 2
  apply Subgroup.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨⟨t,ht⟩, htout, ?_⟩
  intro g
  have hgb : (g : G)*b*(g : G)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp g.property b).mp hb
  have hne1 : (g : G)*b*(g : G)⁻¹ ≠ 1 := by
    intro he
    have he' : MulAut.conj (g : G) b = MulAut.conj (g : G) 1 := by simpa using he
    exact hb1 ((MulAut.conj (g : G)).injective he')
  have hnez : (g : G)*b*(g : G)⁻¹ ≠ z := by
    intro he
    have he' : MulAut.conj (g : G) b = MulAut.conj (g : G) z := by
      change (g:G)*b*(g:G)⁻¹ = (g:G)*z*(g:G)⁻¹
      rw [he, hzconj]
    exact hbz ((MulAut.conj (g : G)).injective he')
  rcases four_cases U z b hz hb hz1 hb1 hbz hgb with h | h | h | h
  · exact (hne1 h).elim
  · exact (hnez h).elim
  · right
    apply hC
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (mul_inv_eq_iff_eq_mul.mp h)
  · left
    apply hC
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change (t*(g:G))*b*(t*(g:G))⁻¹ = b
    calc
      (t*(g:G))*b*(t*(g:G))⁻¹ = t*((g:G)*b*(g:G)⁻¹)*t⁻¹ := by group
      _ = t*(z*b)*t⁻¹ := by rw [h]
      _ = (t*z*t⁻¹)*(t*b*t⁻¹) := by group
      _ = z*(z*b) := by rw [hzconj, htb]
      _ = b := by rw [← mul_assoc, hz2, one_mul]
/-- A four subgroup containing a central involution has normalizer index two when
its other involution is self-centralizing there and its normalizer is larger. -/
public theorem four_normalizer_relIndex (U : Subgroup G) [IsKleinFour U] (z b : G)
    (hz : z ∈ U) (hb : b ∈ U) (hz1 : z ≠ 1) (hb1 : b ≠ 1) (hbz : b ≠ z)
    (hzc : z ∈ Subgroup.center G)
    (hC : Subgroup.centralizer ({b} : Set G) ≤ U)
    (hex : ∃ t : G, t ∈ Subgroup.normalizer (U : Set G) ∧ t ∉ U) :
    U.relIndex (Subgroup.normalizer (U : Set G)) = 2 := by
  obtain ⟨t, ht, htout⟩ := hex
  apply index_of_swap U z b t hz hb hz1 hb1 hbz hzc hC ht
  have htb : t*b*t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp ht b).mp hb
  rcases four_cases U z b hz hb hz1 hb1 hbz htb with h | h | h | h
  · have he : MulAut.conj t b = MulAut.conj t 1 := by simpa using h
    exact (hb1 ((MulAut.conj t).injective he)).elim
  · have htz : t*z*t⁻¹ = z := by
      rw [Subgroup.mem_center_iff.mp hzc t, mul_assoc, mul_inv_cancel, mul_one]
    have he : MulAut.conj t b = MulAut.conj t z := h.trans htz.symm
    exact (hbz ((MulAut.conj t).injective he)).elim
  · exact (htout (hC (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp h)))).elim
  · exact h
end Subgroup
