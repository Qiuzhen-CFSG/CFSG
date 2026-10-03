module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Order-eight elements over the symmetric group of degree four

The fourth power of an element of order eight lies in the kernel of any
homomorphism to `S₄`. If that kernel is cyclic, its unique involution identifies
this fourth power. Conjugacy transports the conclusion from one involution
centralizer to every involution centralizer.

These elementary power calculations supply the cyclic intersection argument
in Suzuki (1965), Section II, Lemma 6 at q = 3. They require neither a
classification of central extensions nor a transfer theorem.
-/

namespace Equiv.Perm

/-- The exponent of the symmetric group of degree four divides twelve. -/
public theorem pow_twelve_eq_one_fin_four (σ : Equiv.Perm (Fin 4)) : σ ^ 12 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hlo := two_le_of_mem_cycleType hn
  have hhi : n ≤ 4 := (Multiset.le_sum_of_mem hn).trans σ.sum_cycleType_le
  interval_cases n <;> decide

end Equiv.Perm

namespace MonoidHom

/-- Every element whose eighth power is one has fourth power in the kernel
of a homomorphism to the symmetric group of degree four. -/
public theorem pow_four_mem_ker_perm_four
    {E : Type*} [Group E] (f : E →* Equiv.Perm (Fin 4))
    (x : E) (hx : x ^ 8 = 1) : x ^ 4 ∈ f.ker := by
  have hx12 : x ^ 12 = x ^ 4 := by
    calc
      x ^ 12 = x ^ 8 * x ^ 4 := by rw [← pow_add]
      _ = x ^ 4 := by rw [hx, one_mul]
  rw [mem_ker, ← hx12, map_pow]
  exact Equiv.Perm.pow_twelve_eq_one_fin_four (f x)

/-- In a cyclic-kernel extension of `S₄`, the fourth power of every element
of order eight is the kernel's unique involution. Surjectivity is unnecessary. -/
public theorem pow_four_eq_of_cyclic_ker_perm_four
    {E : Type*} [Group E] [Finite E]
    (f : E →* Equiv.Perm (Fin 4)) [IsCyclic f.ker]
    (j x : E) (hj : j ∈ f.ker) (hj2 : orderOf j = 2)
    (hx : orderOf x = 8) : x ^ 4 = j := by
  have hxker := f.pow_four_mem_ker_perm_four x
    (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hx4 : orderOf (x ^ 4) = 2 := by rw [orderOf_pow, hx]; decide
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := (⟨x ^ 4, hxker⟩ : f.ker)) (y := (⟨j, hj⟩ : f.ker))
    (by simpa only [← Subgroup.orderOf_coe] using hx4)
    (by simpa only [← Subgroup.orderOf_coe] using hj2))

end MonoidHom

namespace Subgroup

/-- If all involutions are conjugate, a cyclic-kernel model over `S₄` for one
involution centralizer identifies the involution in every cyclic order-eight
subgroup commuting with any involution. -/
public theorem pow_four_eq_of_involution_centralizer_perm_four
    {G : Type*} [Group G] [Finite G]
    (j : G) (hj2 : orderOf j = 2)
    (f : centralizer ({j} : Set G) →* Equiv.Perm (Fin 4)) [IsCyclic f.ker]
    (hjker : (⟨j, mem_centralizer_singleton_iff.mpr rfl⟩ :
      centralizer ({j} : Set G)) ∈ f.ker)
    (hconj : ∀ i : G, orderOf i = 2 → IsConj i j)
    (i x : G) (hi : orderOf i = 2) (hx : orderOf x = 8)
    (hcomm : Commute x i) : x ^ 4 = i := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj i hi)
  let e : G ≃* G := MulAut.conj c
  have hei : e i = j := hc
  have hecomm : Commute (e x) j := by
    rw [← hei]
    exact hcomm.map e.toMonoidHom
  let y : centralizer ({j} : Set G) :=
    ⟨e x, mem_centralizer_singleton_iff.mpr hecomm.eq⟩
  let z : centralizer ({j} : Set G) :=
    ⟨j, mem_centralizer_singleton_iff.mpr rfl⟩
  have hy : orderOf y = 8 := by
    rw [← Subgroup.orderOf_coe, e.orderOf_eq]
    exact hx
  have hz : orderOf z = 2 := by
    simpa only [← Subgroup.orderOf_coe] using hj2
  have heq := f.pow_four_eq_of_cyclic_ker_perm_four z y hjker hz hy
  apply e.injective
  rw [map_pow, hei]
  exact congrArg Subtype.val heq

end Subgroup
