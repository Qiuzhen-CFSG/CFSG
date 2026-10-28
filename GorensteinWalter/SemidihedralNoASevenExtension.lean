module
public import GorensteinWalter.ASevenNormalExtension
public import Stellmacher.MainDefs

/-!
# Semidihedral Sylow subgroups exclude an index-two A₇

A finite group with an actual semidihedral Sylow two subgroup cannot contain
a normal subgroup isomorphic to A₇ of index two. No odd-core-free assumption
or classification of index-two extensions is required. This is the A₇
exclusion in ABG II.3 Proposition 4, article p.29.

An appropriate power of the semidihedral rotation has order eight. Transport
its conjugation action on the normal A₇ through the proved Aut(A₇)≃S₇
bijection. Every permutation on seven points whose eighth power is one has
fourth power one, since its cycle lengths can only be one, two or four.
The rotation's fourth power therefore centralizes the normal subgroup.
It also belongs to that subgroup by the index-two square criterion, so it
lies in A₇'s trivial center. This contradicts the chosen element's order.
The existing permutation bound is reused without changing its proof.
-/

namespace GorensteinWalter

/-- A normal index-two A₇ is incompatible with semidihedral Sylow two geometry. -/
public theorem not_normal_a7_index_two_of_semidihedral_sylow
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (N : Subgroup G) [N.Normal] (hindex : N.index = 2)
    (hN : Nonempty (N ≃* alternatingGroup (Fin 7))) : False := by
  classical
  obtain ⟨e⟩ := hN
  obtain ⟨n, hn, _, a, _, ha, _⟩ := hS
  have hd : 8 ∣ orderOf a := by
    rw [ha]
    exact pow_dvd_pow 2 (by omega : 3 ≤ n - 1)
  let x : S := a ^ (orderOf a / 8)
  have hx : orderOf x = 8 := orderOf_pow_orderOf_div (by rw [ha]; positivity) hd
  let g : G := x
  have hg8 : g ^ 8 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    exact congrArg Subtype.val h
  have hg4 : g ^ 4 ≠ 1 := by
    intro h
    have h4 : x ^ 4 = 1 := Subtype.ext h
    have hd4 := orderOf_dvd_of_pow_eq_one h4
    rw [hx] at hd4
    norm_num at hd4
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  let eAut := MulEquiv.ofBijective c
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let f : G →* Equiv.Perm (Fin 7) := eAut.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N)))
  have hf4 : f (g ^ 4) = 1 := by
    rw [map_pow]
    apply perm_fin_seven_pow_four_eq_one_of_pow_eight_eq_one
    rw [← map_pow, hg8, map_one]
  have hconj : MulAut.conjNormal (H := N) (g ^ 4) = 1 := by
    apply (MulAut.congr e).injective
    apply eAut.symm.injective
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_one] using hf4
  have hgN : g ^ 4 ∈ N := by
    have h := Subgroup.sq_mem_of_index_two hindex (g ^ 2)
    rw [← _root_.pow_mul] at h
    exact h
  let y : N := ⟨g ^ 4, hgN⟩
  have hyconj : MulAut.conj y = 1 := by
    rw [← MulAut.conjNormal_val]
    exact hconj
  have hecenter : e y ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    have hw := congrArg (fun α : MulAut N => α w) hyconj
    change y * w * y⁻¹ = w at hw
    have hc : w * y = y * w := by
      have := congrArg (fun v : N => v * y) hw
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using this.symm
    simpa only [map_mul] using congrArg e hc
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hecenter
  have hy : y = 1 := e.injective (by simpa using hecenter)
  exact hg4 (congrArg Subtype.val hy)

end GorensteinWalter

