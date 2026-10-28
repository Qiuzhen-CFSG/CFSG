module

public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification
public import Theory.GroupTheory.SpecificGroups.QuaternionCentralSquareEmbedding

/-!
# Elementary fours in groups with a central element of order four

A noncyclic finite two-group with a central element of order four contains
an elementary four. Otherwise the unique-involution classification makes it
generalized quaternion, whose center has exponent two. This form keeps the
quaternion exception explicit when applying the rank-one classification to
an element centralizer.

Source: the cyclic/quaternion alternative of Huppert, III.8.2, as used in
Aschbacher, *On finite groups of component type* (1975), Lemma 3.4, p.95.
-/

open Subgroup

namespace IsPGroup

public theorem exists_elementary_four_of_noncyclic_of_central_order_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcyc : ¬ IsCyclic P) (u : P) (hu : orderOf u = 4) (huZ : u ∈ center P) :
    ∃ E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  by_contra h
  have hn : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≠ 4 :=
    fun E hE hc => h ⟨E, hE, hc⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := (hP.isCyclic_or_quaternion_of_no_elementary_four hn).resolve_left hcyc
  have heZ : e u ∈ center (QuaternionGroup (2 ^ (n - 2))) := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨x, rfl⟩ := e.surjective x
    simpa only [← map_mul] using congrArg e (mem_center_iff.mp huZ x)
  have hpow : 2 ≤ 2 ^ (n - 2) := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 1 ≤ n - 2 by omega)
    simpa using hh
  have hu2 : u ^ 2 = 1 := e.injective (by
    simpa only [map_pow, map_one] using QuaternionGroup.sq_eq_one_of_mem_center hpow (e u) heZ)
  have hd := orderOf_dvd_of_pow_eq_one hu2
  norm_num [hu] at hd

end IsPGroup
