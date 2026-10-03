module

public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# Rank-one two-groups of exponent at most four

A finite two-group with no elementary four-subgroup and with every fourth
power trivial is cyclic or quaternion of order eight. The unique-involution
classification gives a generalized quaternion group; its standard cyclic
generator has order twice the parameter, which bounds that parameter by two.

Source: Gorenstein, *Finite Groups*, Section 5.4, with the exponent restriction
used in the extraspecial classification of Section 5.5.
-/

namespace IsPGroup

/-- The exponent-four specialization of the rank-one classification. -/
public theorem isCyclic_or_quaternion_two_of_no_elementary_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hpow : ∀ x : P, x ^ 4 = 1)
    (hfour : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E ≠ 4) :
    IsCyclic P ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  rcases hP.isCyclic_or_quaternion_of_no_elementary_four hfour with h | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl h
  · right
    have hmodel : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (n - 2))) ^ 4 = 1 := by
      simpa only [map_pow, e.apply_symm_apply, map_one] using
        congrArg e (hpow (e.symm (QuaternionGroup.a 1)))
    have hbound : 2 * 2 ^ (n - 2) ≤ 4 := by
      have hd := orderOf_dvd_of_pow_eq_one hmodel
      rw [QuaternionGroup.orderOf_a_one] at hd
      exact Nat.le_of_dvd (by decide) hd
    have hle : n - 2 ≤ 1 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      norm_num only [pow_one]
      omega
    have heq : n = 3 := by omega
    subst n
    exact ⟨e⟩

end IsPGroup
