module
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.QuaternionFixedEight

/-!
# Inner action on an invariant quaternion subgroup from a fixed eight

Let two commuting quaternion factors have intersection of order two and
join of order thirty-two. If an ambient actor preserves the join and a
quaternion subgroup inside it, while fixing an elementary subgroup of order
eight pointwise, its action on the quaternion subgroup is inner.

The intrinsic quaternion-factor theorem identifies the invariant subgroup
with one of the two factors. Conjugation permutes the two factors; its
injectivity prevents the other factor from mapping to the preserved one.
Thus both factors are preserved, and `factor_inner_of_fixed_eight` applies.
All action and subgroup hypotheses are explicit; the elementary assumption
on the fixed eight is stated as the square-one condition used by that lemma.

This is the short intrinsic-factor adapter used to exclude a quaternion
maximal eight in Stellmacher (9.1), Journal of Algebra 190 (1997), p.48.
No campaign-specific predicate or local classification is imported.
-/

namespace Subgroup

public theorem inner_on_quaternion_subgroup_of_fixed_eight
    {G : Type*} [Group G] [Finite G] (B C U A : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hU : Nonempty (U ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hUle : U ≤ B ⊔ C) (hVcard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (hAle : A ≤ B ⊔ C) (hAcard : Nat.card A = 8)
    (hAexp : ∀ a ∈ A, a ^ 2 = 1)
    (actor : G) (hVn : actor ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hUn : actor ∈ normalizer (U : Set G))
    (hfix : ∀ a ∈ A, Commute actor a) :
    ∃ u : G, u ∈ U ∧ ∀ x ∈ U, actor * x * actor⁻¹ = u * x * u⁻¹ := by
  have hne : B ≠ C := by
    intro hh
    have hcard : Nat.card B = 8 := by
      obtain ⟨e⟩ := hB
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← hh,inf_idem,hcard] at hinter
    omega
  let e := MulAut.conj actor
  have hsup : (B ⊔ C).map e.toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp hVn
  have himage (D : Subgroup G) (hD : Nonempty (D ≃* QuaternionGroup 2))
      (hDle : D ≤ B ⊔ C) : D.map e.toMonoidHom = B ∨ D.map e.toMonoidHom = C := by
    obtain ⟨d⟩ := hD
    apply quaternion_subgroup_eq_factor B C _ hB hC hinter hcomm
    · exact ⟨(D.equivMapOfInjective e.toMonoidHom e.injective).symm.trans d⟩
    · exact (map_mono hDle).trans_eq hsup
  have hUeq := quaternion_subgroup_eq_factor B C U hB hC hinter hcomm hU hUle
  rcases hUeq with hUeq | hUeq
  · subst U
    have hBn : B.map e.toMonoidHom = B := mem_normalizer_iff_map_conj_eq.mp hUn
    have hCn : C.map e.toMonoidHom = C := by
      rcases himage C hC le_sup_right with hh | hh
      · exact (hne (map_injective e.injective (hBn.trans hh.symm))).elim
      · exact hh
    exact factor_inner_of_fixed_eight B C A hB hC hcomm hVcard hAle hAcard hAexp
      actor hUn (mem_normalizer_iff_map_conj_eq.mpr hCn) hfix
  · subst U
    have hCn : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hUn
    have hBn : B.map e.toMonoidHom = B := by
      rcases himage B hB le_sup_left with hh | hh
      · exact hh
      · exact (hne (map_injective e.injective (hh.trans hCn.symm))).elim
    exact factor_inner_of_fixed_eight C B A hC hB (fun c hc b hb => (hcomm b hb c hc).symm)
      (by simpa only [sup_comm] using hVcard) (by simpa only [sup_comm] using hAle)
      hAcard hAexp actor hUn (mem_normalizer_iff_map_conj_eq.mpr hBn) hfix

end Subgroup
