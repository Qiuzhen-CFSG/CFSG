module
public import Theory.GroupTheory.Signalizer.Transitivity

/-!
# Completeness of a prime-valued binary signalizer family

A signalizer family for a finite elementary binary actor of order at least
eight is complete if every value is a q-group for one fixed odd prime q.
The ambient group need only be finite, and the original action is retained.

Extend one family value to a maximal q-signalizer subgroup Q. The common
intersection of the values lies in Q. Every other value extends to a
maximal q-signalizer subgroup R, and transitivity conjugates Q to R using
an element of that common intersection. Since the conjugator already lies
in Q, its conjugation fixes Q. Thus every family value lies in Q. The actual
generated closure is an invariant subgroup of Q, so downward closure makes
it a signalizer subgroup, exactly the completeness predicate.

This is the prime-valued case of Kurzweil–Stellmacher, *The Theory of Finite
Groups*, Lemma 11.1.10, printed p.310, using Lemma 11.1.8. Trivial values
are included without a separate prime-spectrum case split.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

/-- A family whose values are all q-groups for an odd prime q is complete. -/
public theorem complete_of_values_pGroup
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    (θ : TwoSignalizerFamily A G) {q : ℕ} [Fact q.Prime]
    (hA : 8 ≤ Nat.card A) (hq : q ≠ 2)
    (hvalues : ∀ a, IsPGroup q (θ.subgroup a)) : θ.IsComplete := by
  let _ : Nontrivial A := (Finite.one_lt_card_iff_nontrivial (α := A)).mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  let a' : {a : A // a ≠ 1} := ⟨a, ha⟩
  let P : Subgroup G → Prop := fun U => θ.IsSignalizerSubgroup U ∧ IsPGroup q U
  obtain ⟨Q, haQ, hQ⟩ := Finite.exists_le_maximal (p := P)
    ⟨θ.value_isSignalizerSubgroup a', hvalues a'⟩
  have hcommon : θ.common ≤ Q := (θ.common_le a').trans haQ
  have hclosure : θ.closure ≤ Q := by
    apply θ.closure_le.mpr
    intro b
    obtain ⟨R, hbR, hR⟩ := Finite.exists_le_maximal (p := P)
      ⟨θ.value_isSignalizerSubgroup b, hvalues b⟩
    obtain ⟨c, hc, hconj⟩ := θ.maximal_pSubgroups_conjugate hA hq Q R hQ hR
    have hnormal : c ∈ Subgroup.normalizer (Q : Set G) := Q.le_normalizer (hcommon hc)
    have hRQ : R = Q := hconj.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormal)
    exact hbR.trans hRQ.le
  exact hQ.1.1.mono hclosure θ.closure_invariant

end Theory.GroupTheory.TwoSignalizerFamily
