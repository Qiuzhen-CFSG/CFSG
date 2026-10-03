module

public import Theory.GroupTheory.Signalizer.Defs
public import Theory.GroupAction.HallProductFixedPoints
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalized joins of prime signalizer subgroups

For an elementary binary actor, two q-subgroups belonging to a signalizer
family remain signalizer subgroups after taking their join, provided the
second normalizes the first and q is odd. The join is again a q-group.
No completeness hypothesis is used.

The standard normalized-join theorem gives the q-group structure; hence the
join has odd order and is nilpotent and solvable. Invariance is preserved by
joins. For each indexing actor, the actual ordered product decomposition of
the normalized join and the odd-intersection fixed-factor theorem express
every fixed element as a product of fixed elements in the two original
subgroups. Both factors lie in the same family value by its defining bounds.
All restrictions use the original ambient action.

This is the prime-subgroup specialization of Kurzweil–Stellmacher,
*The Theory of Finite Groups*, Lemma 11.1.2, printed p.306. It supplies the
join step in the maximal-intersection proof of transitivity, Lemma 11.1.8.
-/

open scoped Pointwise

namespace Theory.GroupTheory.TwoSignalizerFamily

/-- A normalized join of odd-prime signalizer subgroups is a prime signalizer subgroup. -/
public theorem IsSignalizerSubgroup.sup_of_normalizes_pGroup
    {A G : Type*} [Group A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    {θ : TwoSignalizerFamily A G} {D E : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hD : θ.IsSignalizerSubgroup D) (hE : θ.IsSignalizerSubgroup E)
    (hq : q ≠ 2) (hDq : IsPGroup q D) (hEq : IsPGroup q E)
    (hED : E ≤ Subgroup.normalizer (D : Set G)) :
    θ.IsSignalizerSubgroup (D ⊔ E) ∧ IsPGroup q (D ⊔ E : Subgroup G) := by
  have hjoin : IsPGroup q (D ⊔ E : Subgroup G) := hDq.to_sup_of_normal_left' hEq hED
  let : IsInvariant A G D := hD.2.2.1
  let : IsInvariant A G E := hE.2.2.1
  let : Group.IsNilpotent (D ⊔ E : Subgroup G) := hjoin.isNilpotent
  refine ⟨⟨?_, inferInstance, isInvariant_sup D E, ?_⟩, hjoin⟩
  · obtain ⟨n, hn⟩ := hjoin.exists_card_eq
    rw [hn]
    exact ((Fact.out : q.Prime).odd_of_ne_two hq).pow
  · intro a x hx
    let : IsInvariant (Subgroup.zpowers a.val) G D :=
      ⟨fun b g => (hD.2.2.1.invariant (b : A) g)⟩
    let : IsInvariant (Subgroup.zpowers a.val) G E :=
      ⟨fun b g => (hE.2.2.1.invariant (b : A) g)⟩
    have hactor : IsPGroup 2 (Subgroup.zpowers a.val) :=
      (IsElementaryAbelian.isPGroup 2 A).to_subgroup _
    have hodd : Odd (Nat.card (D ⊓ E : Subgroup G)) :=
      hD.1.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : D ⊓ E ≤ D))
    have hprod : x ∈ (D : Set G) * (E : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left D E hED]
      exact hx.1
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp
      (fixed_mem_mul_of_odd_inf hactor D E hodd hx.2 hprod)
    exact (θ.subgroup a).mul_mem (hD.2.2.2 a hu) (hE.2.2.2 a hv)

end Theory.GroupTheory.TwoSignalizerFamily
