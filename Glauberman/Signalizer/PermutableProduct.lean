module
public import FeitThompson.FinalTheorem
public import Theory.GroupTheory.Signalizer.Defs
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupAction.HallProductFixedPoints
public import Theory.ElementaryAbelian.Basic

/-!
# Permutable products of binary signalizer subgroups

If D and E are subgroups satisfying an odd solvable signalizer family's
bounds, and their actual set products DE and ED coincide, then their join
also satisfies those bounds. The group G is finite and the supplied actor
is elementary abelian of exponent two. No ambient solvability or subgroup
normalization hypothesis is imposed.

Permutability makes DE closed under multiplication and inversion, so it is
exactly D ⊔ E. The general subgroup product cardinality formula makes its
order a divisor of |D||E|, hence odd. The proved Feit–Thompson odd-order
theorem gives solvability of the join. For each indexing actor, the odd
intersection D∩E makes every fixed point in DE a product of fixed points
in D and E, which both lie in the corresponding family value. All action
restrictions use the original supplied action and invariant-subgroup proofs.

This is the binary odd case of Kurzweil–Stellmacher, *The Theory of Finite
Groups*, Lemma 11.1.2, printed p.306, used in the factorization step of
Lemma 11.2.7. Its implementation is above Theory because it uses the
Feit–Thompson proof campaign to establish the source's solvability condition.
-/

open scoped Pointwise

private theorem coe_sup_eq_mul_of_permutable
    {G : Type*} [Group G] (D E : Subgroup G)
    (hperm : (D : Set G) * (E : Set G) = (E : Set G) * (D : Set G)) :
    (↑(D ⊔ E) : Set G) = (D : Set G) * (E : Set G) := by
  have hmul : ((D : Set G) * (E : Set G)) * ((D : Set G) * (E : Set G)) =
      (D : Set G) * (E : Set G) := by
    calc
      _ = (D : Set G) * ((E : Set G) * (D : Set G)) * (E : Set G) := by simp only [mul_assoc]
      _ = (D : Set G) * ((D : Set G) * (E : Set G)) * (E : Set G) := by rw [← hperm]
      _ = ((D : Set G) * (D : Set G)) * ((E : Set G) * (E : Set G)) := by simp only [mul_assoc]
      _ = _ := by rw [coe_mul_coe, coe_mul_coe]
  have hinv : ((D : Set G) * (E : Set G))⁻¹ = (D : Set G) * (E : Set G) := by
    rw [mul_inv_rev, inv_coe_set, inv_coe_set, ← hperm]
  rw [Subgroup.sup_eq_closure_mul]
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨1, D.one_mem, 1, E.one_mem, one_mul _⟩
    | mul y z _ _ hy hz =>
      rw [← hmul]
      exact Set.mul_mem_mul hy hz
    | inv y _ hy =>
      rw [← hinv]
      exact Set.inv_mem_inv.mpr hy
  · exact Subgroup.subset_closure

namespace Theory.GroupTheory.TwoSignalizerFamily

/-- A permutable product of odd signalizer subgroups is a signalizer subgroup. -/
public theorem IsSignalizerSubgroup.sup_of_permutable
    {A G : Type*} [Group A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    {θ : TwoSignalizerFamily A G} {D E : Subgroup G}
    (hD : θ.IsSignalizerSubgroup D) (hE : θ.IsSignalizerSubgroup E)
    (hperm : (D : Set G) * (E : Set G) = (E : Set G) * (D : Set G)) :
    θ.IsSignalizerSubgroup (D ⊔ E) := by
  let _ : IsInvariant A G D := hD.2.2.1
  let _ : IsInvariant A G E := hE.2.2.1
  have hprod := coe_sup_eq_mul_of_permutable D E hperm
  have hcard := Subgroup.card_set_mul_mul_card_inf D E
  rw [← hprod] at hcard
  have hodd : Odd (Nat.card (D ⊔ E : Subgroup G)) := by
    have hdiv : Nat.card (D ⊔ E : Subgroup G) ∣ Nat.card D * Nat.card E :=
      ⟨Nat.card (D ⊓ E : Subgroup G), hcard.symm⟩
    exact (hD.1.mul hE.1).of_dvd_nat hdiv
  refine ⟨hodd, odd_order_theorem (D ⊔ E : Subgroup G) hodd, isInvariant_sup D E, ?_⟩
  intro a x hx
  let _ : IsInvariant (Subgroup.zpowers a.val) G D :=
    ⟨fun b g => hD.2.2.1.invariant (b : A) g⟩
  let _ : IsInvariant (Subgroup.zpowers a.val) G E :=
    ⟨fun b g => hE.2.2.1.invariant (b : A) g⟩
  have hactor : IsPGroup 2 (Subgroup.zpowers a.val) :=
    (IsElementaryAbelian.isPGroup 2 A).to_subgroup _
  have hinter : Odd (Nat.card (D ⊓ E : Subgroup G)) :=
    hD.1.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : D ⊓ E ≤ D))
  have hxprod : x ∈ (D : Set G) * (E : Set G) := by rw [← hprod]; exact hx.1
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp
    (fixed_mem_mul_of_odd_inf hactor D E hinter hx.2 hxprod)
  exact (θ.subgroup a).mul_mem (hD.2.2.2 a hu) (hE.2.2.2 a hv)

end Theory.GroupTheory.TwoSignalizerFamily
