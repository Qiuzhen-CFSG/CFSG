module

public import Theory.Representation.Triality.RestrictedWeights
public import Theory.Representation.Triality.RestrictedWeights.BasicDisplacement.WeightPairs

/-!
# Operator displacement from exchanged torus weights

Nonzero vectors in pairwise distinct weight spaces are independent. If an
actual group element carries each of n starting weight spaces into n other
distinct weight spaces, its differences on chosen vectors are independent.
Thus the range of the literal action minus identity has dimension at least n.
This is the linear-algebra input to the two triality root involution bounds.
-/

public section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.BasicDisplacement
universe u v
variable {k : Type u} [Field k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
private theorem differences_independent {ι : Type*} [Fintype ι]
    (v w : ι → V) (h : LinearIndependent k (Sum.elim v w)) :
    LinearIndependent k (fun i => w i - v i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hs : ∑ j : ι ⊕ ι, (Sum.elim (fun j => -c j) c) j • (Sum.elim v w) j = 0 := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_smul,
      Finset.sum_neg_distrib]
    simp only [smul_sub, Finset.sum_sub_distrib] at hc
    exact (sub_eq_zero.mp hc) ▸ neg_add_cancel _
  exact (Fintype.linearIndependent_iff.mp h _ hs) (Sum.inr i)

theorem rank_ge_of_weight_pairs {n : ℕ}
    (ρ : RationalRepresentation K V) (T : ClosedSubgroup K)
    (e : Weight ↪ TorusWeight T) (x : Variety.Point K)
    (a b : Fin n → Weight)
    (hinj : Function.Injective (Sum.elim a b))
    (ha : ∀ i, weightSpace ρ T (e (a i)) ≠ ⊥)
    (hx : ∀ i v, v ∈ weightSpace ρ T (e (a i)) →
      (ρ.action x).val v ∈ weightSpace ρ T (e (b i))) :
    n ≤ Module.finrank k (LinearMap.range ((ρ.action x).val - LinearMap.id)) := by
  classical
  have hex : ∀ i, ∃ v ∈ weightSpace ρ T (e (a i)), v ≠ (0:V) := by
    intro i
    exact (Submodule.ne_bot_iff _).mp (ha i)
  choose v hv hne using hex
  let w := fun i => (ρ.action x).val (v i)
  have hw : ∀ i, w i ∈ weightSpace ρ T (e (b i)) := fun i => hx i _ (hv i)
  have hwne : ∀ i, w i ≠ 0 := by
    intro i hi
    have hi' := congrArg (fun z => (ρ.action x⁻¹).val z) hi
    have hc : (ρ.action x⁻¹).val ((ρ.action x).val (v i)) = v i := by
      change ((ρ.action x⁻¹ * ρ.action x).val : Module.End k V) (v i) = _
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    exact hne i (by simpa only [w, hc, map_zero] using hi')
  have hlin : LinearIndependent k (Sum.elim v w) := by
    apply ((weightSpace_iSupIndep ρ T).comp (e.injective.comp hinj)).linearIndependent
    · intro i
      cases i with
      | inl i => exact hv i
      | inr i => exact hw i
    · intro i
      cases i with
      | inl i => exact hne i
      | inr i => exact hwne i
  let d : Fin n → LinearMap.range ((ρ.action x).val - LinearMap.id) :=
    fun i => ⟨w i - v i, ⟨v i,rfl⟩⟩
  have hd : LinearIndependent k d :=
    LinearIndependent.of_comp (LinearMap.range ((ρ.action x).val - LinearMap.id)).subtype
      (differences_independent v w hlin)
  simpa using hd.fintype_card_le_finrank

end Triality.RestrictedWeights.BasicDisplacement
