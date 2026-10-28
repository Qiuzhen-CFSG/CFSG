module

public import Theory.Mathieu.M22.ValueBoundParabolics.OddCoverLifting.Basic
public import Theory.Alternating.theorem_5_2_1_2

/-!
# Odd central extensions of the small symmetric groups

Every finite central extension of S₃ or S₅ by an odd-order kernel splits.
Lift each adjacent transposition to an involution by correcting its square
with the unique square root in the kernel. A power of a product of two such
involutions which lies in the kernel is both centralized and inverted by the
first involution. It has square one, so oddness makes it trivial. Thus the
lifts satisfy the genuine type-A Coxeter relations.

The Coxeter normal-form bound and generation by adjacent transpositions show
that the resulting map from the presented group to the symmetric group is
bijective. The image of the lifted presentation is therefore a complement.
Only the normal-form results from the alternating-group development are used;
no multiplier or universal-cover splitting assertion is needed.

This supplies the elementary symmetric-extension prerequisite for the local
cover argument in Aschbacher–Smith, E.4.3(2), printed pp. 241–242, combined
manuscript of 1 March 2004. It does not assert characteristicness or perform
the separate reduction across the two-core.
-/

public section
namespace Sporadic.Mathieu.M22ValueBound.OddCoverLifting
open Subgroup
open scoped Pointwise
universe u

/-- Correct a lift by a central square root to make its square trivial. -/
private theorem exists_involution_lift {E F : Type*} [Group E] [Group F]
    (f : E →* F) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker))
    (t : F) (ht : t ^ 2 = 1) : ∃ a : E, f a = t ∧ a ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := hf t
  have hxk : x ^ 2 ∈ f.ker := by simp [MonoidHom.mem_ker, hx, ht]
  obtain ⟨z, hz⟩ := ho.coprime_two_right.pow_left_bijective.surjective
    (⟨(x ^ 2)⁻¹, f.ker.inv_mem hxk⟩ : f.ker)
  have hz' : (z : E) ^ 2 = (x ^ 2)⁻¹ := congrArg Subtype.val hz
  have hcomm : Commute x (z : E) := (mem_center_iff.mp (hc z.property) x)
  refine ⟨x * z, ?_, ?_⟩
  · simp [map_mul, show f (z : E) = 1 from z.property, hx]
  · rw [hcomm.mul_pow, hz', mul_inv_cancel]

/-- A central odd-order power of a product of involutions is trivial. -/
private theorem involution_product_relation {E F : Type*} [Group E] [Group F]
    (f : E →* F) (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker))
    {a b : E} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (k : ℕ)
    (hk : (f a * f b) ^ k = 1) : (a * b) ^ k = 1 := by
  have hak : a * a = 1 := by simpa [pow_two] using ha
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_right hak).symm
  have hbi : b⁻¹ = b := (eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hb)).symm
  have hz : (a * b) ^ k ∈ f.ker := by simpa [MonoidHom.mem_ker] using hk
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    simp [← mul_assoc, hak, hai, hbi]
  have heq : (a * b) ^ k = ((a * b) ^ k)⁻¹ := by
    calc
      (a * b) ^ k = a * (a * b) ^ k * a⁻¹ := by
        rw [mem_center_iff.mp (hc hz) a, mul_inv_cancel_right]
      _ = (a * (a * b) * a⁻¹) ^ k := conj_pow.symm
      _ = ((a * b) ^ k)⁻¹ := by rw [hconj, inv_pow]
  have hsquare : ((a * b) ^ k) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (a * b) ^ k * (a * b) ^ k = ((a * b) ^ k)⁻¹ * (a * b) ^ k :=
        congrArg (fun w => w * (a * b) ^ k) heq
      _ = 1 := inv_mul_cancel _
  have hone : (⟨(a * b) ^ k, hz⟩ : f.ker) = 1 := by
    apply ho.coprime_two_right.pow_left_bijective.injective
    apply Subtype.ext
    simpa using hsquare
  exact congrArg Subtype.val hone

/-- The type-A presentation gives the complement once the permutation relations hold. -/
private theorem symmetricOddCentralSplitting_of_relations (r : ℕ)
    (hrel : (CoxeterMatrix.A r).IsLiftable
      (fun i : Fin r => Equiv.swap i.castSucc i.succ)) :
    SymmetricOddCentralSplitting.{u} (r + 1) := by
  classical
  intro E _ _ f hf hc ho
  have hlift (i : Fin r) : ∃ a : E,
      f a = Equiv.swap i.castSucc i.succ ∧ a ^ 2 = 1 :=
    exists_involution_lift f hf hc ho _ (by simp [pow_two])
  choose a ha ha2 using hlift
  have har : (CoxeterMatrix.A r).IsLiftable a := by
    intro i j
    apply involution_product_relation f hc ho (ha2 i) (ha2 j)
    rw [ha i, ha j]
    exact hrel i j
  let g : (CoxeterMatrix.A r).Group →* E :=
    (CoxeterMatrix.A r).toCoxeterSystem.lift ⟨a, har⟩
  have hg (i : Fin r) : g ((CoxeterMatrix.A r).simple i) = a i :=
    (CoxeterMatrix.A r).toCoxeterSystem.lift_apply_simple har i
  let q := f.comp g
  have hq (i : Fin r) : q ((CoxeterMatrix.A r).simple i) =
      Equiv.swap i.castSucc i.succ := by
    change f (g _) = _
    rw [hg, ha]
  have hsurj : Function.Surjective q := by
    apply MonoidHom.mrange_eq_top.mp
    apply top_unique
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ r]
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨(CoxeterMatrix.A r).simple i, hq i⟩
  let : Finite (CoxeterMatrix.A r).Group :=
    GLS3.Chapter5.SchurPresentation.TypeANormalForm.group_finite r
  have hinj : Function.Injective q :=
    (hsurj.bijective_of_nat_card_le (by
      simpa only [Nat.card_perm, Nat.card_fin] using
        GLS3.Chapter5.SchurPresentation.TypeANormalForm.natCard_group_le_factorial r)).1
  refine ⟨g.range, isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
  · apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx, y, rfl⟩
    have hy : y = 1 := hinj (hx.trans q.map_one.symm)
    simp [hy]
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨y, hy⟩ := hsurj (f x)
    refine ⟨x * (g y)⁻¹, ?_, g y, ⟨y, rfl⟩, ?_⟩
    · change f (x * (g y)⁻¹) = 1
      change f (g y) = f x at hy
      simp [hy]
    · simp

/-- Every finite odd central extension of S₃ has a complement to its kernel. -/
theorem symmetricOddCentralSplitting_three : SymmetricOddCentralSplitting.{u} 3 := by
  apply symmetricOddCentralSplitting_of_relations 2
  unfold CoxeterMatrix.IsLiftable
  decide

/-- Every finite odd central extension of S₅ has a complement to its kernel. -/
theorem symmetricOddCentralSplitting_five : SymmetricOddCentralSplitting.{u} 5 := by
  apply symmetricOddCentralSplitting_of_relations 4
  unfold CoxeterMatrix.IsLiftable
  decide

end Sporadic.Mathieu.M22ValueBound.OddCoverLifting
