module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
/-!
# Exact involution-factorization counts in the Case II coordinates

An involution factorization of r is determined by its first factor x; the second
is xr. Kernel evaluation of the resulting 384-element subtype gives the five
counts 50, 6, 0, 12, 8. Powers of all five representatives equal z₁, so both
involution factors centralize z₁. Transport through the given equivalence k
therefore gives these exact counts in the ambient group, without character
hypotheses or an ambient order assumption.

Source: the local counting in Suzuki's formula used in Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 6, pp.11–14. These are counts of actual ordered factorizations, not
character-table metadata or externally computed proof assumptions.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
private theorem reduced_counts : ∀ r : Fin 5, Fintype.card {x : TwistedModel //
    x ≠ 1 ∧ x * x = 1 ∧ x * specialRepresentative r ≠ 1 ∧
      (x * specialRepresentative r) * (x * specialRepresentative r) = 1} =
    (![50, 6, 0, 12, 8] r : ℕ) := by
  decide +kernel


private theorem count_first_factors {H : Type*} [Group H] (r : H) :
    Theory.Character.involutionPairCount r = Nat.card {x : H //
      x ≠ 1 ∧ x * x = 1 ∧ x * r ≠ 1 ∧ (x * r) * (x * r) = 1} := by
  have ho (x : H) : orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
    simp only [orderOf_eq_prime_iff, pow_two, and_comm]
  unfold Theory.Character.involutionPairCount
  apply Nat.card_congr
  refine {
    toFun := fun p => ⟨p.val.1, ?_⟩
    invFun := fun x => ⟨(x.val, x.val * r), (ho x.val).mpr ⟨x.prop.1, x.prop.2.1⟩,
      (ho (x.val * r)).mpr x.prop.2.2, ?_⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  · have hx := (ho p.val.1).mp p.prop.1
    have hy := (ho p.val.2).mp p.prop.2.1
    have he : p.val.1 * r = p.val.2 := by
      calc
        _ = p.val.1 * (p.val.1 * p.val.2) := congrArg (p.val.1 * ·) p.prop.2.2.symm
        _ = p.val.2 := by rw [← mul_assoc, hx.2, one_mul]
    exact ⟨hx.1, hx.2, he.symm ▸ hy⟩
  · rw [← mul_assoc, x.prop.2.1, one_mul]
  · intro p
    apply Subtype.ext
    change (p.val.1, p.val.1 * r) = p.val
    refine Prod.ext rfl ?_
    calc
      _ = p.val.1 * (p.val.1 * p.val.2) := congrArg (p.val.1 * ·) p.prop.2.2.symm
      _ = p.val.2 := by rw [← mul_assoc, ((ho p.val.1).mp p.prop.1).2, one_mul]

/-- The five actual involution-pair counts in the explicit centralizer model. -/
public theorem specialRepresentative_involutionPairCount : ∀ r : Fin 5,
    Theory.Character.involutionPairCount (specialRepresentative r) =
      (![50, 6, 0, 12, 8] r : ℕ) := by
  intro r
  rw [count_first_factors]
  simpa only [Nat.card_eq_fintype_card] using reduced_counts r


/-- Each special representative is a root of the distinguished involution. -/
public theorem specialRepresentative_power : ∀ r : Fin 5,
    specialRepresentative r ^ (![1, 3, 4, 2, 2] r : ℕ) = CaseII.z 0 := by
  decide +kernel

private theorem pairCount_equiv {H K : Type*} [Group H] [Group K]
    (e : H ≃* K) (r : H) :
    Theory.Character.involutionPairCount (e r) = Theory.Character.involutionPairCount r := by
  unfold Theory.Character.involutionPairCount
  apply Nat.card_congr
  refine {
    toFun := fun p => ⟨(e.symm p.val.1, e.symm p.val.2), ?_, ?_, ?_⟩
    invFun := fun p => ⟨(e p.val.1, e p.val.2), ?_, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (e.symm.orderOf_eq _).trans p.prop.1
  · exact (e.symm.orderOf_eq _).trans p.prop.2.1
  · rw [← map_mul, p.prop.2.2, e.symm_apply_apply]
  · exact (e.orderOf_eq _).trans p.prop.1
  · exact (e.orderOf_eq _).trans p.prop.2.1
  · rw [← map_mul, p.prop.2.2]
  · intro p
    apply Subtype.ext
    simp only [e.apply_symm_apply, Prod.mk.eta]
  · intro p
    apply Subtype.ext
    simp only [e.symm_apply_apply, Prod.mk.eta]

/-- The same five actual counts in the arbitrary ambient group. -/
public theorem ambient_involutionPairCount {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (r : Fin 5) :
    Theory.Character.involutionPairCount (CaseII.into D k (specialRepresentative r)) =
      (![50, 6, 0, 12, 8] r : ℕ) := by
  have hroot : D.z ∈ Subgroup.zpowers (CaseII.into D k (specialRepresentative r)) := by
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨((![1, 3, 4, 2, 2] r : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, ← map_pow, specialRepresentative_power, CaseII.into_z_zero]
  have hh := Theory.Character.involutionPairCount_centralizer_of_root
    D.z D.z_order (k (specialRepresentative r)) hroot
  change Theory.Character.involutionPairCount (CaseII.into D k (specialRepresentative r)) =
    Theory.Character.involutionPairCount (k (specialRepresentative r)) at hh
  rw [hh, pairCount_equiv k, specialRepresentative_involutionPairCount]
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
