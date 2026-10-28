module

public import Theory.GroupAction.ThompsonAB

/-!
# Normalizers fixing a Thompson fixed subgroup

Suppose C acts faithfully on a finite p-group V, commutes with a p-group B,
and has trivial p-core. If A normalizes C and fixes C_V(B) pointwise, then
A centralizes C. Thompson's A × B lemma makes the C-action on C_V(B)
faithful. Conjugating an element of C by A leaves its action there unchanged,
so faithfulness identifies the conjugate with the original element.

This is the faithful-restriction step used in Aschbacher–Smith E.3.40,
printed p.240, with C the odd centralizer of a hyperplane. Taking the whole
centralizer also avoids a separate coprime commutator-idempotence argument.
-/

namespace Subgroup

/-- A normalizer fixing the B-fixed subgroup centralizes a faithful actor
commuting with B and having trivial p-core. Normality is relative to A. -/
public theorem le_centralizer_of_fixes_fixedPoints
    {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    [MulDistribMulAction H V] {p : ℕ} [Fact p.Prime]
    (C B A : Subgroup H) [FaithfulSMul C V]
    (hV : IsPGroup p V) (hB : IsPGroup p B)
    (hCB : ⁅C, B⁆ = ⊥) (hcore : pCore p C = ⊥)
    (hAC : A ≤ normalizer (C : Set H))
    (hfix : A ≤ fixingSubgroup H (FixedPoints.subgroup B V : Set V)) :
    A ≤ centralizer (C : Set H) := by
  let : IsInvariant C V (FixedPoints.subgroup B V) :=
    fixedPoints_isInvariant_of_normalizing_actor C B
      ((commutator_eq_bot_iff_le_centralizer.mp hCB).trans
        (centralizer_le_normalizer _))
  let : FaithfulSMul C (FixedPoints.subgroup B V) :=
    thompson_faithfulSMul_fixedPoints C B hV hB hCB hcore
  intro a ha c hc
  have hc' : a * c * a⁻¹ ∈ C := (mem_normalizer_iff.mp (hAC ha) c).mp hc
  have he : (⟨a * c * a⁻¹, hc'⟩ : C) = ⟨c, hc⟩ := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := FixedPoints.subgroup B V)
    intro v
    apply Subtype.ext
    change (a * c * a⁻¹) • (v : V) = c • (v : V)
    have hinv := (mem_fixingSubgroup_iff H).mp (hfix (A.inv_mem ha)) v.val v.property
    have hcv : c • v.val ∈ FixedPoints.subgroup B V :=
      (IsInvariant.invariant (A := C) (H := FixedPoints.subgroup B V)
        (⟨c, hc⟩ : C) v.val).mp v.property
    rw [mul_smul, mul_smul, hinv]
    exact (mem_fixingSubgroup_iff H).mp (hfix ha) _ hcv
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm

end Subgroup
