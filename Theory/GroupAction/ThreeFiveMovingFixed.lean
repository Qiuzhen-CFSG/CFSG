module

public import Theory.Representation.PrimeSubgroupFixedVector
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.InvariantsBaseChange
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.Commutator.ActionTriviality
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Five-fixed points in a three-moving binary module

A faithful nontrivial elementary abelian three-group has a nonzero moving
subgroup on a finite elementary abelian two-group. Coprime splitting removes
all three-group invariants from this subgroup. Extend its actual linear
representation to an algebraic closure of `ZMod 2` and sum the five translates
of a nonzero character-weight vector. Fixed-free conjugation on the
three-group makes the five weights distinct, so the sum is nonzero.
Invariants commute with scalar extension, giving a nonzero binary invariant.

This proves the existence step used in the fixed-point bound of Thompson,
*Nonsolvable finite groups all of whose local subgroups are solvable*, VI,
printed p.630. The cardinality bound is assembled in a separate module.
-/

open scoped IsMulCommutative TensorProduct

namespace ThreeFiveAction

/-- The three-moving subgroup contains a nonidentity element fixed by the
fixed-free five-complement, for the supplied action on the binary group. -/
public theorem moving_fixed_ne_bot {H V : Type*} [Group H] [Finite H]
    [Group V] [Finite V] [MulDistribMulAction H V] [IsElementaryAbelian 2 V]
    (B A : Subgroup H) [B.Normal] [IsElementaryAbelian 3 B] [FaithfulSMul B V]
    (hB : B ≠ ⊥) (hA : Nat.card A = 5) (_hBA : B.IsComplement' A)
    (hfree : B ⊓ Subgroup.centralizer (A : Set H) = ⊥) :
    commutatorAction B V ⊓ FixedPoints.subgroup A V ≠ ⊥ := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let W := commutatorAction B V
  let : IsInvariant H V W := by
    have ht := commutatorAction_isInvariant_of_normalizing_actor
      (V := V) (⊤ : Subgroup H) B (by rw [Subgroup.normalizer_eq_top])
    exact ⟨fun h v => ht.invariant ⟨h, Subgroup.mem_top h⟩ v⟩
  let : IsInvariant B V W := commutatorAction_isInvariant
  let : IsInvariant A V W := commutatorAction_isInvariant_of_normalizing_actor
    A B (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  let : IsElementaryAbelian 2 W :=
    { exponent_dvd_p := dvd_trans (Monoid.exponent_dvd_of_monoidHom
        W.subtype W.subtype_injective) (IsElementaryAbelian.exponent_dvd_p 2 V) }
  have hW : W ≠ ⊥ := by
    intro h
    have ht := actsTrivially_of_commutatorAction_eq_bot h
    apply hB
    apply eq_bot_iff.mpr
    intro b hb
    have heq : (⟨b, hb⟩ : B) = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
      intro v
      simpa using ht ⟨b, hb⟩ v
    exact congrArg Subtype.val heq
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW
  have hcop : Nat.Coprime (Nat.card B) (Nat.card V) := by
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 3 B).exists_card_eq
    obtain ⟨v, hv⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hb, hv]
    exact ((by decide : Nat.Coprime 3 2).pow_left b).pow_right v
  have hcompl : IsCompl (FixedPoints.subgroup B V) W :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm fun x y : V => mul_comm x y) hcop inferInstance
  have hfixedB : FixedPoints.subgroup B W = ⊥ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
    simpa only [inf_comm] using hcompl.inf_eq_bot
  let rho : Representation (ZMod 2) H (Additive W) :=
    Representation.ofElementaryAbelianAction
  have hfix : Representation.invariants (rho.comp B.subtype) = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    have hvfix : Additive.toMul v ∈ FixedPoints.subgroup B W := by
      intro b
      exact congrArg Additive.toMul (hv b)
    have hvone : Additive.toMul v = 1 := by simpa [hfixedB] using hvfix
    exact hvone
  let E := AlgebraicClosure (ZMod 2)
  let sigma := Representation.extendScalars E rho
  let : Nontrivial (E ⊗[ZMod 2] Additive W) :=
    Representation.extendScalars_nontrivial E rho
  have horder : (Nat.card B : E) ≠ 0 := by
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 3 B).exists_card_eq
    rw [hb, Nat.cast_pow]
    apply pow_ne_zero
    rw [ne_eq, CharP.cast_eq_zero_iff E 2]
    decide
  have hfixE : Representation.invariants (sigma.comp B.subtype) = ⊥ := by
    change (Representation.extendScalars E (rho.comp B.subtype)).invariants = ⊥
    rw [Representation.invariants_extendScalars_eq_baseChange_of_finite, hfix,
      Submodule.baseChange_bot]
  have hnonzero := Representation.prime_subgroup_invariants_ne_bot_of_fixed_free
    sigma B A hA hfree horder hfixE
  have hfixedA : FixedPoints.subgroup A W ≠ ⊥ := by
    intro hbot
    apply hnonzero
    change (Representation.extendScalars E (rho.comp A.subtype)).invariants = ⊥
    rw [Representation.invariants_extendScalars_eq_baseChange_of_finite]
    have hfixA : Representation.invariants (rho.comp A.subtype) = ⊥ := by
      apply eq_bot_iff.mpr
      intro v hv
      have hvfix : Additive.toMul v ∈ FixedPoints.subgroup A W := by
        intro a
        exact congrArg Additive.toMul (hv a)
      have hvone : Additive.toMul v = 1 := by simpa [hbot] using hvfix
      exact hvone
    rw [hfixA, Submodule.baseChange_bot]
  intro hbot
  apply hfixedA
  apply Subgroup.map_injective W.subtype_injective
  rw [fixedPoints_subgroup_map_subtype_eq_inf, Subgroup.map_bot]
  exact hbot

end ThreeFiveAction
