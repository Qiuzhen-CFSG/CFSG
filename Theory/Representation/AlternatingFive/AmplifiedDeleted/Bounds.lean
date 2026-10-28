module

public import Theory.Representation.AlternatingFive.AmplifiedDeleted.Disjoint
public import Theory.Representation.AlternatingFiveInvolutionDisplacement

/-!
# Displacement bounds for amplified deleted A₅ modules

The deleted core in odd degree is faithful. Every nonidentity involution in
its symmetric normalizer moves at least one dimension, and an inner A₅
involution moves at least two. Amplification multiplies these bounds by the
number of copies even when the acting map mixes those copies arbitrarily.

Source: Aschbacher--Smith D.3.9 and D.3.21, printed pp.199--201 and 204--207.
-/

@[expose] public noncomputable section

namespace Representation.AlternatingFive.AmplifiedDeleted
open Module BinaryOffender.NaturalTensor

/-- The permutation action on the degree-five binary deleted core is faithful. -/
theorem core_faithful : Function.Injective (BinaryPermutation.coreRepresentation (Fin 5)) := by
  classical
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  change g = 1
  change BinaryPermutation.coreRepresentation (Fin 5) g = 1 at hg
  have hc (v : C) : BinaryPermutation.coreRepresentation (Fin 5) g v = v := by
    exact DFunLike.congr_fun hg v
  have hf (v : BinaryPermutation.Full (Fin 5)) :
      BinaryPermutation.representation (Fin 5) g v = v := by
    let w := v - BinaryPermutation.augmentation (Fin 5) v • BinaryPermutation.allOne (Fin 5)
    have hw : w ∈ C := by
      change BinaryPermutation.augmentation (Fin 5) w = 0
      have ho : Odd (Fintype.card (Fin 5)) := by decide
      simp only [w, map_sub, map_smul, BinaryPermutation.augmentation_allOne,
        ho.natCast_zmod_two, smul_eq_mul, mul_one, sub_self]
    have he := congrArg Subtype.val (hc ⟨w, hw⟩)
    change BinaryPermutation.representation (Fin 5) g w = w at he
    simpa only [w, map_sub, map_smul, BinaryPermutation.permute_allOne,
      sub_left_inj] using he
  apply _root_.Equiv.ext
  intro i
  have hi := congrFun (hf (Pi.single i 1)) (g i)
  simpa [Pi.single_apply] using hi.symm

/-- A nontrivial core permutation has positive displacement. -/
theorem core_displacement_pos (p : Sym) (hp : p ≠ 1) :
    1 ≤ operatorFixedCodim (BinaryPermutation.coreRepresentation (Fin 5) p) := by
  by_contra h
  have hz : operatorFixedCodim (BinaryPermutation.coreRepresentation (Fin 5) p) = 0 :=
    Nat.eq_zero_of_not_pos h
  have hbot : LinearMap.range (BinaryPermutation.coreRepresentation (Fin 5) p - 1) = ⊥ :=
    (Submodule.finrank_eq_zero).mp hz
  have hzero := LinearMap.range_eq_bot.mp hbot
  apply hp
  apply core_faithful
  simpa only [map_one] using sub_eq_zero.mp hzero

/-- Inner involutions displace at least two dimensions on the simple core. -/
theorem core_inner_displacement (p : Alt) (hp : p * p = 1) (hne : p ≠ 1) :
    2 ≤ operatorFixedCodim (BinaryPermutation.coreRepresentation (Fin 5) p.val) := by
  let ρ := (BinaryPermutation.coreRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype
  have hρ : Function.Injective ρ := core_faithful.comp Subtype.val_injective
  have ho : orderOf p = 2 := orderOf_eq_prime (by simpa only [pow_two] using hp) hne
  exact AlternatingFiveInvolutionDisplacement.displacement_lower ρ hρ p ho

/-- Every nontrivial involution in the symmetric normalizer displaces at least
one dimension per deleted summand, with no restriction on multiplicity mixing. -/
theorem nontrivial_involution_bound {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C)) (p : Sym) (hp : p * p = 1) (hne : p ≠ 1)
    (hT : ∀ (g : Alt) v, T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p * g.val * p⁻¹) (T v)) :
    Fintype.card ι ≤ operatorFixedCodim T := by
  have h := Nat.mul_le_mul_left (Fintype.card ι) (core_displacement_pos p hne)
  simpa only [Nat.mul_one] using h.trans (amplified_involution_bound T p hp hT)

/-- Every nontrivial inner involution displaces at least two dimensions per
deleted summand, allowing arbitrary mixing among those summands. -/
theorem inner_involution_bound {ι : Type*} [Fintype ι]
    (T : Module.End (ZMod 2) (ι → C)) (p : Alt) (hp : p * p = 1) (hne : p ≠ 1)
    (hT : ∀ (g : Alt) v, T (deletedSumAction ι g.val v) =
      deletedSumAction ι (p.val * g.val * p.val⁻¹) (T v)) :
    2 * Fintype.card ι ≤ operatorFixedCodim T := by
  have h := Nat.mul_le_mul_left (Fintype.card ι) (core_inner_displacement p hp hne)
  have hp' : p.val * p.val = 1 := congrArg Subtype.val hp
  simpa only [Nat.mul_comm] using h.trans (amplified_involution_bound T p.val hp' hT)

end Representation.AlternatingFive.AmplifiedDeleted
