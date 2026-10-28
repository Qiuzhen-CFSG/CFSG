module
public import Theory.Representation.BinaryOffender.PairActorRank
/-!
# Rank bounds in the normalizer of an irreducible binary SL₂ square

An elementary actor exchanging the two factors has rank at most n+1.
A larger actor preserves both factors, whose simultaneous conjugation action
is faithful and has rank at most 2n. Above rank n each single-factor
projection has a nontrivial kernel. These are kernels of the original actor,
not replacement actors faithful on one factor.

The determinant large-actor calculation uses both kernels to produce
independently supported inner involutions.
Source: Aschbacher--Smith H.1.1(2), D.3.7, printed pp.378,197--199,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace Representation.BinaryOffender.SquarePreserving
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [IsQuasisimple SL(2,F)]

/-- An elementary actor larger than the exchanging bound preserves both factors. -/
theorem preserving_of_rank_gt
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ) (hZ : center SL(2,F) = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (linearNormalizer σ)) [IsElementaryAbelian 2 A]
    (hr : n+1 < rank A) : ∀ a ∈ A, a.val ∈ group σ := by
  intro a ha
  rcases involution_preserves_or_exchanges σ hZ hf a
    (elemPow_eq_one_of_isElementaryAbelian a ha) with hp | ⟨α,hα⟩
  · exact hp
  · have hb := twisted_exchange_rank_le σ hZ hi hf A a ha α hα
    have hn := Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF
    omega

/-- The entire elementary tensor normalizer has rank at most twice the field degree. -/
theorem normalizer_rank_le_twice_degree
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ) (hZ : center SL(2,F) = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (linearNormalizer σ)) [IsElementaryAbelian 2 A] : rank A ≤ 2*n := by
  by_cases hr : rank A ≤ n+1
  · omega
  have hp := preserving_of_rank_gt σ hi hf hZ n hn hF A (by omega)
  let j : A →* group σ := ((linearNormalizer σ).subtype.comp A.subtype).codRestrict
    (group σ) (fun a => hp a a.property)
  have hj : Function.Injective j := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : group σ => z.val) h))
  let : IsElementaryAbelian 2 j.range :=
    IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hb := even_elementary_rank_le σ hi hf n hn hF j.range
  have he : rank j.range = rank A :=
    (congrArg (Nat.log 2) (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv)).symm
  rwa [he] at hb

omit [FiniteDimensional (ZMod 2) V] [IsQuasisimple SL(2,F)] in
/-- A projection to one factor cannot detect an elementary actor of rank above n. -/
theorem exists_centralizing_member_of_rank_gt
    (σ : Representation (ZMod 2) (SL(2,F) × SL(2,F)) V)
    (n : ℕ) (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (A : Subgroup (group σ)) [Finite A] [IsElementaryAbelian 2 A]
    (J : Subgroup (group σ)) [J.Normal] (e : SL(2,F) ≃* J)
    (hr : n < rank A) : ∃ a ∈ A, a ≠ 1 ∧ a ∈ centralizer (J : Set (group σ)) := by
  by_contra! h
  let f := (MulAut.conjNormal : group σ →* MulAut J).comp A.subtype
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    by_contra hane
    apply h a a.property hane
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  let k := (MulAut.congr e.symm).toMonoidHom.comp f
  have hki : Function.Injective k := (MulAut.congr e.symm).injective.comp hfi
  let : IsElementaryAbelian 2 k.range :=
    IsElementaryAbelian.of_surjective k.rangeRestrict k.rangeRestrict_surjective
  have hb := (primeRank_le_iff_elementary_card_le _).mp
    (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn hF)
    k.range (inferInstance : IsElementaryAbelian 2 k.range)
  rw [←Nat.card_congr (MonoidHom.ofInjective hki).toEquiv] at hb
  have hl := Nat.log_mono_right (b := 2) hb
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  exact (Nat.not_lt_of_ge hl) hr
end Representation.BinaryOffender.SquarePreserving
