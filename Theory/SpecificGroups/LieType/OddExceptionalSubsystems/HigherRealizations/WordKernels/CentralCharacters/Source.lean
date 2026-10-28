module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Words
/-!
# The central coroot word is an E6 adjoint relation

The candidate parameters `(u,u²,1,1,u,u²)` annihilate every simple-root
character when `u³ = 1`. Integral root expansion then annihilates every root
character, so the actual E6 diagonal matrix, and hence the evaluated coroot
word, is the identity. This verifies the source-kernel direction of the
central parameter calculation without enumerating the roots or dividing by
three. The converse localization of arbitrary source relations is not assumed.

Source: GLS3 §§1.12 and 2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
open scoped BigOperators
open FaithfulSMul (algebraMap_injective)
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters
noncomputable section
attribute [local instance] Classical.decEq
section Generic
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]
omit [P.IsReduced] [Fintype ι] in
/-- Simple roots determine whether a torus parameter annihilates every root. -/
theorem rootScale_eq_one_of_simple (u : b.support → Fˣ)
    (h : ∀ i : b.support, integralChevalleyRootScale (P := P) u i = 1) (r : ι) :
    integralChevalleyRootScale (P := P) u r = 1 := by
  obtain ⟨f, _, _, hf⟩ := b.exists_root_eq_sum_int r
  have hp (q : b.support) :
      P.pairingIn ℤ r q = ∑ j ∈ b.support, f j • P.pairingIn ℤ j q :=
    algebraMap_injective ℤ R <| by
      simp_rw [RootPairing.algebraMap_pairingIn, map_sum,
        ← RootPairing.root_coroot_eq_pairing, hf, map_sum, map_zsmul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        RootPairing.root_coroot_eq_pairing, zsmul_eq_mul,
        RootPairing.algebraMap_pairingIn]
  have hp' (q : b.support) :
      P.pairingIn ℤ r q = ∑ j ∈ b.support, P.pairingIn ℤ j q * f j := by
    simpa only [zsmul_eq_mul, Int.cast_id, mul_comm] using hp q
  have hz (a : Fˣ) (s : Finset ι) (f : ι → ℤ) :
      a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
  simp only [integralChevalleyRootScale, hp', hz, zpow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.prod_zpow]
  change (integralChevalleyRootScale (P := P) u i) ^ (f i) = 1
  rw [h ⟨i, hi⟩, one_zpow]
end Generic

variable (F : Type*) [Field F]
/-- The literal six coordinates in the E6 source. -/
theorem centralParameter_source_simple (u : Fˣ) (i : Fin 6) :
    centralParameter F simpleIndex u (simpleIndex i) = ![u,u^2,1,1,u,u^2] i := by
  have he (i j : Fin 6) : simpleIndex i = simpleIndex j ↔ i = j :=
    typeE6RootPairing_baseEquiv.injective.eq_iff
  simp only [centralParameter, Pi.mul_apply, integralChevalleySimpleCorootParameter, he]
  fin_cases i <;> simp

/-- The six E6 root characters are trivial on the central parameter. -/
theorem centralParameter_source_scale (u : Fˣ) (hu : u ^ 3 = 1) (i : Fin 6) :
    integralChevalleyRootScale (P := Pairing) (centralParameter F simpleIndex u)
      (simpleIndex i) = 1 := by
  unfold integralChevalleyRootScale
  rw [← Equiv.prod_comp typeE6RootPairing_baseEquiv]
  have hp (k : Fin 6) : Pairing.pairingIn ℤ (simpleIndex i) (simpleIndex k) =
      typeE6CartanMatrix i k := typeE6RootPairing_base_cartan_apply i k
  simp only [centralParameter_source_simple, hp]
  have hs : u ^ 2 = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hu
  fin_cases i <;> simp [Fin.prod_univ_succ, typeE6CartanMatrix, hs]

/-- The corresponding E6 adjoint diagonal is the identity. -/
theorem centralMatrix_source (u : Fˣ) (hu : u ^ 3 = 1) :
    centralMatrix F simpleIndex u = 1 := by
  apply (integralChevalleyTorusElement_eq_one_iff_rootScale_eq_one _).mpr
  apply rootScale_eq_one_of_simple
  intro i
  obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
  exact centralParameter_source_scale F u hu i

/-- The explicit central word belongs to the literal source kernel. -/
theorem sourceSix_centralWord (u : Fˣ) (hu : u ^ 3 = 1) :
    sourceSix F (centralWord F u) = 1 := by
  apply Subtype.ext
  change ((splitCarrier F).subtype.comp (sourceSix F)) (centralWord F u) = 1
  rw [eval_centralWord F _ simpleIndex, centralMatrix_source F u hu]
  · intro s i t
    simp
  · exact hu
end
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters
