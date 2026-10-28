module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.CoordinateAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.IntrinsicCenter.Pairing

/-!
# Binary coordinates for the actual max2 central quotient

Products of the twelve noncentral quotient generators define a homomorphism
from the additive binary twelve-space onto the literal N/<t>. Generation
proves surjectivity. If a binary product is trivial in the quotient, its lift
is a power of t and hence commutes with every generator. The certified
commutator pairing and its proved radical then force all twelve coordinates
to vanish, proving injectivity. The inverse isomorphism sends each specified
generator to the corresponding standard basis vector.

This uses the exact pairing proved in `IntrinsicCenter.Pairing`, whose
entries are the actual matrix-certified relations. No intrinsic-center bound,
normal-form count, global order, extraspeciality or quotient faithfulness is
assumed. Source motivation: GLS3 Table 5.3i, printed p.270; the ATLAS words
and relation witnesses are documented in `Certificates.Relations`.
-/

set_option maxRecDepth 4000
@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
namespace OuterImageComparison
open NormalClosureControl NormalClosureControl.IntrinsicCenter
open Janko4.Cardinality.KernelCount
open scoped IsMulCommutative

lemma quotientBasis_square (i : Fin 13) : quotientBasis i * quotientBasis i = 1 := by
  have hs : basisElement i ^ 2 = 1 ∨ basisElement i ^ 2 = centralWord := by
    rcases basis_square i with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  change projection (basisElement i) * projection (basisElement i) = 1
  rw [← map_mul, ← pow_two]
  rcases hs with h | h
  · rw [h, map_one]
  · rw [h, projection_centralWord]

/-- A quotient relation has zero noncentral coordinates, by the actual pairing. -/
lemma quotient_binaryProduct_one (v : Fin 13 → Bool)
    (h : binaryProduct quotientBasis v = 1) : ∀ i : Fin 12, v i.succ = false := by
  have hn : binaryProduct basisElement v ∈ centralPowers := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection (binaryProduct basisElement v) = 1
    rw [map_binaryProduct]
    exact h
  have hz : binaryProduct basis v ∈ Subgroup.zpowers subgroupInvolution := by
    have hm : binaryProduct basis v ∈ centralPowers.map localNormalClosure.subtype :=
      ⟨binaryProduct basisElement v, hn, map_binaryProduct localNormalClosure.subtype basisElement v⟩
    change binaryProduct basis v ∈ (Subgroup.zpowers centralWord).map localNormalClosure.subtype at hm
    rwa [MonoidHom.map_zpowers] at hm
  have hc : binaryProduct basis v ∈ Subgroup.center localSubgroup :=
    (Subgroup.zpowers_le.mpr involution_mem_center) hz
  have hne : subgroupInvolution ≠ 1 := by
    intro he
    have ho := orderOf_subgroupInvolution
    rw [he, orderOf_one] at ho
    exact (by decide : (1 : ℕ) ≠ 2) ho
  have hzero : ∀ i, pairing v (commutatorForm i) = false := by
    intro i
    have ht := binaryProduct_twist basis v (commutatorForm i) (basis i)
      subgroupInvolution involution_mem_center involution_pow_two (basis_twist i)
    rw [← (Subgroup.mem_center_iff.mp hc) (basis i)] at ht
    have hb : bit subgroupInvolution (pairing v (commutatorForm i)) = 1 := by
      apply mul_left_cancel (a := basis i * binaryProduct basis v)
      simpa only [mul_one] using ht.symm
    cases he : pairing v (commutatorForm i) with
    | false => rfl
    | true => exact (hne (by simpa only [he, bit, Bool.true_eq, if_true] using hb)).elim
  intro i
  exact radical v hzero i.succ (Fin.succ_ne_zero i)

/-- Convert binary field coordinates to the thirteen product bits, central bit zero. -/
def coordinateBits (v : Multiplicative BinaryVector) : Fin 13 → Bool :=
  Fin.cases false (fun i => v.toAdd i == 1)

private lemma binary_add (a b : ZMod 2) :
    ((a + b) == 1) = ((a == 1) ^^ (b == 1)) := by
  revert a b
  decide +kernel

private lemma binary_eq_zero (a : ZMod 2) (h : (a == 1) = false) : a = 0 := by
  have hh : ∀ b : ZMod 2, (b == 1) = false → b = 0 := by decide +kernel
  exact hh a h

/-- The product of the actual quotient generators with the given binary coordinates. -/
def decodeCoordinates : Multiplicative BinaryVector →* CentralQuotient where
  toFun v := binaryProduct quotientBasis (coordinateBits v)
  map_one' := by
    change binaryProduct quotientBasis (coordinateBits 1) = 1
    rw [show coordinateBits 1 = (fun _ => false) by decide +kernel]
    exact binaryProduct_zero _
  map_mul' v w := by
    change binaryProduct quotientBasis (coordinateBits (v * w)) =
      binaryProduct quotientBasis (coordinateBits v) * binaryProduct quotientBasis (coordinateBits w)
    rw [binaryProduct_mul _ quotientBasis_square quotientBasis_commute]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact binary_add (v.toAdd j) (w.toAdd j)

private lemma coordinateBits_vectorBasis_succ (i : Fin 12) :
    coordinateBits (vectorBasis i.succ) = fun j => decide (j = i.succ) := by
  revert i
  decide +kernel

lemma decodeCoordinates_basis (i : Fin 13) : decodeCoordinates (vectorBasis i) = quotientBasis i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change decodeCoordinates 1 = quotientBasis 0
    rw [map_one, quotientBasis_zero]
  · change binaryProduct quotientBasis (coordinateBits (vectorBasis j.succ)) = quotientBasis j.succ
    rw [coordinateBits_vectorBasis_succ, binaryProduct_single]

lemma decodeCoordinates_surjective : Function.Surjective decodeCoordinates := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← quotientBasis_generate]
  apply (Subgroup.closure_le _).mpr
  rintro q ⟨i, rfl⟩
  exact ⟨vectorBasis i, decodeCoordinates_basis i⟩

lemma decodeCoordinates_injective : Function.Injective decodeCoordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  have hb := quotient_binaryProduct_one (coordinateBits v) hv
  change v = 1
  change v.toAdd = (0 : BinaryVector)
  funext i
  exact binary_eq_zero (v.toAdd i) (hb i)

/-- Coordinates on the literal quotient, with no group-shape or order premise. -/
noncomputable def coordinates : Coordinates :=
  (MulEquiv.ofBijective decodeCoordinates
    ⟨decodeCoordinates_injective, decodeCoordinates_surjective⟩).symm

lemma coordinates_respectsBasis : RespectsBasis coordinates := by
  intro i
  apply coordinates.symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact (decodeCoordinates_basis i).symm

end OuterImageComparison
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
