module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.RootLifts
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Multiplication
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# An involutory highest-root lift and all six additive root sections

In the genuine arms radical, the highest-root value at 1 is both the
commutator of the first two long roots and the commutator of the last two
short roots. The first of these short roots commutes with both long roots.
The explicit arms coordinate multiplication proves all four identities,
including the cubic trace Tr(1) = 1 and the literal central quotient.

In any central extension, conjugating a commutator by an element whose image
commutes with both entries leaves that commutator unchanged. Comparing the
two expressions above makes the lifted short commutator commute with its
first entry. That entry is involutory by the additive PSL₂(8) lift, so the
commutator identity for its square proves that the highest-root lift is also
involutory. This does not infer the order of a lift from its image.

The Weyl transport and binary fixed-field map in `RootLifts` now construct
all six additive sections without extra assumptions. Inter-root correction
relations remain a separate obligation; `universalRootSections` alone does
not assert the multiplier result.

Sources: GLS3 §2.4.5(b)(1–2), §6.1; Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section

open Triality.Standard
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open PerfectCentralCovering
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

private theorem commute_commutator_of_images {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E) (a b c : E)
    (ha : Commute (f c) (f a)) (hb : Commute (f c) (f b)) :
    Commute c ⁅a, b⁆ := by
  have h : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · simp only [map_mul, map_inv]
      rw [ha.eq, mul_inv_cancel_right]
    · simp only [map_mul, map_inv]
      rw [hb.eq, mul_inv_cancel_right]
  exact mul_inv_eq_iff_eq_mul.mp h

/-- Two expressions for one base commutator force an involutory lift.
Only the short-root lift c is assumed to be involutory. -/
theorem commutator_square_of_comparison {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E) (a b c d : E)
    (ha : Commute (f c) (f a)) (hb : Commute (f c) (f b))
    (he : ⁅f c, f d⁆ = ⁅f a, f b⁆) (hc : c ^ 2 = 1) : ⁅c, d⁆ ^ 2 = 1 := by
  have hca : Commute c ⁅a, b⁆ := commute_commutator_of_images f hk a b c ha hb
  have hcc : Commute c ⁅c, d⁆ := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl
      (show f ⁅c, d⁆ = f ⁅a, b⁆ by simpa only [map_commutatorElement] using he)]
    exact hca.commutator_eq
  have h := commutatorElement_mul_left_eq_conj_mul c c d
  rw [hcc.eq, mul_inv_cancel_right, ← pow_two, hc, commutatorElement_one_left] at h
  simpa only [pow_two] using h.symm

open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers

private def armsValue (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P) :
    Carrier P := (armsEquiv P hp v).val

private theorem armsValue_factorization (P : Parameters) (hp : P.prime = 2)
    (v : ArmsParameters P) :
    armsValue P hp v = long P hp 0 (v.2 0) * short P hp 1 (v.1 0) *
      short P hp 2 (v.1 1) * long P hp 1 (v.2 1) * long P hp 2 (v.2 2) := by
  have hv : armsValue P hp v = toCarrier P (rootElement P hp .arms v) := rfl
  rw [hv, rootElement_factorization]
  simp [extendOrbit]

private theorem armsValue_commutator (P : Parameters) (hp : P.prime = 2)
    (v w : ArmsParameters P) :
    ⁅armsValue P hp v, armsValue P hp w⁆ =
      long P hp 2 (armsCommutator P v w) := by
  have h := congrArg (armsSubgroup P).subtype (armsEquiv_commutator P hp v w)
  change ⁅armsValue P hp v, armsValue P hp w⁆ = _ at h
  rw [h]
  change armsValue P hp (centralParameters P _) = _
  rw [armsValue_factorization]
  simp [centralParameters]

private theorem long_pair_commutator (P : Parameters) (hp : P.prime = 2) :
    ⁅long P hp 0 1, long P hp 1 1⁆ = long P hp 2 1 := by
  have h := armsValue_commutator P hp (0, ![1,0,0]) (0, ![0,1,0])
  simpa [armsValue_factorization, armsCommutator, armsCocycle] using h

private theorem short_pair_commutator (P : Parameters) (hp : P.prime = 2) :
    ⁅short P hp 1 1, short P hp 2 1⁆ = long P hp 2 1 := by
  have h := armsValue_commutator P hp (![1,0], 0) (![0,1], 0)
  have htrace : Centers.cubicTrace P 1 = 1 := Centers.cubicTrace_fixed P hp 1
  simpa [armsValue_factorization, armsCommutator, armsCocycle, armsPairing,
    -fieldFrobenius_apply, htrace] using h

private theorem short_long_zero_commute (P : Parameters) (hp : P.prime = 2) :
    Commute (short P hp 1 1) (long P hp 0 1) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := armsValue_commutator P hp (![1,0], 0) (0, ![1,0,0])
  simpa [armsValue_factorization, armsCommutator, armsCocycle] using h

private theorem short_long_one_commute (P : Parameters) (hp : P.prime = 2) :
    Commute (short P hp 1 1) (long P hp 1 1) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := armsValue_commutator P hp (![1,0], 0) (0, ![0,1,0])
  simpa [armsValue_factorization, armsCommutator, armsCocycle] using h

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one

/-- The highest long-root candidate is an actual commutator of the two lifted short roots. -/
def highestLift {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) : E :=
  ⁅shortRootLift f hf hk 1 (.ofAdd 1), shortRootLift f hf hk 2 (.ofAdd 1)⁆

theorem highestLift_spec {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    highestLift f hf hk ^ 2 = 1 ∧ f (highestLift f hf hk) = long P (binaryParameters_prime 1 Nat.zero_lt_one) 2 1 := by
  let c := shortRootLift f hf hk 1 (.ofAdd 1)
  let d := shortRootLift f hf hk 2 (.ofAdd 1)
  have hc : f c = short P (binaryParameters_prime 1 Nat.zero_lt_one) 1 1 :=
    shortRootLift_project f hf hk 1 1
  have hd : f d = short P (binaryParameters_prime 1 Nat.zero_lt_one) 2 1 :=
    shortRootLift_project f hf hk 2 1
  obtain ⟨a, ha⟩ := hf (long P (binaryParameters_prime 1 Nat.zero_lt_one) 0 1)
  obtain ⟨b, hb⟩ := hf (long P (binaryParameters_prime 1 Nat.zero_lt_one) 1 1)
  have hca : Commute (f c) (f a) := by
    rw [hc, ha]
    exact short_long_zero_commute P (binaryParameters_prime 1 Nat.zero_lt_one)
  have hcb : Commute (f c) (f b) := by
    rw [hc, hb]
    exact short_long_one_commute P (binaryParameters_prime 1 Nat.zero_lt_one)
  have he : ⁅f c, f d⁆ = ⁅f a, f b⁆ := by
    rw [hc, hd, ha, hb, short_pair_commutator, long_pair_commutator]
  have hc2 : c ^ 2 = 1 := by
    have ht : (Multiplicative.ofAdd (1 : ExtensionField P)) ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      change (1 : GaloisField 2 3) + 1 = 0
      exact CharTwo.add_self_eq_zero _
    change (shortRootLift f hf hk 1 (.ofAdd 1)) ^ 2 = 1
    rw [← map_pow, ht, map_one]
  change ⁅c,d⁆ ^ 2 = 1 ∧ f ⁅c,d⁆ = _
  refine ⟨commutator_square_of_comparison f hk a b c d hca hcb he hc2, ?_⟩
  rw [map_commutatorElement, hc, hd]
  exact short_pair_commutator P (binaryParameters_prime 1 Nat.zero_lt_one)

/-- Six additive lifts in every central extension of the genuine smallest carrier. -/
def initialRootSections {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    RootSections 1 Nat.zero_lt_one f :=
  rootSectionsOfHighestLift f hf hk (highestLift f hf hk)
    (highestLift_spec f hf hk).1 (highestLift_spec f hf hk).2

/-- The actual root sections in the canonical universal covering group. -/
def universalRootSections : RootSections 1 Nat.zero_lt_one (universalProjection G) :=
  initialRootSections (universalProjection G) (universalProjection_surjective G)
    (universalProjection_ker_le_center G)


end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
