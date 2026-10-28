module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.Sections
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates.Checker
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates.Data56
public import Theory.Representation.HigmanSims.LargeModels.Binary.Small.SectionCertificates.Data132

/-!
# Certified exterior-square sections for the degree-56 and degree-132 HS models

The supplied kernel rows N and lifts U are independent: the inverse of their
pivot minor, embedded at the pivot columns, gives a right inverse in exactly
kernel-then-lift order. For each literal exterior-square generator T the
checked identities are N*T = K*N and U*T = C*N + M*U, with M the published
target matrix. These give unconditional witnesses of the `SectionCertificate`
contract; constructing the dual quotient action is a separate consumer.

`SectionCertificates.Ambient`, `Data56`, and `Data132` keep the numerical
checks under narrow imports. Here their packed products are interpreted as
matrix equations and assembled into the actual records. No marked comparison,
carrier action, or representation-theoretic hypothesis is needed.

Source: ATLAS HSG1-f2r20B0, HSG1-f2r56B0 and HSG1-f2r132B0;
`Binary/source/section56.json`, `section132.json`, and `source/README.md`.
Generation, attribution, and measurements: `SectionCertificates/source/README.md`.
-/

@[expose] public section

open Matrix Thompson.BinaryMatrix
namespace Representation.HigmanSims.LargeModels.Binary.Small
namespace SectionCertificates

private theorem bit_and (a b j : ℕ) : bit (a &&& b) j = bit a j * bit b j := by
  simp only [bit, Nat.testBit_and]
  cases a.testBit j <;> cases b.testBit j <;> decide

private theorem pair_eq (i : Fin 190) : Ambient.pair i = exteriorPair i := by
  rfl

private theorem exterior_checked (a hi lo t : Array ℕ)
    (hh : ∀ i : Fin 20, ∀ j : Fin 190,
      hi[i.val]!.testBit j.val = a[i.val]!.testBit (Ambient.pair j).1.val)
    (hl : ∀ i : Fin 20, ∀ j : Fin 190,
      lo[i.val]!.testBit j.val = a[i.val]!.testBit (Ambient.pair j).2.val)
    (ht : ∀ i : Fin 190, t[i.val]! =
      (hi[(Ambient.pair i).1.val]! &&& lo[(Ambient.pair i).2.val]!) ^^^
      (lo[(Ambient.pair i).1.val]! &&& hi[(Ambient.pair i).2.val]!)) :
    rect 190 190 t = exteriorMatrix (decode 20 a) := by
  ext i j
  change bit t[i.val]! j.val =
    bit a[(exteriorPair i).1.val]! (exteriorPair j).1.val *
      bit a[(exteriorPair i).2.val]! (exteriorPair j).2.val +
    bit a[(exteriorPair i).1.val]! (exteriorPair j).2.val *
      bit a[(exteriorPair i).2.val]! (exteriorPair j).1.val
  rw [ht i, bit_xor, bit_and, bit_and]
  simp only [bit, hh, hl, pair_eq]

/-- The first packed actor is the literal exterior-square generator. -/
theorem ambient_a : rect 190 190 Ambient.a = ambientGenerator 0 :=
  exterior_checked Sporadic.LeechRelated.HS.Twenty.aRows _ _ _
    Ambient.aHigh_checked Ambient.aLow_checked Ambient.a_checked

/-- The second packed actor is the literal exterior-square generator. -/
theorem ambient_b : rect 190 190 Ambient.b = ambientGenerator 1 :=
  exterior_checked Sporadic.LeechRelated.HS.Twenty.bRows _ _ _
    Ambient.bHigh_checked Ambient.bLow_checked Ambient.b_checked

end SectionCertificates
open SectionCertificates

/-- An unconditional certificate for the literal degree-56 section of exterior-square(20). -/
def sectionCertificate56 : SectionCertificate 0 1 where
  kernelRows := rect 1 190 SectionCertificates.D56.kernel
  liftRows := rect 56 190 SectionCertificates.D56.lifts
  retract := rightInverse 1 56 SectionCertificates.D56.retract
  independent := independent_checked _ _ _ SectionCertificates.D56.retract_size
    SectionCertificates.D56.kernel_retract_checked SectionCertificates.D56.lifts_retract_checked
  kernelAction s := if s = 0 then rect 1 1 SectionCertificates.D56.aKernel
    else rect 1 1 SectionCertificates.D56.bKernel
  corrections s := if s = 0 then rect 56 1 SectionCertificates.D56.aCorrection
    else rect 56 1 SectionCertificates.D56.bCorrection
  kernel_invariant := by
    intro s
    fin_cases s
    · change rect 1 190 SectionCertificates.D56.kernel * ambientGenerator 0 =
        rect 1 1 SectionCertificates.D56.aKernel * rect 1 190 SectionCertificates.D56.kernel
      rw [← ambient_a]
      exact mul_eq_checked _ _ _ _ Ambient.a_size SectionCertificates.D56.kernel_size
        SectionCertificates.D56.a_kernel_checked
    · change rect 1 190 SectionCertificates.D56.kernel * ambientGenerator 1 =
        rect 1 1 SectionCertificates.D56.bKernel * rect 1 190 SectionCertificates.D56.kernel
      rw [← ambient_b]
      exact mul_eq_checked _ _ _ _ Ambient.b_size SectionCertificates.D56.kernel_size
        SectionCertificates.D56.b_kernel_checked
  lift_action := by
    intro s
    fin_cases s
    · change rect 56 190 SectionCertificates.D56.lifts * ambientGenerator 0 =
        rect 56 1 SectionCertificates.D56.aCorrection * rect 1 190 SectionCertificates.D56.kernel +
        rect 56 56 Binary.D56.aRows * rect 56 190 SectionCertificates.D56.lifts
      rw [← ambient_a]
      exact mul_eq_add_checked _ _ _ _ _ _ Ambient.a_size SectionCertificates.D56.kernel_size
        SectionCertificates.D56.lifts_size SectionCertificates.D56.a_lifts_checked
    · change rect 56 190 SectionCertificates.D56.lifts * ambientGenerator 1 =
        rect 56 1 SectionCertificates.D56.bCorrection * rect 1 190 SectionCertificates.D56.kernel +
        rect 56 56 Binary.D56.bRows * rect 56 190 SectionCertificates.D56.lifts
      rw [← ambient_b]
      exact mul_eq_add_checked _ _ _ _ _ _ Ambient.b_size SectionCertificates.D56.kernel_size
        SectionCertificates.D56.lifts_size SectionCertificates.D56.b_lifts_checked

/-- An unconditional certificate for the literal degree-132 section of exterior-square(20). -/
def sectionCertificate132 : SectionCertificate 1 57 where
  kernelRows := rect 57 190 SectionCertificates.D132.kernel
  liftRows := rect 132 190 SectionCertificates.D132.lifts
  retract := rightInverse 57 132 SectionCertificates.D132.retract
  independent := independent_checked _ _ _ SectionCertificates.D132.retract_size
    SectionCertificates.D132.kernel_retract_checked SectionCertificates.D132.lifts_retract_checked
  kernelAction s := if s = 0 then rect 57 57 SectionCertificates.D132.aKernel
    else rect 57 57 SectionCertificates.D132.bKernel
  corrections s := if s = 0 then rect 132 57 SectionCertificates.D132.aCorrection
    else rect 132 57 SectionCertificates.D132.bCorrection
  kernel_invariant := by
    intro s
    fin_cases s
    · change rect 57 190 SectionCertificates.D132.kernel * ambientGenerator 0 =
        rect 57 57 SectionCertificates.D132.aKernel * rect 57 190 SectionCertificates.D132.kernel
      rw [← ambient_a]
      exact mul_eq_checked _ _ _ _ Ambient.a_size SectionCertificates.D132.kernel_size
        SectionCertificates.D132.a_kernel_checked
    · change rect 57 190 SectionCertificates.D132.kernel * ambientGenerator 1 =
        rect 57 57 SectionCertificates.D132.bKernel * rect 57 190 SectionCertificates.D132.kernel
      rw [← ambient_b]
      exact mul_eq_checked _ _ _ _ Ambient.b_size SectionCertificates.D132.kernel_size
        SectionCertificates.D132.b_kernel_checked
  lift_action := by
    intro s
    fin_cases s
    · change rect 132 190 SectionCertificates.D132.lifts * ambientGenerator 0 =
        rect 132 57 SectionCertificates.D132.aCorrection * rect 57 190 SectionCertificates.D132.kernel +
        rect 132 132 Binary.D132.aRows * rect 132 190 SectionCertificates.D132.lifts
      rw [← ambient_a]
      exact mul_eq_add_checked _ _ _ _ _ _ Ambient.a_size SectionCertificates.D132.kernel_size
        SectionCertificates.D132.lifts_size SectionCertificates.D132.a_lifts_checked
    · change rect 132 190 SectionCertificates.D132.lifts * ambientGenerator 1 =
        rect 132 57 SectionCertificates.D132.bCorrection * rect 57 190 SectionCertificates.D132.kernel +
        rect 132 132 Binary.D132.bRows * rect 132 190 SectionCertificates.D132.lifts
      rw [← ambient_b]
      exact mul_eq_add_checked _ _ _ _ _ _ Ambient.b_size SectionCertificates.D132.kernel_size
        SectionCertificates.D132.lifts_size SectionCertificates.D132.b_lifts_checked

end Representation.HigmanSims.LargeModels.Binary.Small
