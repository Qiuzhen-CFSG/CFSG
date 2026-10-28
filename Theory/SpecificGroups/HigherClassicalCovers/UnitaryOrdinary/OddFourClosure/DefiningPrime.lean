module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.Reduction
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Collection

/-!
# Defining-prime assembly for ordinary SU₄ coverings

The root collection theorem supplies the literal section once compatible
positive-root lifts have been constructed. Transfer then excludes a kernel
of order q, provided the positive subgroup has index prime to q. We retain
both obligations explicitly here, and transport covers by an actual
special-unitary equivalence, leaving their kernels unchanged. The final
application uses the prime-degree quotient reduction for arbitrary kernels.

This is conditional assembly for Aschbacher--Smith I.1.4(3), printed p.408,
and GLS3 §6.1. It is not the defining-prime theorem until the independent
index and root-lifting calculations have discharged the two premises.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
universe u
variable {F : Type u} [Field F] (J : HermitianForm 4 F)

/-- The missing lifting calculation is on the actual hyperbolic matrix group,
for precisely the prime-degree covers needed by prime-kernel reduction. -/
def PrimeKernelRootLifts (q : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (HyperbolicSU J)),
    Nat.card f.toMonoidHom.ker = q → Nonempty (PositiveRootLifts J f.toMonoidHom)

/-- Change only the target coordinates of a cover; no quotient or new kernel
is introduced. -/
def hyperbolicCover {E : Type u} [Group E]
    (e : HyperbolicSU J ≃* J.specialSubgroup)
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    PerfectCentralCovering.Cover E (HyperbolicSU J) where
  toMonoidHom := e.symm.toMonoidHom.comp f.toMonoidHom
  surjective := e.symm.surjective.comp f.surjective
  isPerfect := f.isPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective]
    exact f.ker_le_center

/-- The cover is marked by the literal change-of-basis equivalence. -/
theorem hyperbolicCover_projection {E : Type u} [Group E]
    (e : HyperbolicSU J ≃* J.specialSubgroup)
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    e.toMonoidHom.comp (hyperbolicCover J e f).toMonoidHom = f.toMonoidHom := by
  apply MonoidHom.ext
  intro x
  exact e.apply_symm_apply (f.toMonoidHom x)

/-- In particular, coordinate transport preserves the exact subgroup kernel. -/
theorem hyperbolicCover_kernel {E : Type u} [Group E]
    (e : HyperbolicSU J ≃* J.specialSubgroup)
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    (hyperbolicCover J e f).toMonoidHom.ker = f.toMonoidHom.ker :=
  MonoidHom.ker_comp_of_injective _ _ e.symm.injective

variable [Finite F]

/-- Consume compatible lifted roots and the prime-to-q index using the
actual subgroup inclusion in the transfer theorem. -/
theorem not_dvd_hyperbolic_kernel_of_root_lifts {q : ℕ} (hp : q.Prime)
    (hindex : ¬ q ∣ (positive J).index)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (HyperbolicSU J))
    (L : PositiveRootLifts J f.toMonoidHom) :
    ¬ q ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact q.Prime := ⟨hp⟩
  obtain ⟨s,hs⟩ := L.exists_positive_section
  exact PerfectCentralCovering.not_dvd_card_kernel_of_section f (positive J) hindex s hs

/-- Conditional prime-degree exclusion in the original arbitrary Hermitian
form. The root-lifting and index obligations remain visible. -/
theorem noPrimeKernel_of_root_lifts {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    (hindex : ¬ q ∣ (positive J).index) (hlifts : PrimeKernelRootLifts J q) :
    OddFourClosure.NoPrimeKernel J q := by
  obtain ⟨e⟩ := exists_hyperbolic_special_equiv J hp hcard hconj
  intro E _ _ f hdegree
  have hd : Nat.card (hyperbolicCover J e f).toMonoidHom.ker = q := by
    rw [hyperbolicCover_kernel, hdegree]
  obtain ⟨L⟩ := hlifts E (hyperbolicCover J e f) hd
  exact not_dvd_hyperbolic_kernel_of_root_lifts J hp hindex
    (hyperbolicCover J e f) L (hd ▸ dvd_rfl)

/-- Prime-degree reduction applies the same conditional result to every
finite covering kernel, including those of mixed prime order. -/
theorem not_dvd_card_kernel_of_root_lifts {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    (hindex : ¬ q ∣ (positive J).index) (hlifts : PrimeKernelRootLifts J q)
    {E : Type u} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E J.specialSubgroup) :
    ¬ q ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact q.Prime := ⟨hp⟩
  exact f.not_dvd_card_kernel_of_no_prime_kernel
    (noPrimeKernel_of_root_lifts J hp hcard hconj hindex hlifts)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
