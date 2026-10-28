module

public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.CoveringKernelBound

/-!
# Natural covers in the ordinary unitary cases

The scalar kernel of the literal special-unitary projection is cyclic of
order `gcd(n,q+1)`. In dimension four over an even fixed field it is trivial,
so projective perfectness transfers to the matrix group. A perfect matrix
group gives a genuine quasisimple covering of its projective image.

This is the natural-cover part of Aschbacher--Smith I.1.3--4, printed
pp.407--408, and GLS3 Section 6.1. Kernel calculations do not assert the
universal property; that requires a separate upper bound for central covers.
-/

@[expose] public noncomputable section

open BenderSuzuki.MatrixGroups Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary

variable {F : Type*} [Field F] [Finite F]

instance projectiveFinite {n : ℕ} (J : HermitianForm n F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective _ (project_surjective J)

/-- The actual scalar kernel is a cyclic group of the indicated order. -/
def kernelEquiv {n q : ℕ} [NeZero n] (J : HermitianForm n F)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    (project J).ker ≃* Multiplicative (ZMod (Nat.gcd n (q + 1))) := by
  let e := scalarKernelEquiv J hconj
  let : IsCyclic (project J).ker := e.isCyclic.mp inferInstance
  apply mulEquivOfCyclicCardEq
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact card_project_kernel J hconj hcard

/-- The Mersenne condition needed for the canonical kernel is `4 ∣ q+1`. -/
theorem gcd_four_mersenne {q : ℕ} (hq : 3 < q)
    (hm : ∃ k : ℕ, q + 1 = 2 ^ k) : Nat.gcd 4 (q + 1) = 4 := by
  obtain ⟨k, hk⟩ := hm
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hk <;> omega
  apply Nat.gcd_eq_left_iff_dvd.mpr
  rw [hk]
  exact Nat.pow_dvd_pow 2 hk2

/-- The natural degree-four Mersenne kernel is the actual cyclic group C₄. -/
def fourMersenneKernelEquiv (J : HermitianForm 4 F) {q : ℕ}
    (hq : 3 < q) (hm : ∃ k : ℕ, q + 1 = 2 ^ k)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    (project J).ker ≃* Multiplicative (ZMod 4) := by
  have e := kernelEquiv J hcard hconj
  rw [gcd_four_mersenne hq hm] at e
  exact e

/-- Four is coprime to one more than an even number. -/
theorem gcd_four_even {q : ℕ} (hq : Even q) : Nat.gcd 4 (q + 1) = 1 := by
  have h : Nat.Coprime 2 (q + 1) := Nat.coprime_two_left.mpr hq.add_one
  exact h.pow_left 2

/-- The actual degree-four projection has trivial kernel for even q. -/
theorem fourEven_kernel_eq_bot (J : HermitianForm 4 F) {q : ℕ}
    (hq : Even q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) : (project J).ker = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [card_project_kernel J hconj hcard, gcd_four_even hq]

/-- The literal natural projection is an isomorphism in even degree four. -/
def fourEvenProjectEquiv (J : HermitianForm 4 F) {q : ℕ}
    (hq : Even q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q) :
    J.specialSubgroup ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (project J)
    ⟨(project J).ker_eq_bot_iff.mp (fourEven_kernel_eq_bot J hq hcard hconj),
      project_surjective J⟩

/-- Projective perfectness gives perfectness of SU₄ in the even case. -/
theorem fourEven_isPerfect (J : HermitianForm 4 F) {q : ℕ}
    (hq : Even q) (hcard : Nat.card F = q ^ 2)
    (hconj : ∀ x, J.conj x = x ^ q)
    [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)] :
    Group.IsPerfect J.specialSubgroup :=
  Group.IsPerfect.ofSurjective
    (f := (fourEvenProjectEquiv J hq hcard hconj).symm.toMonoidHom)
    (fourEvenProjectEquiv J hq hcard hconj).symm.surjective

/-- The natural SU₅(4) kernel is C₅; its matrices are over a field of order 16. -/
def fiveFourKernelEquiv (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) :
    (project J).ker ≃* Multiplicative (ZMod 5) := by
  simpa using kernelEquiv J (q := 4) (by simpa using hcard) hconj

variable {n : ℕ} (J : HermitianForm n F) [Group.IsPerfect J.specialSubgroup]

/-- Package the canonical map as a perfect central extension. -/
def naturalCentralCover :
    PerfectCentralCovering.Cover J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) where
  toMonoidHom := project J
  surjective := project_surjective J
  isPerfect := inferInstance
  ker_le_center := project_kernel_le_center J

omit [Finite F] in
/-- Only projective quasisimplicity, inherited from the source model, is needed. -/
theorem natural_isQuasisimple [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    IsQuasisimple J.specialSubgroup := (naturalCentralCover J).isQuasisimple

/-- The covering retains the literal projective homomorphism. -/
def naturalCover [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)] :
    letI := natural_isQuasisimple J
    Covering J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  letI := natural_isQuasisimple J
  exact (naturalCentralCover J).toCovering

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
