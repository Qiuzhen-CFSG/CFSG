module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.Diagonal
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.NormOneIndex
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

/-!
# Quadratic-torus applications to arbitrary unitary covers

For the actual rank-three diagonal torus in PSU₄, the signed swaps make its
full covering preimage abelian. The three-cycle norm argument then excludes a
prime from any finite perfect central kernel when the torus-by-cycle subgroup
has index prime to it. Orthonormalization and postcomposition transport this
calculation to the original Hermitian form without changing the covering kernel.
The paired-torus application uses the corresponding two-generator swap argument.

The full primary coefficient groups in `NormOneIndex` and `PairedTorus`
supply the required indices, including the three-cycle supplement when r = 3
divides p+1. Splitting p²−1 into (p+1)(p−1) therefore excludes every odd
nondefining prime dividing p²−1 from the kernel of every finite perfect
central cover, for every odd prime p and every original Hermitian form.

Source: Aschbacher–Smith A.2.17, printed p.39; perfect-cover and multiplier
conventions I.1.1–I.1.4, printed pp.407–408. No universality, natural-cover
lifting or Mersenne restriction is used.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open Theory.SpecificGroups.ClassicalUnitary

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining
open UnitaryQuadratic

/-- The explicit rank-three norm-one torus and its actual three-cycle exclude every prime absent from their index. -/
theorem unitary_not_dvd_kernel_of_diagonal_torus_index
    {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 4 F) (hJ : J.form = 1)
    (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)
    (ho : (Nat.card C).Coprime 2) {r : ℕ} [Fact r.Prime]
    (hi : ¬ r ∣ ((diagonalProjective J hJ C hC).range ⊔ zpowers (cycle J hJ)).index)
    {E : Type*} [Group E] [Finite E] (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  exact f.not_dvd_kernel_of_permuted_torus (diagonalProjective J hJ C hC)
    (diagonalProjective_injective J hJ C hC ho) ho
    (exists_coordinate_swap J hJ C hC) (cycle J hJ) (cycle_cube J hJ)
    (cycle_diagonal J hJ C hC) hi

/-- Orthonormalization applies the norm-one torus calculation to the original arbitrary-form cover and its literal kernel. -/
theorem unitary_not_dvd_kernel_of_normOne_torus_index
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p^2) (hconj : ∀ x, J.conj x = x^p)
    (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)
    (ho : (Nat.card C).Coprime 2)
    (hi : ¬ r ∣ ((diagonalProjective
      (UnitaryFourThree.identityForm J.conj J.conj_involutive) rfl C hC).range ⊔
      zpowers (cycle (UnitaryFourThree.identityForm J.conj J.conj_involutive) rfl)).index)
    {E : Type*} [Group E] [Finite E] (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 2) (by
    simpa only [← Nat.card_eq_fintype_card] using hF)
  obtain ⟨P,hP⟩ := J.exists_orthonormal_basis_of_prime_frobenius hconj hF
  let K : HermitianForm 4 F := UnitaryFourThree.identityForm J.conj J.conj_involutive
  let e := UnitaryFourThree.projectiveBasisEquiv J P hP
  let g := e.toMonoidHom.comp f.toMonoidHom
  have hgker : g.ker = f.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  let f' : Cover E (ProjectiveSpecialUnitaryMatrixGroup K) := {
    toMonoidHom := g
    surjective := e.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := hgker ▸ f.ker_le_center }
  have hn := unitary_not_dvd_kernel_of_diagonal_torus_index K rfl C hC ho hi f'
  change ¬ r ∣ Nat.card g.ker at hn
  rwa [hgker] at hn

/-- A paired torus in the original projective group excludes a prime once its generators, ambient swap and prime-to-r index are supplied. -/
theorem unitary_not_dvd_kernel_of_paired_torus_index
    {F : Type*} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (J : HermitianForm 4 F)
    (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (x y s : ProjectiveSpecialUnitaryMatrixGroup J)
    (hgen : closure ({x,y} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = T)
    (hxy : Commute x y) (hsx : s*x*s⁻¹ = y) (hsy : s*y*s⁻¹ = x)
    {m : ℕ} (hm : m.Coprime 2) (hx : x^m = 1) (hi : ¬ r ∣ T.index)
    {E : Type*} [Group E] [Finite E] (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_kernel_of_swapped_pair_at_prime_index T x y s hgen hxy hsx hsy hm hx hi

/-- The two torus cases exhaust every prime dividing the quadratic factor. -/
theorem unitary_prime_dvd_sq_sub_one_cases {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (h : r ∣ p^2 - 1) : r ∣ p + 1 ∨ r ∣ p - 1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsq : 1 ≤ p^2 := by nlinarith
  have he : p^2 - 1 = (p+1)*(p-1) := by
    nlinarith [Nat.sub_add_cancel hp, Nat.sub_add_cancel hsq]
  rw [he] at h
  exact (Fact.out : r.Prime).dvd_mul.mp h

/-- The quadratic-prime part of the degree-four unitary covering step in A.2.17:
every odd nondefining prime dividing p²−1 is absent from the kernel of every
finite perfect central cover of the original projective special unitary group. -/
theorem unitary_not_dvd_kernel_of_dvd_sq_sub_one
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p) (hd : r ∣ p ^ 2 - 1)
    {E : Type*} [Group E] [Finite E]
    (f : Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  rcases unitary_prime_dvd_sq_sub_one_cases hd with hplus | hminus
  · obtain ⟨C, hC, ho, hi⟩ := exists_normOne_torus_prime_index
      (UnitaryFourThree.identityForm J.conj J.conj_involutive) rfl
      hp2 hr2 hrp hplus hF hconj
    exact unitary_not_dvd_kernel_of_normOne_torus_index J hF hconj C hC ho hi f
  · exact PairedTorus.not_dvd_kernel_of_split_prime J hF hconj hr2 hrp hminus f

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
