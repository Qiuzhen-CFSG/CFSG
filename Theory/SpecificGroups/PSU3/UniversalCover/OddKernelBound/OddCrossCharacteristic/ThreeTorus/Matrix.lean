module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix.Index
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix.Swap
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.FixedPoints
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
/-!
# The odd three-primary projective unitary configuration

The parameter group is the Sylow three-subgroup of the norm-one field units.
Its two diagonal generators commute and are exchanged by the determinant-one
negative coordinate transposition. Their odd exponent is the full parameter
order. Adjoining the coordinate cycle has order m² and index prime to three.
These constructions allow arbitrarily large three-valuations of q+1.

The coordinate cycle's fixed subgroup in the full projective norm-one torus
has order at most three, by the cubic-coordinate calculation in `FixedPoints`.
Restriction gives the bound for our three-primary torus. An actual orthonormal
basis carries the resulting configuration to the input Hermitian form. Thus
`nonempty_threeTorus` constructs every required witness whenever q ≡ 2 mod 3,
and `not_nine_dvd_kernel` applies the central-cover argument to the literal
projective matrix group, with no additional torus or fixed-subgroup premise.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), PDF pp.418–419;
GLS III, Theorem 6.1.4 and Tables 6.1.2–3; Huppert II.10.4 for basis change.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups PerfectCentralCovering
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
@[expose] public noncomputable section
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
variable {E : Type*} [Field E] [Finite E] {K : HermitianForm 3 E}

/-- Carry all marked elements and both subgroup conditions through an actual
multiplicative equivalence of projective matrix groups. -/
def transport (e : ProjectiveSpecialUnitaryMatrixGroup J ≃*
    ProjectiveSpecialUnitaryMatrixGroup K) (D : ThreeTorus J) :
    ThreeTorus K where
  torus := D.torus.map e.toMonoidHom
  first := e D.first
  second := e D.second
  cycle := e D.cycle
  swapper := e D.swapper
  generate := by
    have hg := congrArg (fun H : Subgroup _ => H.map e.toMonoidHom) D.generate
    simpa only [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, Set.image_pair] using hg
  commute := D.commute.map e.toMonoidHom
  swap_first := by rw [← map_inv, ← map_mul, ← map_mul, D.swap_first]
  swap_second := by rw [← map_inv, ← map_mul, ← map_mul, D.swap_second]
  exponent := D.exponent
  coprime_two := D.coprime_two
  first_pow := by rw [← map_pow, D.first_pow, map_one]
  normalizes := by
    rw [mem_normalizer_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [← map_mul, ← map_inv, mem_map_equiv, e.symm_apply_apply] using
      (mem_normalizer_iff.mp D.normalizes x)
  index_prime_to_three := by
    have hz := e.toMonoidHom.map_zpowers D.cycle
    simp only [MulEquiv.coe_toMonoidHom] at hz
    rw [← hz, ← Subgroup.map_sup, Subgroup.index_map_of_bijective e.bijective]
    exact D.index_prime_to_three
  fixed_card_le := by
    have he : (D.torus ⊓ centralizer ({D.cycle} : Set _)).map e.toMonoidHom =
        D.torus.map e.toMonoidHom ⊓ centralizer ({e D.cycle} : Set _) := by
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      simp only [mem_map_equiv, e.symm_apply_apply, mem_inf, mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, e.injective.eq_iff]
    rw [← he, ← Nat.card_congr
      ((D.torus ⊓ centralizer ({D.cycle} : Set _)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv]
    exact D.fixed_card_le


/-- Construct every marked matrix and the odd exponent; the two local counts
remain explicit in this intermediate constructor. -/
def configurationOfCounts (hJ : J.form = 1)
    (hindex : ¬ 3 ∣ (primaryTorus J hJ ⊔ zpowers (cycle J hJ)).index)
    (hfixed : Nat.card (primaryTorus J hJ ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3) : ThreeTorus J := by
  let g : primary J := Classical.choose (IsCyclic.exists_generator (α := primary J))
  have hg : ∀ a : primary J, ∃ k : ℤ, g ^ k = a :=
    Classical.choose_spec (IsCyclic.exists_generator (α := primary J))
  exact {
    torus := primaryTorus J hJ
    first := first J hJ _ (primary_norm J) g
    second := second J hJ _ (primary_norm J) g
    cycle := cycle J hJ
    swapper := negativeSwap J hJ
    generate := generate J hJ _ (primary_norm J) g hg
    commute := first_commute_second J hJ _ (primary_norm J) g
    swap_first := negativeSwap_first J hJ _ (primary_norm J) g
    swap_second := negativeSwap_second J hJ _ (primary_norm J) g
    exponent := Nat.card (primary J)
    coprime_two := primary_coprime_two J
    first_pow := first_pow J hJ _ (primary_norm J) g pow_card_eq_one'
    normalizes := cycle_normalizes J hJ _ (primary_norm J)
    index_prime_to_three := hindex
    fixed_card_le := hfixed }

/-- Restricting the full norm-one torus's fixed-point bound to the primary
parameters gives the fixed-point field of the configuration. -/
def configurationOfFixed (hJ : J.form = 1) {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2)
    (hfixed : Nat.card (normOneTorus J hJ ⊓ centralizer ({cycle J hJ} : Set _) :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ 3) : ThreeTorus J :=
  configurationOfCounts J hJ (primary_join_index J hJ hcard hc hq)
    ((Subgroup.card_le_of_le (inf_le_inf_right _ (primaryTorus_le_normOneTorus J hJ))).trans hfixed)

/-- Identity Gram model with the original field involution. -/
def identityModel : HermitianForm 3 F :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.identityForm J.conj J.conj_involutive

/-- Transport the constructed configuration through an actual orthonormal
basis, with the projective fixed-subgroup bound supplied explicitly. -/
theorem nonempty_of_identity_fixed {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2)
    (hfixed : Nat.card (normOneTorus (identityModel J) rfl ⊓
      centralizer ({cycle (identityModel J) rfl} : Set _) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityModel J))) ≤ 3) :
    Nonempty (ThreeTorus J) := by
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    3 J q hcard (card_fixed J hcard hc)
  let e := (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.projectiveBasisEquiv J P hP).symm
  exact ⟨transport (identityModel J) e
    (configurationOfFixed (identityModel J) rfl hcard hc hq hfixed)⟩

/-- Literal application to the original perfect-cover kernel. This remains
conditional on the fixed-subgroup count, with no covering conclusion assumed. -/
theorem not_nine_dvd_kernel_of_identity_fixed {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2)
    (hfixed : Nat.card (normOneTorus (identityModel J) rfl ⊓
      centralizer ({cycle (identityModel J) rfl} : Set _) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup (identityModel J))) ≤ 3)
    {X : Type*} [Group X] [Finite X]
    (f : Cover X (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨t⟩ := nonempty_of_identity_fixed J hcard hc hq hfixed
  exact not_nine_dvd_kernel_of_three_torus J t f

/-- The three-primary matrix configuration for every quadratic field parameter
congruent to two modulo three. In particular this discharges the odd-prime,
`9 ∣ p + 1` witness premise of `not_nine_dvd_kernel_of_torus_witness`.
No bound on the three-valuation of the parameter order is needed. -/
theorem nonempty_threeTorus {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2) :
    Nonempty (ThreeTorus J) :=
  nonempty_of_identity_fixed J hcard hc hq
    (normOneTorus_fixed_card_le (identityModel J) rfl)

/-- Every finite perfect central cover of the literal PSU₃ has kernel order
not divisible by nine when q ≡ 2 mod 3, including arbitrarily large
three-valuations of q + 1. All matrix-configuration premises are discharged. -/
theorem not_nine_dvd_kernel {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hc : ∀ x, J.conj x = x ^ q) (hq : q % 3 = 2)
    {X : Type*} [Group X] [Finite X]
    (f : Cover X (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨t⟩ := nonempty_threeTorus J hcard hc hq
  exact not_nine_dvd_kernel_of_three_torus J t f

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.OddThreeMatrix
