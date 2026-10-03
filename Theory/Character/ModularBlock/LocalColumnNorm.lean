module

public import Theory.Character.ModularBlock.BlockConjugationTrace
public import Theory.Character.ModularBlock.PrincipalBrauerEquality
public import Theory.Character.ModularBlock.CompatibleSelectorComplex
public import Theory.Character.ModularBlock.BrauerConjugationTrace

/-!
# Principal two-block local column norms

For a two-element `y`, the Brauer restriction of the ambient principal
selector is the compatible principal selector of `C_G(y)`. The coefficient
statement below transports the subgroup theorem along
`C_G(⟨y⟩) = C_G(y)` and compares the actual integral lifts after reduction.

The integral permutation-summand trace theorem then identifies the ambient
block's conjugation trace at `y` with the local block's regular projection
trace. The ordinary character formulas for these traces give local column
orthogonality: the ambient column norm equals the local sum of squared
degrees.

Source application: Fong, *Some Sylow subgroups of order 32 and a
characterization of U(3,3)*, J. Algebra 6 (1967), p. 71, equation (6),
citing Brauer--Suzuki, Section I.
-/

public section
noncomputable section

namespace ModularBlock.LocalColumnNorm

open scoped BigOperators
open PrincipalBlockConstruction CompatibleBrauerBlock BrauerBlockReduction

variable {G : Type*} [Group G] [Finite G]

/-- Principal Brauer equality at any element of two-power order, expressed
coefficientwise in its actual element centralizer. -/
theorem localPrincipalBlock_residue_coeff
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (x : Subgroup.centralizer ({y} : Set G)) :
    (localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer ({y} : Set G))).coeff x =
        (reducedPrincipalBlockElement d).coeff (x : G) := by
  obtain ⟨n, hn⟩ := hy
  have hQ : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hn)
  have hcentralizer : Subgroup.centralizer (Subgroup.zpowers y : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcoeff (z : Subgroup.centralizer (Subgroup.zpowers y : Set G)) :
      (localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Subgroup.zpowers y : Set G))).coeff z =
          (reducedPrincipalBlockElement d).coeff (z : G) := by
    rw [← PrincipalBrauer.subgroupPrincipalBrauerEquality d (Subgroup.zpowers y) hQ]
    rfl
  rw [hcentralizer] at hcoeff
  exact hcoeff x

/-- The two integral idempotents have the required equal reduced
coefficients on `C_G(y)`. This is an exact consequence of principal block
theory, without a column-orthogonality hypothesis. -/
theorem localPrincipalBlock_localization_coeff_reduce
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (x : Subgroup.centralizer ({y} : Set G)) :
    localizationToResidue d
        ((localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({y} : Set G))).coeff x) =
      localizationToResidue d
        ((BlockOrthogonality.localizedPrincipalBlockElement d).coeff (x : G)) := by
  have h := congrArg (fun a => a.coeff x)
    (localPrincipalBlockElementInAmbientLocalization_reduce d
      (Subgroup.centralizer ({y} : Set G)))
  rw [MonoidAlgebra.coeff_mapRingHom] at h
  exact h.trans (localPrincipalBlock_residue_coeff d y hy x)

/-- Principal two-block local column orthogonality. The compatible principal
block of the element centralizer accounts for the entire column norm at a
two-element, with no additional subsection or decomposition hypotheses. -/
theorem principalBlock_local_column_norm
    (d : PrincipalCongruenceBlockData G) (y : G)
    (hy : ∃ n : ℕ, y ^ (2 ^ n) = 1) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk y) *
        star (d.chi i (ConjClasses.mk y)) =
      ∑ j ∈ (localData d (Subgroup.centralizer ({y} : Set G))).block,
        (localData d (Subgroup.centralizer ({y} : Set G))).chi j
          (ConjClasses.mk 1) ^ 2 := by
  have h := BrauerConjugationTrace.conjugation_trace_eq d y hy
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({y} : Set G)))
    (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d)
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)
    (localPrincipalBlockElementInAmbientLocalization_isIdempotent d _)
    (localPrincipalBlock_localization_coeff_reduce d y hy)
  rw [BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      d (IsotypicLattice.localizationToComplex d)
      (IsotypicLattice.localizationToComplex_algebraMap d),
    CharacterwiseProjection.map_localPrincipalBlockElementInAmbientLocalization,
    BlockConjugationTrace.principalBlock_conjugation_trace,
    BlockConjugationTrace.principalBlock_projection_trace] at h
  exact h

end ModularBlock.LocalColumnNorm
