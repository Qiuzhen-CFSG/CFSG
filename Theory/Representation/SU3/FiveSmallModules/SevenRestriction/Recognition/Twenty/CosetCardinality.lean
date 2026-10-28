module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.Factors
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# The 126 literal Borel cosets of SU₃(5)

Huppert's projective point stabilizer is identified with the literal upper
root-and-full-torus join by its matrix coordinates. Its order is 1000 in the
projective group of order 126000. The special-to-projective map carries the
special Borel onto this subgroup, and its scalar kernel lies in the full
special torus, so the two Borel indices agree.

Specializing to the canonical antidiagonal form over GF(25) retains its
fifth-power conjugation. The final application discharges the coset-count
premise of the degree-twenty factor selection; the independently constructed
middle flag remains an explicit input.

Source: Huppert, *Endliche Gruppen I*, II.10.12, pp.264–265; the principal-series
application is used in the approach to Guralnick–Malle, *Classification of
2F-modules I*, Proposition 4.3, and Aschbacher–Smith K.2, printed p.453.
-/

open Matrix BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open Subgroup

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty

private theorem scalar_kernel_le_borel {E : Type*} [Field E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.specialToProjective.ker ≤ specialBorel J hJ := by
  intro x hx
  have hz : x.val ∈ center (GL (Fin 3) E) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, hc⟩ := hz
  obtain ⟨hu, hd⟩ := (J.mem_specialSubgroup_iff _).mp x.property
  rw [← hc, hJ] at hu
  have hn := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 0) hu
  simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Fin.sum_univ_three] at hn
  have hj : J.conj (c : E) = (c : E)⁻¹ := eq_inv_of_mul_eq_one_left hn
  rw [← hc, GeneralLinearGroup.det_scalar] at hd
  have hcube : (c : E) ^ 3 = 1 := by simpa using congrArg Units.val hd
  have hmid : (c : E)⁻¹ * (c : E)⁻¹ = (c : E) := by
    field_simp
    linear_combination -hcube
  apply (show specialTorus J hJ ≤ specialBorel J hJ from le_sup_right)
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change hermitianTorusGL J c = x.val
  rw [← hc]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, GeneralLinearGroup.coe_scalar, hj, hmid]

private theorem borel_projective_image {E : Type*} [Field E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (specialBorel J hJ).map J.specialToProjective = projectiveBorel J hJ := by
  rw [specialBorel, projectiveBorel, Subgroup.map_sup]
  congr 1
  · rw [specialRoot, projectiveRoot, ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro z
    apply Subtype.ext
    exact J.specialToProjective_apply_val _
  · rw [specialTorus, projectiveTorus, ← MonoidHom.range_comp]
    congr 1
    apply MonoidHom.ext
    intro k
    apply Subtype.ext
    exact J.specialToProjective_apply_val _

private theorem projective_borel_index_five {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hcard : Nat.card E = 5 ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 5) :
    (projectiveBorel J hJ).index = 126 := by
  obtain ⟨_, rho, pinf, _, _, hUcard, hstructure, _, hGcard, _⟩ :=
    huppert_II_10_12 J 5 hcard hfixed hJ
  obtain ⟨R, H, _, _, _, _, hsup, _, _, _, _, _, _,
    ⟨coord, hcoord⟩, hHcoord, hHcover⟩ := hstructure
  have hcoord_eq (z : hermitianUnipotentCoord J) :
      (coord z).val = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, heq⟩ := hcoord z
    have hM' : M = hermitianUnipotentGL J z := Units.ext hM
    apply Subtype.ext
    simpa only [hM', hermitianUnipotentPSU_val] using heq
  have hR : R = projectiveRoot J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨z, hz⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨z, (hcoord_eq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro r ⟨z, rfl⟩
      rw [← hcoord_eq z]
      exact (coord z).property
  have hH : H = projectiveTorus J hJ := by
    apply le_antisymm
    · intro h hh
      obtain ⟨k, M, hM, heq⟩ := hHcoord ⟨h, hh⟩
      have hM' : M = hermitianTorusGL J k := Units.ext hM
      refine ⟨k, Subtype.ext ?_⟩
      simpa only [hM', hermitianTorusPSU_val] using heq.symm
    · rintro h ⟨k, rfl⟩
      obtain ⟨h, M, hM, heq⟩ := hHcover k
      have hM' : M = hermitianTorusGL J k := Units.ext hM
      have he : h.val = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        simpa only [hM', hermitianTorusPSU_val] using heq
      rw [← he]
      exact h.property
  rw [hR, hH] at hsup
  change projectiveBorel J hJ = _ at hsup
  rw [← hsup] at hUcard
  have hmul := (projectiveBorel J hJ).card_mul_index
  norm_num only at hUcard hGcard
  rw [hUcard, hGcard] at hmul
  omega

open Degrees.TrivialCalculation
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The canonical left-coset space for the actual upper Borel has 126 elements. -/
public theorem canonical_borel_coset_card : Nat.card CanonicalPoints = 126 := by
  let J := FormTransport.standardForm canonicalInputForm
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hc : Nat.card (GaloisField 5 (2 * 1)) = 5 ^ 2 :=
    GaloisField.card 5 (2 * 1) (by decide)
  have hj (x : GaloisField 5 (2 * 1)) : J.conj x = x ^ 5 := by
    simp only [J, FormTransport.standardForm, canonicalInputForm, ABG.unitaryForm,
      iterateFrobeniusEquiv_def, pow_one]
  have hf : Nat.card {x : GaloisField 5 (2 * 1) // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hc)
      (by simpa only [pow_one] using hj)
  change (specialBorel J hJ).index = 126
  rw [← (specialBorel J hJ).index_map_eq J.specialToProjective_surjective
    (scalar_kernel_le_borel J hJ), borel_projective_image J hJ]
  exact projective_borel_index_five J hJ hc hf

universe v
/-- The canonical middle flag now selects an actual degree-twenty quotient
without an additional coset-cardinality assumption. -/
public theorem trivial_twenty_factor_of_canonical_middle_flags
    (hm : CanonicalMiddleFlags.{v})
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (K : Type v) [Field K] [Finite K] [CharP K 2] :
    ∃ (S : Subrepresentation (ind (standardBorel J).subtype
        (scalarCharacter (1 : standardBorel J →* Kˣ))))
      (T : Subrepresentation S.toRepresentation),
      T.quotientRepresentation.IsIrreducible ∧
        Module.finrank K (S.toSubmodule ⧸ T.toSubmodule) = 20 :=
  trivial_twenty_factor_of_middle_flags canonical_borel_coset_card hm J hc hconj K

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
