module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Cosets.Checks

/-!
# The fixed SU₃(5) coset enumeration

Invert the 126 displayed right representatives to obtain left cosets of the
literal upper-root-and-full-torus Borel. The checked root–torus multipliers
identify the published permutations with inverse-actor multiplication.
For distinctness, the literal Borel lies in the upper triangular subgroup;
its bottom row therefore acts by a nonzero scalar. Normalized bottom rows
recover the representative indices by the checked recovery table.
Finally, `CosetEnumeration.ofTable` transports the marked group/Borel pair
to the canonical field, including the basepoint and action convention.
No group order, coset count, or generation hypothesis is used here.

Source: `MiddleFactors/source/standard_flag_data.txt`, lines 133–276.
Source motivation: Guralnick–Malle Proposition 4.3, p.10;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
namespace CosetCertificate

abbrev mat (g : TableGroup) : Matrix (Fin 3) (Fin 3) F25 := g.val.val

def upper : Subgroup TableGroup where
  carrier := {g | (mat g).IsUpperTriangular}
  one_mem' := by intro i j hij; exact Matrix.one_apply_ne (ne_of_gt hij)
  mul_mem' := fun hg hh => hg.mul hh
  inv_mem' := by
    intro g hg
    change (g.val⁻¹).val.IsUpperTriangular
    simpa only [GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hg

theorem borel_upper : tableBorel ≤ upper := by
  apply sup_le
  · rintro _ ⟨z, rfl⟩
    change (hermitianUnipotentMatrix form z).IsUpperTriangular
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hermitianUnipotentMatrix]
  · rintro _ ⟨k, rfl⟩
    change (hermitianTorusMatrix form k).IsUpperTriangular
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hermitianTorusMatrix]

theorem rowKey_scale (c : F25) (hc : c ≠ 0) (v : Fin 3 → F25) :
    rowKey (fun j => c * v j) = rowKey v := by
  simp [rowKey, mul_eq_zero, hc, mul_div_mul_left _ _ hc]

theorem bottom_mul (g : TableGroup) (hg : g ∈ upper)
    (m : Matrix (Fin 3) (Fin 3) F25) (j : Fin 3) :
    (mat g * m) 2 j = mat g 2 2 * m 2 j := by
  have h20 : mat g 2 0 = 0 := hg (by decide)
  have h21 : mat g 2 1 = 0 := hg (by decide)
  simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

theorem bottom_diagonal_ne_zero (g : TableGroup) (hg : g ∈ upper) : mat g 2 2 ≠ 0 := by
  have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) F25 => m 2 2) g.val.mul_inv
  rw [bottom_mul g hg] at h
  intro hz
  simp [hz] at h

theorem rowKey_borel_mul (g h : TableGroup) (hg : g ∈ tableBorel) :
    rowKey (mat (g * h) 2) = rowKey (mat h 2) := by
  have hrow : mat (g * h) 2 = fun j => mat g 2 2 * mat h 2 j := by
    funext j
    exact bottom_mul g (borel_upper hg) (mat h) j
  rw [hrow, rowKey_scale _ (bottom_diagonal_ne_zero g (borel_upper hg))]

/-- The displayed right representative, as an element of the actual table group. -/
def representativeLinear (i : Fin 126) : GL (Fin 3) F25 :=
  GeneralLinearGroup.mkOfDetNeZero (representativeMatrix i)
    (by rw [(representative_valid i).1]; exact one_ne_zero)

theorem representative_mem (i : Fin 126) :
    representativeLinear i ∈ form.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · exact (representative_valid i).2
  · apply Units.ext
    exact (representative_valid i).1

def representative (i : Fin 126) : TableGroup :=
  ⟨representativeLinear i, representative_mem i⟩

def borelMultiplier (j : Fin 2) (i : Fin 126) : TableGroup :=
  hermitianUnipotentSU form rfl (transitionRoot j i) *
    hermitianTorusSU form rfl (transitionTorus j i)

theorem borelMultiplier_mem (j : Fin 2) (i : Fin 126) :
    borelMultiplier j i ∈ tableBorel := by
  apply Subgroup.mul_mem_sup
  · exact ⟨transitionRoot j i, rfl⟩
  · exact ⟨transitionTorus j i, rfl⟩

theorem representative_transition (j : Fin 2) (i : Fin 126) :
    representative i * tableActor j = borelMultiplier j i * representative (image j i) := by
  apply Subtype.ext
  apply Units.ext
  exact transition_matrix j i

/-- Invert the source's right representatives to obtain literal left cosets. -/
def point (i : Fin 126) : TableGroup ⧸ tableBorel :=
  QuotientGroup.mk (representative i)⁻¹

theorem point_injective : Function.Injective point := by
  intro i j h
  have hb : representative i * (representative j)⁻¹ ∈ tableBorel := by
    have hh := QuotientGroup.eq.mp h
    simpa only [inv_inv] using hh
  apply rowKey_injective
  change rowKey (mat (representative i) 2) = rowKey (mat (representative j) 2)
  have hh := rowKey_borel_mul (representative i * (representative j)⁻¹) (representative j) hb
  simpa only [inv_mul_cancel_right] using hh

theorem point_action (j : Fin 2) (i : Fin 126) :
    point (image j i) = (tableActor j)⁻¹ • point i := by
  rw [point, point, MulAction.Quotient.smul_mk]
  apply QuotientGroup.eq.mpr
  change (representative (image j i))⁻¹⁻¹ *
    ((tableActor j)⁻¹ * (representative i)⁻¹) ∈ tableBorel
  rw [inv_inv, ← _root_.mul_inv_rev, representative_transition]
  simpa only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
    tableBorel.inv_mem (borelMultiplier_mem j i)

theorem point_base : point 0 = QuotientGroup.mk 1 := by
  have h : representative 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    change representativeMatrix 0 = 1
    decide +kernel
  simp only [point, h, inv_one]

end CosetCertificate

/-- The fixed point and permutation tables realize distinct canonical Borel
cosets, with the prescribed inverse-actor action and identity basepoint. -/
theorem coset_enumeration : Nonempty CosetEnumeration :=
  ⟨CosetEnumeration.ofTable CosetCertificate.point CosetCertificate.point_injective
    CosetCertificate.point_action CosetCertificate.point_base⟩

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
