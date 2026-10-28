module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
/-!
# The point radical's central quotient and natural action

For the actual point-local subgroup L of Sp₄(F), let Q be the kernel of its
middle-block quotient onto SL₂(F). In characteristic two, Z(L) ∩ Q consists
exactly of the elements with radical coordinates (0,0,z). Thus the surjective
two-coordinate homomorphism induces an isomorphism Q/(Z(L) ∩ Q) ≃ F².
Under this isomorphism conjugation by l ∈ L is multiplication by its actual
SL₂ quotient matrix, with the original embeddings retained throughout.

The fixed first column and opposite row prove that the z-coordinate is central.
Two elementary Levi matrices force the other coordinates of a central radical
element to vanish. For arbitrary conjugation, normality gives q′ = l q l⁻¹ in Q;
comparison of the middle entries of l q = q′ l gives the natural action.
No finiteness or field-size hypothesis is needed.

Source: the point-local calculation supporting Aschbacher–Smith,
F.1.12(I)(2), refs/quasithin.pdf, printed pp.262–264. The remaining block
conditions and the complete amalgam statement belong to their assembly modules.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]
open scoped CharTwo

/-- Every pure z-coordinate element centralizes the whole point-local group. -/
theorem pointRadicalElement_central (z : F) :
    pointRadicalElement 0 0 z ∈ Subgroup.center (pointLocal (F := F)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change (g.val.val * pointRadicalMatrix 0 0 z) i j =
    (pointRadicalMatrix 0 0 z * g.val.val) i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, add_comm]

/-- A radical element is central precisely when its two vector coordinates vanish. -/
theorem pointRadicalElement_mem_center_iff (u v z : F) :
    pointRadicalElement u v z ∈ Subgroup.center (pointLocal (F := F)) ↔
      u = 0 ∧ v = 0 := by
  constructor
  · intro hc
    have h (A : Matrix.SpecialLinearGroup (Fin 2) F) :
        pointRadicalElement (A 0 0 * u + A 0 1 * v) (A 1 0 * u + A 1 1 * v) z =
          pointRadicalElement u v z := by
      rw [← pointLevi_conj_radical, Subgroup.mem_center_iff.mp hc (pointLevi A)]
      simp [mul_assoc]
    let U : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp⟩
    let V : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp⟩
    have hv := ((pointRadicalElement_eq_iff ..).mp (h U)).1
    have hu := ((pointRadicalElement_eq_iff ..).mp (h V)).2.1
    simpa [U, V] using And.intro hu hv
  · rintro ⟨rfl, rfl⟩
    exact pointRadicalElement_central z

/-- The central elements of the actual radical are exactly the pure z-coordinates. -/
theorem pointRadical_mem_center_iff (q : pointRadical (F := F)) :
    q.val ∈ Subgroup.center (pointLocal (F := F)) ↔
      ∃ z : F, q.val = pointRadicalElement 0 0 z := by
  constructor
  · intro h
    have he := pointRadical_eq_element q.val q.property
    rw [he, pointRadicalElement_mem_center_iff] at h
    exact ⟨_, by simpa [h.1, h.2] using he⟩
  · rintro ⟨z, hz⟩
    rw [hz]
    exact pointRadicalElement_central z

/-- The relative center is exactly the kernel of the natural-vector map. -/
theorem pointRadical_center_eq_vector_ker :
    (Subgroup.center (pointLocal (F := F))).subgroupOf pointRadical =
      pointRadicalVector.ker := by
  ext q
  rw [Subgroup.mem_subgroupOf, pointRadical_mem_center_iff, MonoidHom.mem_ker]
  constructor
  · rintro ⟨z, hz⟩
    change Multiplicative.ofAdd ![q.val.val.val (.inl 1) (.inr 0),
      q.val.val.val (.inr 1) (.inr 0)] = 1
    rw [hz]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  · intro h
    have hu := congrArg (fun x : Multiplicative (Fin 2 → F) => x.toAdd 0) h
    have hv := congrArg (fun x : Multiplicative (Fin 2 → F) => x.toAdd 1) h
    change q.val.val.val (.inl 1) (.inr 0) = 0 at hu
    change q.val.val.val (.inr 1) (.inr 0) = 0 at hv
    exact ⟨_, by simpa only [hu, hv] using pointRadical_eq_element q.val q.property⟩

/-- The central quotient of the actual radical is the natural two-space. -/
def pointCentralQuotientEquiv :
    (pointRadical (F := F) ⧸
      (Subgroup.center (pointLocal (F := F))).subgroupOf pointRadical) ≃*
        Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (pointRadical_center_eq_vector_ker (F := F))).trans
    (QuotientGroup.quotientKerEquivOfSurjective (pointRadicalVector (F := F))
      (pointRadicalVector_surjective (F := F)))

@[simp] theorem pointCentralQuotientEquiv_mk (q : pointRadical (F := F)) :
    pointCentralQuotientEquiv (QuotientGroup.mk q) = pointRadicalVector q := rfl

/-- Conjugation retains the original embedding in the point-local group. -/
def pointRadicalConjugate (l : pointLocal (F := F)) (q : pointRadical (F := F)) :
    pointRadical (F := F) :=
  ⟨l * q.val * l⁻¹, pointRadical_normal.conj_mem _ q.property l⟩

omit [CharP F 2] in
@[simp] theorem pointRadicalConjugate_coe
    (l : pointLocal (F := F)) (q : pointRadical (F := F)) :
    (pointRadicalConjugate l q).val = l * q.val * l⁻¹ := rfl

/-- All point-local elements act on radical vectors by their middle SL₂ matrix. -/
theorem pointRadicalVector_conjugate
    (l : pointLocal (F := F)) (q : pointRadical (F := F)) :
    pointRadicalVector (pointRadicalConjugate l q) =
      Multiplicative.ofAdd ((pointQuotient l).val *ᵥ (pointRadicalVector q).toAdd) := by
  let r := pointRadicalConjugate l q
  have hm : l * q.val = r.val * l := by simp [r, pointRadicalConjugate, mul_assoc]
  have h0 := congrArg (fun g : pointLocal (F := F) => g.val.val (.inl 1) (.inr 0)) hm
  have h1 := congrArg (fun g : pointLocal (F := F) => g.val.val (.inr 1) (.inr 0)) hm
  rw [pointRadical_eq_element q.val q.property,
    pointRadical_eq_element r.val r.property] at h0 h1
  change (l.val.val * pointRadicalMatrix (F := F) _ _ _) (.inl 1) (.inr 0) =
    (pointRadicalMatrix (F := F) _ _ _ * l.val.val) (.inl 1) (.inr 0) at h0
  change (l.val.val * pointRadicalMatrix (F := F) _ _ _) (.inr 1) (.inr 0) =
    (pointRadicalMatrix (F := F) _ _ _ * l.val.val) (.inr 1) (.inr 0) at h1
  simp [pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two] at h0 h1
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · change r.val.val.val (.inl 1) (.inr 0) =
      (pointQuotientMatrix l *ᵥ
        ![q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0)]) 0
    simp [pointQuotientMatrix, middleIndex, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.submatrix]
    linear_combination -h0
  · change r.val.val.val (.inr 1) (.inr 0) =
      (pointQuotientMatrix l *ᵥ
        ![q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0)]) 1
    simp [pointQuotientMatrix, middleIndex, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.submatrix]
    linear_combination -h1

/-- Under the central quotient isomorphism, conjugation is the literal natural SL₂ action. -/
theorem pointCentralQuotientEquiv_conjugate
    (l : pointLocal (F := F)) (q : pointRadical (F := F)) :
    pointCentralQuotientEquiv (QuotientGroup.mk (pointRadicalConjugate l q)) =
      Multiplicative.ofAdd ((pointQuotient l).val *ᵥ
        (pointCentralQuotientEquiv (QuotientGroup.mk q)).toAdd) := by
  simpa only [pointCentralQuotientEquiv_mk] using pointRadicalVector_conjugate l q

end Theory.SpecificGroups.SymplecticFour
