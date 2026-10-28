module

public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Displacement over an arbitrary finite binary field

A nonscalar SL₂ matrix moves a projective line. Restricting the left-right
matrix displacement to the corresponding row space gives an injection, hence
binary rank at least twice the field degree. Transposition handles the second
factor. In characteristic two a scalar SL₂ matrix is the identity.

This extends the GF(4) argument in `OrthogonalFourPlusMatrix.Displacement`.
It uses the literal determinant action, with no involution or model tags.
Source application: Aschbacher–Smith, G.9.3(15) and 15.3.58, printed pp.354,1149.
-/

@[expose] public section
namespace ClassicalOrthogonal.FourPlusMatrix.FieldDisplacement
open Matrix Module ClassicalOrthogonal.FourPlusMatrix

section Field
variable {K : Type*} [Field K] [CharP K 2]

private def wedge (v w : Fin 2 → K) : K := v 0 * w 1 - v 1 * w 0

private lemma exists_moved_line (A : Matrix.SpecialLinearGroup (Fin 2) K) (hA : A ≠ 1) :
    ∃ v : Fin 2 → K, wedge v (A.val *ᵥ v) ≠ 0 := by
  by_contra! hh
  have h10 : A 1 0 = 0 := by
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two] using hh ![1, 0]
  have h01 : A 0 1 = 0 := by
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two] using hh ![0, 1]
  have he : A 1 1 = A 0 0 := by
    have h := hh ![1, 1]
    simpa [wedge, mulVec, dotProduct, Fin.sum_univ_two, h10, h01, sub_eq_zero] using h
  have hsq : A 0 0 ^ 2 = 1 := by
    simpa only [det_fin_two, h10, h01, he, mul_zero, sub_zero, pow_two] using A.property
  have ha : A 0 0 = 1 := CharTwo.sq_injective (by simpa using hsq)
  apply hA
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, he, ha]

private def outer (v : Fin 2 → K) : (Fin 2 → K) →ₗ[K] Mat (F := K) where
  toFun w := vecMulVec v w
  map_add' _ _ := vecMulVec_add _ _ _
  map_smul' c w := vecMulVec_smul c v w

omit [CharP K 2] in
private lemma outer_intertwiner_zero (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (B : Mat (F := K)) (v : Fin 2 → K) (hv : wedge v (A.val *ᵥ v) ≠ 0)
    (w : Fin 2 → K) (hw : A.val * outer v w = outer v w * B) : w = 0 := by
  change A.val * vecMulVec v w = vecMulVec v w * B at hw
  rw [mul_vecMulVec, vecMulVec_mul] at hw
  funext j
  have h0 := congrArg (fun M : Mat (F := K) => M 0 j) hw
  have h1 := congrArg (fun M : Mat (F := K) => M 1 j) hw
  change (A.val *ᵥ v) 0 * w j = v 0 * (w ᵥ* B) j at h0
  change (A.val *ᵥ v) 1 * w j = v 1 * (w ᵥ* B) j at h1
  have hz : wedge v (A.val *ᵥ v) * w j = 0 := by
    unfold wedge
    linear_combination v 0 * h1 - v 1 * h0
  exact (mul_eq_zero.mp hz).resolve_left hv

end Field

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]

local notation "G" => PairSL (F := F)
local notation "V" => Mat (F := F)
local notation "action" => Representation.restrictScalars (k := ZMod 2)
  (representation (F := F))

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
private theorem action_apply (g : G) (M : V) :
    action g M = g.1.val * M * g.2⁻¹.val := rfl

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
/-- The fixed-matrix equation has no inverse after multiplication on the right. -/
private theorem fixed_iff_intertwines (g : G) (M : V) :
    action g M = M ↔ g.1.val * M = M * g.2.val := by
  rw [action_apply]
  constructor
  · intro hh
    have ht := congrArg (fun X : V => X * g.2.val) hh
    simpa only [mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one] using ht
  · intro hh
    rw [hh, mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, mul_one]

/-- A nonidentity first factor displaces a full row space injectively. -/
private theorem displacement_rank_left (g : G) (hg : g.1 ≠ 1) :
    2 * finrank (ZMod 2) F ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  obtain ⟨v, hv⟩ := exists_moved_line g.1 hg
  let f := (action g - LinearMap.id).comp ((outer v).restrictScalars (ZMod 2))
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    change action g (outer v w) - outer v w = 0 at hw
    exact outer_intertwiner_zero g.1 g.2.val v hv w
      ((fixed_iff_intertwines g _).mp (sub_eq_zero.mp hw))
  have hr := Submodule.finrank_mono
    (LinearMap.range_comp_le_range ((outer v).restrictScalars (ZMod 2))
      (action g - LinearMap.id))
  have he := LinearMap.finrank_range_of_inj hf
  rw [Module.finrank_pi_fintype] at he
  simp only [Fin.sum_univ_two, ← two_mul] at he
  exact he.symm.trans_le hr

/-- The transposed argument applies to a nonidentity second factor. -/
private theorem displacement_rank_right (g : G) (hg : g.2 ≠ 1) :
    2 * finrank (ZMod 2) F ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  have hgT : g.2.transpose ≠ 1 := by
    intro hh
    apply hg
    apply Subtype.ext
    have ht := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A.val.transpose) hh
    simpa using ht
  obtain ⟨v, hv⟩ := exists_moved_line g.2.transpose hgT
  let outerT := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) F F).toLinearMap.comp (outer v)
  let f := (action g - LinearMap.id).comp (outerT.restrictScalars (ZMod 2))
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    change action g (outer v w).transpose - (outer v w).transpose = 0 at hw
    have hh := (fixed_iff_intertwines g _).mp (sub_eq_zero.mp hw)
    have ht := congrArg Matrix.transpose hh
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
    exact outer_intertwiner_zero g.2.transpose g.1.val.transpose v hv w ht.symm
  have hr := Submodule.finrank_mono
    (LinearMap.range_comp_le_range (outerT.restrictScalars (ZMod 2))
      (action g - LinearMap.id))
  have he := LinearMap.finrank_range_of_inj hf
  rw [Module.finrank_pi_fintype] at he
  simp only [Fin.sum_univ_two, ← two_mul] at he
  exact he.symm.trans_le hr

/-- Every nonidentity element of the determinant action has displacement rank
at least twice the binary field degree; no involution hypothesis is needed. -/
theorem binary_displacement_rank (g : G) (hg : g ≠ 1) :
    2 * finrank (ZMod 2) F ≤ finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) := by
  by_cases h1 : g.1 = 1
  · apply displacement_rank_right g
    intro h2
    exact hg (Prod.ext h1 h2)
  · exact displacement_rank_left g h1

/-- The bound on the actual elementary orthogonal carrier, transported through
the proved determinant-coordinate comparison, after restriction to F₂. -/
theorem elementary_binary_displacement_rank (g : OmegaPlus 2 F) (hg : g ≠ 1) :
    2 * finrank (ZMod 2) F ≤ finrank (ZMod 2)
      (LinearMap.range ((Representation.restrictScalars (k := ZMod 2)
        (subgroupNatural (OmegaPlus 2 F))) g - LinearMap.id)) := by
  let σ := Representation.restrictScalars (k := ZMod 2)
    (subgroupNatural (OmegaPlus 2 F))
  let τ := Representation.restrictScalars (k := ZMod 2) (representation (F := F))
  let e := elementaryEquiv (F := F)
  let E := (coordinates (F := F)).restrictScalars (ZMod 2)
  have hE : ∀ a v, E (σ a v) = τ (e.symm a) (E v) := by
    intro a v
    obtain ⟨b, rfl⟩ := e.surjective a
    rw [e.symm_apply_apply]
    exact toOrthogonal_coordinates b v
  have hr := Representation.BinaryOffender.fixedCodim_map_equivariant σ τ
    e.symm.toMonoidHom E hE (Subgroup.zpowers g)
  rw [MonoidHom.map_zpowers,
    Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank,
    Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hr
  change 2 * finrank (ZMod 2) F ≤ finrank (ZMod 2) (LinearMap.range (σ g - LinearMap.id))
  rw [hr]
  apply binary_displacement_rank
  exact fun he => hg (e.symm.injective (he.trans (map_one e.symm).symm))

end ClassicalOrthogonal.FourPlusMatrix.FieldDisplacement
