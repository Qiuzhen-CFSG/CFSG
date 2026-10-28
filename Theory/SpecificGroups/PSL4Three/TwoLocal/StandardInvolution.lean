module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A split involution and its full projective centralizer in PSL₄(3)

The center of SL₄(3) consists of the two scalar matrices ±1. Consequently,
two matrix lifts have the same projective image exactly when they differ
by sign. Commutation in PSL₄(3) therefore allows both commuting and
anticommuting lifts. In particular the centralizer of the image of
diag(-1,-1,1,1) includes the matrix interchanging the two eigenspaces.

These concrete definitions supply the common interface for a calculation
of this centralizer's intrinsic two-core and a classification of involutions
in Sylow centers. Neither of those remaining calculations is asserted here.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

namespace Matrix.PSL4Three.TwoLocal

/-- The actual determinant-one matrix group. -/
public abbrev SL := SpecialLinearGroup (Fin 4) (ZMod 3)

/-- Its quotient by its center, rather than a separately chosen finite model. -/
public abbrev PSL := ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

local instance : Fact (Even (Fintype.card (Fin 4))) := ⟨by decide⟩

/-- The defining central quotient map. -/
@[expose] public def project : SL →* PSL := QuotientGroup.mk' _

public theorem project_surjective : Function.Surjective project :=
  QuotientGroup.mk'_surjective _

private theorem mem_center_SL_iff (g : SL) :
    g ∈ Subgroup.center SL ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    obtain ⟨a, ha, hag⟩ := SpecialLinearGroup.mem_center_iff.mp hg
    have hroot : ∀ a : ZMod 3, a ^ 4 = 1 → a = 1 ∨ a = -1 := by decide
    rcases hroot a (by simpa using ha) with rfl | rfl
    · left
      exact Subtype.ext (by simpa using hag.symm)
    · right
      exact Subtype.ext (by simpa [← Matrix.diagonal_neg, Matrix.diagonal_one] using hag.symm)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · apply SpecialLinearGroup.mem_center_iff.mpr
      exact ⟨-1, by decide, by simp [← Matrix.diagonal_neg, Matrix.diagonal_one]⟩

private theorem project_eq_SL_iff (g h : SL) :
    project g = project h ↔ g = h ∨ g = -h := by
  change (g : SL ⧸ Subgroup.center SL) = h ↔ _
  rw [QuotientGroup.eq_iff_div_mem, mem_center_SL_iff]
  constructor
  · rintro (he | he)
    · exact Or.inl (div_eq_one.mp he)
    · right
      have hh := congrArg (fun x : SL => x * h) he
      simp only [div_mul_cancel, neg_one_mul] at hh
      exact hh
  · rintro (he | he)
    · left
      rw [he]
      exact mul_inv_cancel h
    · right
      rw [he]
      change (-h) * h⁻¹ = -1
      rw [neg_mul, mul_inv_cancel]

/-- The only central matrices are the two scalar matrices ±1. -/
public theorem mem_center_iff (g : SL) :
    g ∈ Subgroup.center SL ↔ g.val = 1 ∨ g.val = -1 := by
  rw [mem_center_SL_iff]
  constructor
  · rintro (he | he)
    · exact Or.inl (congrArg (fun a : SL => a.val) he)
    · exact Or.inr (congrArg (fun a : SL => a.val) he)
  · rintro (he | he)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)

/-- Equality of projective images retains the negative scalar possibility. -/
public theorem project_eq_iff (g h : SL) :
    project g = project h ↔ g.val = h.val ∨ g.val = -h.val := by
  rw [project_eq_SL_iff]
  constructor
  · rintro (he | he)
    · exact Or.inl (congrArg (fun a : SL => a.val) he)
    · exact Or.inr (congrArg (fun a : SL => a.val) he)
  · rintro (he | he)
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)

/-- A lift of a projective involution may have square -1. -/
public theorem project_sq_eq_one_iff (g : SL) :
    project g ^ 2 = 1 ↔ g.val * g.val = 1 ∨ g.val * g.val = -1 := by
  rw [pow_two, ← map_mul]
  exact project_eq_iff (g * g) 1

/-- Projective commutation is commuting or anticommuting at the matrix level. -/
public theorem project_commute_iff (g h : SL) :
    project g * project h = project h * project g ↔
      g.val * h.val = h.val * g.val ∨ g.val * h.val = -(h.val * g.val) := by
  rw [← map_mul, ← map_mul, project_eq_iff]
  rfl

/-- The split two-by-two eigenspace decomposition. -/
@[expose] public def standardInvolutionMatrix : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.diagonal ![-1, -1, 1, 1]

/-- The representative lies in the actual special linear group. -/
@[expose] public def standardInvolutionSL : SL := ⟨standardInvolutionMatrix, by decide⟩

/-- Its image in the central quotient. -/
@[expose] public def standardInvolution : PSL := project standardInvolutionSL

public theorem standardInvolutionSL_sq : standardInvolutionSL ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change standardInvolutionMatrix * standardInvolutionMatrix = 1
  decide

public theorem standardInvolution_sq : standardInvolution ^ 2 = 1 := by
  rw [standardInvolution, ← map_pow, standardInvolutionSL_sq, map_one]

public theorem standardInvolution_ne_one : standardInvolution ≠ 1 := by
  intro h
  have hh : project standardInvolutionSL = project 1 := h
  rcases (project_eq_SL_iff _ _).mp hh with he | he
  · have hv := congrArg (fun a : SL => a.val 0 0) he
    exact (by decide : (-1 : ZMod 3) ≠ 1) hv
  · have hv := congrArg (fun a : SL => a.val 2 2) he
    exact (by decide : (1 : ZMod 3) ≠ -1) hv

/-- The central quotient does not kill the representative. -/
public theorem standardInvolution_orderOf : orderOf standardInvolution = 2 :=
  orderOf_eq_prime standardInvolution_sq standardInvolution_ne_one

/-- The full centralizer in the projective group. -/
public abbrev standardCentralizer := Subgroup.centralizer ({standardInvolution} : Set PSL)

/-- The full projective centralizer includes eigenspace interchange. -/
public theorem project_mem_standardCentralizer_iff (g : SL) :
    project g ∈ standardCentralizer ↔
      g.val * standardInvolutionMatrix = standardInvolutionMatrix * g.val ∨
        g.val * standardInvolutionMatrix = -(standardInvolutionMatrix * g.val) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact project_commute_iff g standardInvolutionSL

/-- Interchange the two eigenspaces of the representative. -/
@[expose] public def blockSwapMatrix : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] public def blockSwapSL : SL := ⟨blockSwapMatrix, by decide⟩

/-- The projective centralizer contains the block interchange. -/
public theorem blockSwap_project_mem_standardCentralizer :
    project blockSwapSL ∈ standardCentralizer := by
  apply (project_mem_standardCentralizer_iff _).mpr
  right
  decide

/-- The block interchange is absent from the ordinary matrix centralizer. -/
public theorem blockSwapSL_not_mem_linearCentralizer :
    blockSwapSL ∉ Subgroup.centralizer ({standardInvolutionSL} : Set SL) := by
  intro h
  have he := congrArg (fun a : SL => a.val)
    (Subgroup.mem_centralizer_singleton_iff.mp h)
  exact (by decide : blockSwapMatrix * standardInvolutionMatrix ≠
    standardInvolutionMatrix * blockSwapMatrix) he

end Matrix.PSL4Three.TwoLocal
