module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent.SplitAssembly
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Invariant lines in reducible unitary three-space

A proper nonzero invariant subspace has dimension one or two. In the second
case its Hermitian orthogonal complement has dimension one and is invariant
under the same literal special-unitary matrices. This includes degenerate
planes: only the ambient form must be nondegenerate.

For the stored conjugation and Gram matrix, conjugating a subspace converts
Hermitian orthogonality to orthogonality for the corresponding bilinear form.
Conjugation preserves cardinality over the finite coefficient field, hence
also dimension. The determinant hypothesis then gives the complement dimension
formula. No field-cardinality formula, splitting or normalizing involution is
needed. Under the source no-Borel hypothesis, the resulting projective line
supplies an anisotropic common eigenvector via `SplitAssembly`.

Source: the reducible geometry used in GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. The complement argument adapts
`ClassicalUnitary.UnitaryFourThree.NondegenerateStabilizers.Geometry` to an
arbitrary stored Hermitian form; the full common-eigenbasis assembly is separate.
-/

public section

open Matrix Module BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.AbelianFrame.InvariantLine
variable {E : Type*} [Field E]

private theorem conj_conj (J : HermitianForm 3 E) (a : E) :
    J.conj (J.conj a) = a := J.conj_involutive a

private def conjugateSubspace (J : HermitianForm 3 E)
    (W : Submodule E (Fin 3 → E)) : Submodule E (Fin 3 → E) where
  carrier := {v | (fun i => J.conj (v i)) ∈ W}
  zero_mem' := by
    change (fun i : Fin 3 => J.conj (0 : E)) ∈ W
    simpa only [map_zero, Pi.zero_def] using W.zero_mem
  add_mem' := by
    intro v w hv hw
    change (fun i => J.conj ((v + w) i)) ∈ W
    simpa only [Pi.add_apply, map_add, Pi.add_def] using W.add_mem hv hw
  smul_mem' := by
    intro c v hv
    change (fun i => J.conj ((c • v) i)) ∈ W
    simpa only [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_def] using
      W.smul_mem (J.conj c) hv

private def conjugateSubspaceEquiv (J : HermitianForm 3 E)
    (W : Submodule E (Fin 3 → E)) : W ≃ conjugateSubspace J W where
  toFun v := ⟨fun i => J.conj (v.val i), by
    change (fun i => J.conj (J.conj (v.val i))) ∈ W
    simpa only [conj_conj] using v.property⟩
  invFun v := ⟨fun i => J.conj (v.val i), v.property⟩
  left_inv v := Subtype.ext (funext fun i => J.conj_involutive _)
  right_inv v := Subtype.ext (funext fun i => J.conj_involutive _)

private theorem finrank_conjugateSubspace [Finite E] (J : HermitianForm 3 E)
    (W : Submodule E (Fin 3 → E)) :
    finrank E (conjugateSubspace J W) = finrank E W := by
  let : Fintype E := Fintype.ofFinite E
  have h := Nat.card_congr (conjugateSubspaceEquiv J W)
  rw [Module.natCard_eq_pow_finrank (K := E) (V := W),
    Module.natCard_eq_pow_finrank (K := E) (V := conjugateSubspace J W)] at h
  exact (Nat.pow_right_injective (by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card) h).symm

private def orthogonal (J : HermitianForm 3 E) (W : Submodule E (Fin 3 → E)) :
    Submodule E (Fin 3 → E) := J.form.toBilin'.orthogonal (conjugateSubspace J W)

private theorem mem_orthogonal_iff (J : HermitianForm 3 E)
    (W : Submodule E (Fin 3 → E)) (v : Fin 3 → E) :
    v ∈ orthogonal J W ↔
      ∀ w ∈ W, dotProduct (fun i => J.conj (w i)) (J.form.mulVec v) = 0 := by
  change (∀ w ∈ conjugateSubspace J W, J.form.toBilin' w v = 0) ↔ _
  simp only [Matrix.toBilin'_apply']
  constructor
  · intro h w hw
    exact h (fun i => J.conj (w i)) (by
      change (fun i => J.conj (J.conj (w i))) ∈ W
      simpa only [conj_conj] using hw)
  · intro h w hw
    have hh := h (fun i => J.conj (w i)) hw
    simpa only [conj_conj] using hh

private theorem finrank_orthogonal [Finite E] (J : HermitianForm 3 E)
    (W : Submodule E (Fin 3 → E)) :
    finrank E (orthogonal J W) = 3 - finrank E W := by
  rw [orthogonal, LinearMap.BilinForm.finrank_orthogonal
    (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' J.form J.form_nondegenerate),
    finrank_conjugateSubspace]
  simp

private theorem pairing_invariant (J : HermitianForm 3 E) (x : J.specialSubgroup)
    (v w : Fin 3 → E) :
    dotProduct (fun i => J.conj ((x • v) i)) (J.form.mulVec (x • w)) =
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec w) := by
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  let A := x.val.val
  change star (A *ᵥ v) ⬝ᵥ J.form *ᵥ (A *ᵥ w) = star v ⬝ᵥ J.form *ᵥ w
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  change star v ᵥ* (J.conjTranspose A * J.form * A) ⬝ᵥ w = _
  rw [(J.mem_specialSubgroup_iff x.val).mp x.property |>.1]
  exact (Matrix.dotProduct_mulVec _ _ _).symm

private theorem orthogonal_invariant (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (W : Submodule E (Fin 3 → E))
    (hW : ∀ h : H, ∀ v ∈ W, specialNatural J h.val v ∈ W) :
    ∀ h : H, ∀ v ∈ orthogonal J W, specialNatural J h.val v ∈ orthogonal J W := by
  intro h v hv
  rw [mem_orthogonal_iff] at hv ⊢
  intro w hw
  have hi : h.val⁻¹ • w ∈ W := hW h⁻¹ w hw
  have hp := pairing_invariant J h.val (h.val⁻¹ • w) v
  rw [smul_inv_smul] at hp
  change dotProduct (fun i => J.conj (w i)) (J.form.mulVec (h.val • v)) = 0
  exact hp.trans (hv _ hi)

private theorem commonEigenline_of_invariant_one (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (W : Submodule E (Fin 3 → E))
    (hdim : finrank E W = 1)
    (hW : ∀ h : H, ∀ v ∈ W, specialNatural J h.val v ∈ W) :
    ∃ l : ℙ E (Fin 3 → E), l ∈ commonEigenlines J H := by
  have hW0 : W ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hdim
    exact Nat.zero_ne_one hdim
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hspan : W = E ∙ v := eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hv0
  refine ⟨Projectivization.mk E v hv0, ?_⟩
  intro h hh
  have hmem := hW ⟨h, hh⟩ v hv
  rw [hspan, Submodule.mem_span_singleton] at hmem
  change h.val • Projectivization.mk E v hv0 = Projectivization.mk E v hv0
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact hmem

end UnitaryThree.OddTorusNormalizer.AbelianFrame.InvariantLine

namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
open InvariantLine
variable {E : Type*} [Field E] [Finite E]

/-- Every reducible natural special-unitary action in dimension three has a
common projective eigenline over its original finite coefficient field. -/
theorem exists_commonEigenline_of_reducible (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup)
    (hred : ¬ Representation.IsIrreducible ((specialNatural J).comp H.subtype)) :
    ∃ l : ℙ E (Fin 3 → E), l ∈ commonEigenlines J H := by
  let ρ := (specialNatural J).comp H.subtype
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    exact (bot_ne_top : (⊥ : Submodule E (Fin 3 → E)) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule he)
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
  have hex : ∃ W : Subrepresentation ρ, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hn
    apply hred
    refine { eq_bot_or_eq_top := ?_ }
    intro W
    by_cases hb : W = ⊥
    · exact Or.inl hb
    · exact Or.inr (by by_contra ht; exact hn ⟨W, hb, ht⟩)
  obtain ⟨W, hW0, hWt⟩ := hex
  have h0 : W.toSubmodule ≠ ⊥ := fun hz =>
    hW0 (Subrepresentation.toSubmodule_injective hz)
  have ht : W.toSubmodule ≠ ⊤ := fun hz =>
    hWt (Subrepresentation.toSubmodule_injective hz)
  have hpos : finrank E W.toSubmodule ≠ 0 := fun hz =>
    h0 (Submodule.finrank_eq_zero.mp hz)
  have hlt := Submodule.finrank_lt ht
  have hdim : finrank E (Fin 3 → E) = 3 := by simp
  rw [hdim] at hlt
  have hd : finrank E W.toSubmodule = 1 ∨ finrank E W.toSubmodule = 2 := by omega
  have hstable : ∀ h : H, ∀ v ∈ W.toSubmodule,
      specialNatural J h.val v ∈ W.toSubmodule := fun h _ hv =>
    W.apply_mem_toSubmodule h hv
  rcases hd with hd | hd
  · exact commonEigenline_of_invariant_one J H W.toSubmodule hd hstable
  · apply commonEigenline_of_invariant_one J H (orthogonal J W.toSubmodule)
    · rw [finrank_orthogonal, hd]
    · exact orthogonal_invariant J H W.toSubmodule hstable

/-- The source no-Borel condition makes the line obtained from reducibility
anisotropic, giving the exact vector and scalar-action input to spectral descent. -/
theorem exists_anisotropic_commonEigenvector_of_reducible (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    (hred : ¬ Representation.IsIrreducible ((specialNatural J).comp H.subtype)) :
    ∃ v : Fin 3 → E,
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) ≠ 0 ∧
        ∀ h : H, ∃ a : E, specialNatural J h.val v = a • v := by
  obtain ⟨l, hl⟩ := exists_commonEigenline_of_reducible J H hred
  exact ⟨l.rep, commonEigenline_rep_spectral_data J H hB hl⟩

end UnitaryThree.OddTorusNormalizer.AbelianFrame
