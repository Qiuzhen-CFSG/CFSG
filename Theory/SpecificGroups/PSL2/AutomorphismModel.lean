module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.GroupAction.AutomorphismFixedTransport
import Mathlib.Tactic.LinearCombination

/-!
# The genuine binary PSL₂ model and its field action

The group is the matrix quotient SL₂/Z(SL₂). In characteristic two the center
is trivial, so the actual quotient map is an isomorphism. Entrywise field
automorphisms descend through this isomorphism. The inner subgroup below is
the range of the conjugation homomorphism, rather than a family label.

These are the model conventions used in GLS, Volume 2, Theorem 26.24, Step 5.
The quotient and field-action proofs are adapted from
`BenderSuzuki.Converse.PSL2` and the prerequisite's `Linear.FieldAction`, with
no dependency on that campaign. Automorphism coverage is a separate theorem.
-/

namespace Theory.PSL2

/-- The actual projective special linear matrix group. -/
public abbrev Group (K : Type*) [Field K] :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) K

/-- The finite field used in the binary matrix model. -/
public abbrev BinaryField (n : ℕ) := GaloisField 2 n

/-- PSL₂ over the field of order `2 ^ n` (with `n > 0` in cardinality results). -/
public abbrev BinaryGroup (n : ℕ) := Group (BinaryField n)

variable (K : Type*) [Field K]

/-- The canonical quotient map from SL₂ to PSL₂. -/
@[expose] public def quotientMap : Matrix.SpecialLinearGroup (Fin 2) K →* Group K :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))

public theorem quotientMap_surjective : Function.Surjective (quotientMap K) :=
  QuotientGroup.mk'_surjective _

public theorem sl2_center_eq_bot [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  simp only [Fintype.card_fin] at hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 :=
    eq_of_sub_eq_zero (pow_eq_zero_iff (n := 2) (by decide) |>.1 hsq)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

public theorem quotientMap_injective [CharP K 2] :
    Function.Injective (quotientMap K) := by
  rw [← MonoidHom.ker_eq_bot_iff, quotientMap, QuotientGroup.ker_mk']
  exact sl2_center_eq_bot K

/-- In characteristic two this isomorphism is the canonical quotient map. -/
@[expose] public noncomputable def sl2QuotientEquiv [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* Group K :=
  MulEquiv.ofBijective (quotientMap K)
    ⟨quotientMap_injective K, quotientMap_surjective K⟩

/-- The genuine inner automorphism subgroup. -/
@[expose] public def inner : Subgroup (MulAut (Group K)) :=
  (MulAut.conj : Group K →* MulAut (Group K)).range

public theorem mem_inner_iff (a : MulAut (Group K)) :
    a ∈ inner K ↔ ∃ g : Group K, a = MulAut.conj g := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, hg.symm⟩

public instance inner_normal : (inner K).Normal := by
  refine ⟨?_⟩
  intro a ha b
  obtain ⟨g, rfl⟩ := (mem_inner_iff K a).mp ha
  apply (mem_inner_iff K _).mpr
  refine ⟨b g, ?_⟩
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable {K}

/-- Entrywise field automorphisms of determinant-one matrices. -/
@[expose] public def sl2FieldAut (σ : K ≃+* K) :
    MulAut (Matrix.SpecialLinearGroup (Fin 2) K) where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv g := by ext i j; exact σ.symm_apply_apply (g i j)
  right_inv g := by ext i j; exact σ.apply_symm_apply (g i j)
  map_mul' := (Matrix.SpecialLinearGroup.map σ.toRingHom).map_mul

/-- The field action on the actual quotient group. -/
@[expose] public noncomputable def fieldAut [CharP K 2] (σ : K ≃+* K) :
    MulAut (Group K) := MulAut.congr (sl2QuotientEquiv K) (sl2FieldAut σ)

public theorem fieldAut_apply_quotientMap [CharP K 2] (σ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    fieldAut σ (quotientMap K g) =
      quotientMap K (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  change sl2QuotientEquiv K (sl2FieldAut σ
    ((sl2QuotientEquiv K).symm (sl2QuotientEquiv K g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Theory.PSL2
