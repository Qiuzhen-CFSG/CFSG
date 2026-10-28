module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Coordinates

/-!
# The concrete alpha groups for tensor involution fixers

For j with central shear block B, the scalar line consists of the shears t B.
This is exactly the definition g + I = t(j + I) of the α-group in Aschbacher–Seitz,
*Involutions in Chevalley groups over fields of even order*, §11, printed p.30,
Nagoya Math. J. 63 (1976), DOI 10.1017/S0027763000017438.

On the two coordinate axes these are the actual root groups. For a mixed c₂
involution we retain the α-group. When j centralizes coefficient σ, the subgroup
with σ-fixed parameters is exactly the fixed subgroup of σ on that α-group.
These definitions are shared inputs for the pointwise-fixer computation in
Aschbacher–Smith, K.3.4.2, printed p.457; no fixer equality is assumed here.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open scoped Matrix TensorProduct Classical
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

/-- The scalar line through a central involution's natural displacement. -/
noncomputable def centralAlphaParameter (a b : F) : Multiplicative F →* Sp F where
  toFun t := Plane.shearSp (t.toAdd • centralBlock a b)
  map_one' := by
    apply Subtype.ext
    simp [Plane.shearSp]
  map_mul' t u := by
    apply Subtype.ext
    simp [Plane.shearSp, add_smul, Matrix.fromBlocks_multiply, add_comm]

/-- The concrete α-group of AS76a §11, for a central normal form. In type c₂
this is used in place of a root group. -/
noncomputable def centralAlpha (a b : F) : Subgroup (Sp F) :=
  (centralAlphaParameter a b).range

/-- Fixed coefficients for the source's coefficient involution σ. -/
def sigmaFixedCoefficients (σ : F ≃+* F) : Subgroup (Multiplicative F) where
  carrier := {t | σ t.toAdd = t.toAdd}
  one_mem' := map_zero σ
  mul_mem' {x y} hx hy := by
    change σ (x.toAdd + y.toAdd) = x.toAdd + y.toAdd
    change σ x.toAdd = x.toAdd at hx
    change σ y.toAdd = y.toAdd at hy
    rw [map_add,hx,hy]
  inv_mem' {x} hx := by
    change σ (-x.toAdd) = -x.toAdd
    change σ x.toAdd = x.toAdd at hx
    rw [map_neg,hx]

/-- The σ-fixed part of the α-line, with the literal matrix inclusion. -/
noncomputable def centralSigmaAlpha (σ : F ≃+* F) (a b : F) : Subgroup (Sp F) :=
  (sigmaFixedCoefficients σ).map (centralAlphaParameter a b)

lemma mem_centralSigmaAlpha (σ : F ≃+* F) (a b : F) (g : Sp F) :
    g ∈ centralSigmaAlpha σ a b ↔
      ∃ t : F, σ t = t ∧ Plane.shearSp (t • centralBlock a b) = g := by
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨t.toAdd,ht,he⟩
  · rintro ⟨t,ht,he⟩
    exact ⟨Multiplicative.ofAdd t,ht,he⟩

variable [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
/-- Literal agreement with the definition g + I = t(j + I) in AS76a,
Section 11, printed p.30. -/
lemma mem_centralAlpha_iff (a b : F) (g : Sp F) :
    g ∈ centralAlpha a b ↔ ∃ t : F,
      g.val + 1 = t • ((rootElement 0 a * rootElement 4 b : Sp F).val + 1) := by
  rw [central_matrix]
  have he (t : F) :
      (Plane.shearSp (t • centralBlock a b)).val + 1 =
        t • (Matrix.fromBlocks 1 !![a,b;b,0] 0 1 + 1) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
    all_goals simp [Plane.shearSp, centralBlock, Matrix.fromBlocks,
      Matrix.one_apply, CharTwo.add_self_eq_zero]
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t.toAdd, he t.toAdd⟩
  · rintro ⟨t,ht⟩
    refine ⟨Multiplicative.ofAdd t,?_⟩
    apply Subtype.ext
    exact add_right_cancel ((he t).trans ht.symm)
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F]

lemma centralAlphaParameter_injective {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    Function.Injective (centralAlphaParameter a b) := by
  intro t u he
  suffices ht : t.toAdd = u.toAdd by exact congrArg Multiplicative.ofAdd ht
  rcases hab with ha | hb
  · have hh := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 0)) he
    change t.toAdd * a = u.toAdd * a at hh
    exact mul_right_cancel₀ ha hh
  · have hh := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 1)) he
    change t.toAdd * b = u.toAdd * b at hh
    exact mul_right_cancel₀ hb hh

lemma field_centralAlphaParameter (σ : F ≃+* F) (a b : F) (t : Multiplicative F) :
    DiagramAutomorphisms.fieldAutomorphism σ (centralAlphaParameter a b t) =
      centralAlphaParameter (σ a) (σ b) (Multiplicative.ofAdd (σ t.toAdd)) := by
  apply Subtype.ext
  ext i j
  change σ ((Plane.shearSp (t.toAdd • centralBlock a b)).val i j) =
    (Plane.shearSp (σ t.toAdd • centralBlock (σ a) (σ b))).val i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals simp [Plane.shearSp, centralBlock, Matrix.fromBlocks, Matrix.one_apply]

/-- For a normal form centralizing σ, the parameter-defined subgroup is
exactly the fixed subgroup of σ on the source α-group. -/
lemma mem_centralSigmaAlpha_iff_fixed (σ : F ≃+* F) {a b : F}
    (hab : a ≠ 0 ∨ b ≠ 0) (ha : σ a = a) (hb : σ b = b) (g : Sp F) :
    g ∈ centralSigmaAlpha σ a b ↔
      g ∈ centralAlpha a b ∧ DiagramAutomorphisms.fieldAutomorphism σ g = g := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨⟨t,rfl⟩,?_⟩
    rw [field_centralAlphaParameter,ha,hb]
    change σ t.toAdd = t.toAdd at ht
    rw [ht]
    rfl
  · rintro ⟨⟨t,rfl⟩,ht⟩
    refine ⟨t,?_,rfl⟩
    rw [field_centralAlphaParameter,ha,hb] at ht
    have he := centralAlphaParameter_injective hab ht
    exact congrArg Multiplicative.toAdd he
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

lemma centralAlphaParameter_eq_roots (a b : F) (t : Multiplicative F) :
    centralAlphaParameter a b t = rootElement 0 (t.toAdd*a) * rootElement 4 (t.toAdd*b) := by
  rw [central_eq_shear]
  change Plane.shearSp (t.toAdd • centralBlock a b) = _
  congr 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [centralBlock]

/-- On the b₁ axis the α-group is the actual long root group. -/
lemma centralAlpha_left_eq_root {a : F} (ha : a ≠ 0) :
    centralAlpha a 0 = RootSubgroup.group 0 := by
  ext g
  constructor
  · rintro ⟨t,rfl⟩
    rw [centralAlphaParameter_eq_roots, mul_zero, RootSubgroup.element_zero, mul_one]
    exact (RootSubgroup.mem_group_iff _ _).mpr ⟨t.toAdd*a,rfl⟩
  · intro hg
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hg
    refine ⟨Multiplicative.ofAdd (t/a),?_⟩
    rw [centralAlphaParameter_eq_roots]
    simp [ha,RootSubgroup.element_zero]

/-- On the a₂ axis the α-group is the actual short root group. -/
lemma centralAlpha_right_eq_root {b : F} (hb : b ≠ 0) :
    centralAlpha 0 b = RootSubgroup.group 4 := by
  ext g
  constructor
  · rintro ⟨t,rfl⟩
    rw [centralAlphaParameter_eq_roots, mul_zero, RootSubgroup.element_zero, one_mul]
    exact (RootSubgroup.mem_group_iff _ _).mpr ⟨t.toAdd*b,rfl⟩
  · intro hg
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hg
    refine ⟨Multiplicative.ofAdd (t/b),?_⟩
    rw [centralAlphaParameter_eq_roots]
    simp [hb,RootSubgroup.element_zero]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
