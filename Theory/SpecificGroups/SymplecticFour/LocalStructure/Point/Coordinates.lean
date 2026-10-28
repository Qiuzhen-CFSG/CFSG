module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Coordinates for the symplectic point-local extension

The determinant-one subgroup of the stabilizer of the line spanned by e₀ is
exactly the subgroup fixing e₀. Its action on e₀-perpendicular modulo e₀ is the
middle 2-by-2 submatrix in the ordered basis (e₀,e₁,f₀,f₁). We construct this
surjective map to SL₂ and an explicit Levi section in the original matrix group.

In characteristic two its kernel has coordinates (u,v,z), with multiplication
(u,v,z)(u',v',z') = (u+u',v+v',z+z'+uv'+vu'). The kernel is consequently
nontrivial elementary abelian. The two middle coordinates give a surjective
homomorphism onto the additive natural two-space. Levi conjugation acts by
literal multiplication by its SL₂ matrix on these coordinates and fixes z.

The identification of the central fixed subgroup and the nonbinary commutator
assertion are separate extensions of this coordinate calculation.

Source: the concrete point-local calculation supporting Aschbacher--Smith,
F.1.12(I)(2), refs/quasithin.pdf, printed pp.262--264 (1 March 2004 manuscript).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

theorem pointParabolic_smul_e_zero (g : stabilizer (point F)) :
    g.val • e (F := F) 0 = g.val.val (.inl 0) (.inl 0) • e (F := F) 0 := by
  have h := (mem_pointParabolic_iff g.val).mp g.property
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [smul_eq_mulVec, e, Matrix.mulVec_single, h.1]
  | inr i => simp [smul_eq_mulVec, e, Matrix.mulVec_single, h.2 i]

theorem determinantCharacter_point_coe (g : stabilizer (point F)) :
    (determinantCharacter (point F) g : F) = g.val.val (.inl 0) (.inl 0) := by
  simp only [determinantCharacter, MonoidHom.comp_apply, LinearEquiv.coe_det]
  have hm : (restriction (point F) g).toLinearMap =
      g.val.val (.inl 0) (.inl 0) • (1 : Module.End F (point F)) := by
    ext x : 1
    apply Subtype.ext
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    change g.val • x.val = g.val.val (.inl 0) (.inl 0) • x.val
    rw [← ha]
    change toLinear g.val (a • e (F := F) 0) = _
    rw [map_smul]
    change a • (g.val • e (F := F) 0) = _
    rw [pointParabolic_smul_e_zero]
    simp [smul_smul, mul_comm]
  rw [hm, LinearMap.det_smul, finrank_point]
  simp

theorem mem_pointLocal_iff_fixed (g : Sp F) :
    g ∈ pointLocal ↔ g • e (F := F) 0 = e (F := F) 0 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hd : (determinantCharacter (point F) p : F) = 1 :=
      congrArg Units.val hp
    have hg : p.val.val (.inl 0) (.inl 0) = 1 := (determinantCharacter_point_coe p).symm.trans hd
    change p.val • e (F := F) 0 = e (F := F) 0
    rw [pointParabolic_smul_e_zero p, hg, one_smul]
  · intro hg
    have hp : g ∈ stabilizer (point F) := by
      rw [mem_stabilizer_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change toLinear g (a • e (F := F) 0) ∈ point F
      rw [map_smul]
      change a • (g • e (F := F) 0) ∈ point F
      rw [hg]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    refine ⟨⟨g, hp⟩, ?_, rfl⟩
    apply Units.ext
    rw [determinantCharacter_point_coe]
    have h := congrFun hg (.inl 0)
    simpa [smul_eq_mulVec, e, Matrix.mulVec_single] using h

@[simp] theorem pointLocal_column (g : pointLocal (F := F)) (i : Fin 2 ⊕ Fin 2) :
    g.val.val i (.inl 0) = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i (.inl 0) := by
  have h := congrFun ((mem_pointLocal_iff_fixed g.val).mp g.property) i
  simpa [smul_eq_mulVec, e, Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using h

@[simp] theorem pointLocal_row (g : pointLocal (F := F)) (j : Fin 2 ⊕ Fin 2) :
    g.val.val (.inr 0) j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inr 0) j := by
  have h := preserves_form g.val (Pi.single j 1) (e (F := F) 0)
  rw [(mem_pointLocal_iff_fixed g.val).mp g.property] at h
  simpa [form_e_right, smul_eq_mulVec, Matrix.mulVec_single,
    Matrix.one_apply, Pi.single_apply, eq_comm] using h

/-- Indices of the quotient of the perpendicular space by the fixed line. -/
def middleIndex : Fin 2 → Fin 2 ⊕ Fin 2 := ![.inl 1, .inr 1]

def pointQuotientMatrix (g : pointLocal (F := F)) : Matrix (Fin 2) (Fin 2) F :=
  g.val.val.submatrix middleIndex middleIndex

theorem pointQuotientMatrix_det (g : pointLocal (F := F)) :
    (pointQuotientMatrix g).det = 1 := by
  have h := preserves_form g.val (e (F := F) 1) (Pi.single (.inr 1) 1)
  simpa [pointQuotientMatrix, middleIndex, Matrix.det_fin_two, Matrix.submatrix,
    form_apply, smul_eq_mulVec, e, Matrix.mulVec_single, Fin.sum_univ_two,
    mul_comm] using h

def pointQuotient : pointLocal (F := F) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨pointQuotientMatrix g, pointQuotientMatrix_det g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    ext i j
    change (g.val.val * h.val.val) (middleIndex i) (middleIndex j) =
      (pointQuotientMatrix g * pointQuotientMatrix h) i j
    fin_cases i <;> fin_cases j <;>
      simp [pointQuotientMatrix, middleIndex, Matrix.mul_apply, Matrix.submatrix,
        Fintype.sum_sum_type, Fin.sum_univ_two]

/-- The Levi factor fixes the first hyperbolic pair and acts on the second. -/
def pointLeviMatrix (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, 0; 0, A 0 0] !![0, 0; 0, A 0 1]
    !![0, 0; 0, A 1 0] !![1, 0; 0, A 1 1]

theorem pointLeviMatrix_mem (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    pointLeviMatrix A ∈ Matrix.symplecticGroup (Fin 2) F := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  rw [pointLeviMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hA]

def pointLevi (A : Matrix.SpecialLinearGroup (Fin 2) F) : pointLocal (F := F) :=
  ⟨⟨pointLeviMatrix A, pointLeviMatrix_mem A⟩, by
    rw [mem_pointLocal_iff_fixed]
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [pointLeviMatrix, e, Matrix.mulVec_single]
    | inr i => fin_cases i <;> simp [pointLeviMatrix, e, Matrix.mulVec_single]⟩

@[simp] theorem pointQuotient_pointLevi (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    pointQuotient (pointLevi A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem pointQuotient_surjective : Function.Surjective (pointQuotient (F := F)) :=
  fun A => ⟨pointLevi A, pointQuotient_pointLevi A⟩

variable [CharP F 2]
open scoped CharTwo

/-- The radical coordinates are the two middle entries and top entry of column f₀. -/
def pointRadicalMatrix (u v z : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, v; 0, 1] !![z, u; u, 0]
    !![0, 0; 0, 0] !![1, 0; v, 1]

theorem pointRadicalMatrix_mem (u v z : F) :
    pointRadicalMatrix u v z ∈ Matrix.symplecticGroup (Fin 2) F := by
  rw [pointRadicalMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def pointRadicalElement (u v z : F) : pointLocal (F := F) :=
  ⟨⟨pointRadicalMatrix u v z, pointRadicalMatrix_mem u v z⟩, by
    rw [mem_pointLocal_iff_fixed]
    funext i
    cases i with
    | inl i => fin_cases i <;> simp [pointRadicalMatrix, e, Matrix.mulVec_single]
    | inr i => fin_cases i <;> simp [pointRadicalMatrix, e, Matrix.mulVec_single]⟩

@[simp] theorem pointQuotient_pointRadicalElement (u v z : F) :
    pointQuotient (pointRadicalElement u v z) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The intrinsic normal radical, defined as the kernel of the actual quotient action. -/
def pointRadical : Subgroup (pointLocal (F := F)) := pointQuotient.ker

instance pointRadical_normal : (pointRadical (F := F)).Normal :=
  inferInstanceAs (pointQuotient (F := F)).ker.Normal

@[simp] theorem pointRadicalElement_mem (u v z : F) :
    pointRadicalElement u v z ∈ pointRadical := pointQuotient_pointRadicalElement u v z


theorem pointRadical_eq_element (g : pointLocal (F := F)) (hg : g ∈ pointRadical) :
    g = pointRadicalElement (g.val.val (.inl 1) (.inr 0))
      (g.val.val (.inr 1) (.inr 0)) (g.val.val (.inl 0) (.inr 0)) := by
  have hq : pointQuotient g = 1 := hg
  have h00 : g.val.val (.inl 1) (.inl 1) = 1 :=
    congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 0 0) hq
  have h01 : g.val.val (.inl 1) (.inr 1) = 0 :=
    congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 0 1) hq
  have h10 : g.val.val (.inr 1) (.inl 1) = 0 :=
    congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 1 0) hq
  have h11 : g.val.val (.inr 1) (.inr 1) = 1 :=
    congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A 1 1) hq
  have ht1 : g.val.val (.inl 0) (.inl 1) = g.val.val (.inr 1) (.inr 0) := by
    have h := preserves_form g.val (Pi.single (.inr 0) 1) (e (F := F) 1)
    simpa [form_apply, smul_eq_mulVec, e, Matrix.mulVec_single, Fin.sum_univ_two,
      h00, h10, CharTwo.add_eq_zero] using h
  have ht2 : g.val.val (.inl 0) (.inr 1) = g.val.val (.inl 1) (.inr 0) := by
    have h := preserves_form g.val (Pi.single (.inr 0) 1) (Pi.single (.inr 1) 1)
    simpa [form_apply, smul_eq_mulVec, Matrix.mulVec_single, Fin.sum_univ_two,
      h01, h11, CharTwo.add_eq_zero] using h
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, h00, h01, h10, h11, ht1, ht2]

@[simp] theorem pointRadicalElement_zero : pointRadicalElement (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pointRadicalElement, pointRadicalMatrix]

theorem pointRadicalElement_mul (u v z u' v' z' : F) :
    pointRadicalElement u v z * pointRadicalElement u' v' z' =
      pointRadicalElement (u + u') (v + v') (z + z' + u * v' + v * u') := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change (pointRadicalMatrix u v z * pointRadicalMatrix u' v' z') i j = _
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem pointRadicalElement_comm (u v z u' v' z' : F) :
    pointRadicalElement u v z * pointRadicalElement u' v' z' =
      pointRadicalElement u' v' z' * pointRadicalElement u v z := by
  rw [pointRadicalElement_mul, pointRadicalElement_mul]
  congr 1 <;> ring

@[simp] theorem pointRadicalElement_sq (u v z : F) :
    pointRadicalElement u v z ^ 2 = 1 := by
  rw [pow_two, pointRadicalElement_mul]
  simp [mul_comm]


theorem pointRadical_pow_two (g : pointRadical (F := F)) : g ^ 2 = 1 := by
  apply Subtype.ext
  change g.val ^ 2 = 1
  rw [pointRadical_eq_element g.val g.property]
  exact pointRadicalElement_sq _ _ _

instance pointRadical_elementaryAbelian : IsElementaryAbelian 2 (pointRadical (F := F)) where
  toIsMulCommutative := ⟨⟨by
    intro a b
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    rw [pointRadical_eq_element a.val a.property, pointRadical_eq_element b.val b.property]
    exact pointRadicalElement_comm _ _ _ _ _ _⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr pointRadical_pow_two

/-- The quotient by the radical is the concrete special linear group. -/
def pointRadicalQuotientEquiv :
    pointLocal (F := F) ⧸ pointRadical ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
  QuotientGroup.quotientKerEquivOfSurjective pointQuotient pointQuotient_surjective

theorem pointRadicalElement_eq_iff (u v z u' v' z' : F) :
    pointRadicalElement u v z = pointRadicalElement u' v' z' ↔
      u = u' ∧ v = v' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨congrArg (fun g : pointLocal (F := F) => g.val.val (.inl 1) (.inr 0)) h,
      congrArg (fun g : pointLocal (F := F) => g.val.val (.inr 1) (.inr 0)) h,
      congrArg (fun g : pointLocal (F := F) => g.val.val (.inl 0) (.inr 0)) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The two noncentral radical coordinates, viewed as an additive group. -/
def pointRadicalVector : pointRadical (F := F) →* Multiplicative (Fin 2 → F) where
  toFun q := Multiplicative.ofAdd ![q.val.val.val (.inl 1) (.inr 0),
    q.val.val.val (.inr 1) (.inr 0)]
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' q r := by
    apply Multiplicative.toAdd.injective
    change ![(q.val * r.val).val.val (.inl 1) (.inr 0),
      (q.val * r.val).val.val (.inr 1) (.inr 0)] =
      ![q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0)] +
      ![r.val.val.val (.inl 1) (.inr 0), r.val.val.val (.inr 1) (.inr 0)]
    conv_lhs => rw [pointRadical_eq_element q.val q.property,
      pointRadical_eq_element r.val r.property, pointRadicalElement_mul]
    funext i
    fin_cases i <;> rfl

@[simp] theorem pointRadicalVector_element (u v z : F) :
    pointRadicalVector ⟨pointRadicalElement u v z, pointRadicalElement_mem u v z⟩ =
      Multiplicative.ofAdd ![u, v] := rfl

theorem pointRadicalVector_surjective : Function.Surjective (pointRadicalVector (F := F)) := by
  intro v
  refine ⟨⟨pointRadicalElement (v.toAdd 0) (v.toAdd 1) 0,
    pointRadicalElement_mem _ _ _⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl


/-- The explicit Levi conjugation, before passing to any central quotient. -/
theorem pointLevi_mul_radical (A : Matrix.SpecialLinearGroup (Fin 2) F) (u v z : F) :
    pointLevi A * pointRadicalElement u v z =
      pointRadicalElement (A 0 0 * u + A 0 1 * v) (A 1 0 * u + A 1 1 * v) z *
        pointLevi A := by
  have hA : A 0 0 * A 1 1 + A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, CharTwo.sub_eq_add] using A.property
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change (pointLeviMatrix A * pointRadicalMatrix u v z) i j =
    (pointRadicalMatrix (A 0 0 * u + A 0 1 * v) (A 1 0 * u + A 1 1 * v) z *
      pointLeviMatrix A) i j
  fin_cases i <;> fin_cases j <;>
    simp [pointLeviMatrix, pointRadicalMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    solve
    | (linear_combination (norm := (ring_nf; simp)) v * hA)
    | (linear_combination (norm := (ring_nf; simp)) u * hA)


omit [CharP F 2] in
@[simp] theorem pointQuotient_ker : (pointQuotient (F := F)).ker = pointRadical := rfl

theorem pointLevi_conj_radical (A : Matrix.SpecialLinearGroup (Fin 2) F) (u v z : F) :
    pointLevi A * pointRadicalElement u v z * (pointLevi A)⁻¹ =
      pointRadicalElement (A 0 0 * u + A 0 1 * v) (A 1 0 * u + A 1 1 * v) z := by
  rw [pointLevi_mul_radical, mul_assoc, mul_inv_cancel, mul_one]

instance pointRadical_nontrivial : Nontrivial (pointRadical (F := F)) := by
  refine ⟨⟨⟨pointRadicalElement 0 0 1, pointRadicalElement_mem 0 0 1⟩, 1, ?_⟩⟩
  intro h
  have he := congrArg (fun q : pointRadical (F := F) => q.val.val.val (.inl 0) (.inr 0)) h
  exact one_ne_zero he

/-- The radical has exponent exactly two, not merely dividing two. -/
theorem pointRadical_exponent [Finite F] : Monoid.exponent (pointRadical (F := F)) = 2 :=
  IsElementaryAbelian.exponent_eq_prime

end Theory.SpecificGroups.SymplecticFour
