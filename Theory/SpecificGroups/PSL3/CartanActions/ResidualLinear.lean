module

public import Theory.SpecificGroups.PSL3.CartanActions.ResidualParameters
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm

/-!
# Linear, field and graph contributions on the binary PSL₃ Borel quotient

A Sylow-preserving linear factor is upper triangular. Comparing its nonzero
diagonal entries modulo the unipotent radical removes that factor from the
torus parameter calculation, retaining the cubic scalar kernel. No chosen
torus is assumed invariant. Powers of a linear-field actor have the expected
coefficient factor, so the order bound on the whole actor bounds that factor.
Residual parameter rigidity then kills the field contribution outside degrees
two and six and excludes every graph-field contribution outside degree two.

The final theorem places a standard residual fixer in the inner-diagonal
image. Removing the remaining linear two-part and transporting arbitrary
Sylows and the special linear cover are separate obligations.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; GLS3, §2.7.
The compatibility proofs adapt the matrix identities in FieldComponentFixer;
the trace/flag input is NormalizerForm.BorelKernel. The imported ATLAS field
transport retains its original source attribution and license.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup
open Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
namespace Matrix.PSL3.CartanActions.ResidualLinear
variable {F : Type*} [Field F]

private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

private theorem linearConjSL_val (m : GL (Fin 3) F) (x : SL(3,F)) :
    (linearConjSL F m x).val = m.val * x.val * m.inv :=
  congrArg Units.val (linearConjSL_toGL F m x)

/-- A triangular linear factor acts trivially on diagonal parameters modulo U. -/
theorem parameters_eq_of_displacement (m : GL (Fin 3) F)
    (hm : m.val 1 0 = 0 ∧ m.val 2 0 = 0 ∧ m.val 2 1 = 0)
    (d e : Fˣ × Fˣ)
    (h : linearConj F m (torusMap F d) * (torusMap F e)⁻¹ ∈ unipotent F) :
    torusMap F d = torusMap F e := by
  obtain ⟨u,hu,hproj⟩ := h
  have hp : projection F (linearConjSL F m (torusSL F d)) =
      projection F (u * torusSL F e) := by
    rw [map_mul, hproj]
    change linearConj F m (torusMap F d) =
      (linearConj F m (torusMap F d) * (torusMap F e)⁻¹) * torusMap F e
    group
  obtain ⟨r,hr⟩ := scalar_of_projection_eq _ _ hp
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  have hn' : ∀ i : Fin 3, m.val i i ≠ 0 := by
    intro i
    fin_cases i
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
    · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
    · exact (mul_ne_zero_iff.mp hn).2
  have heq : m.val * (torusSL F d).val =
      (r • (u * torusSL F e).val) * m.val := by
    rw [← hr, linearConjSL_val, Matrix.mul_assoc, m.inv_val, mul_one]
  have hu0 := (mem_pointLocalSL_iff F u).mp hu.1
  have hu2 := (mem_lineLocalSL_iff F u).mp hu.2
  have hu1 : u.val 1 1 = 1 := by
    have ht := u.property
    rw [Matrix.det_fin_three] at ht
    simpa [hu0.1,hu0.2.1,hu0.2.2,hu2.2.1,hu2.2.2] using ht
  have hd (i : Fin 3) : (torusSL F d).val i i = r * (torusSL F e).val i i := by
    apply mul_left_cancel₀ (hn' i)
    have hh := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a i i) heq
    fin_cases i <;>
      simpa [torusSL_val, SpecialLinearGroup.coe_mul, Matrix.mul_diagonal,
        Matrix.mul_apply, Fin.sum_univ_three, hm.1,hm.2.1,hm.2.2,
        hu0.1,hu0.2.1,hu0.2.2,hu2.2.1,hu2.2.2,hu1,
        mul_comm, mul_left_comm, mul_assoc] using hh
  have hs : (torusSL F d).val = r • (torusSL F e).val := by
    ext i j
    by_cases hij : i = j
    · subst j; exact hd i
    · simp [torusSL_val, hij]
  have hcent : (torusSL F e)⁻¹ * torusSL F d ∈ center SL(3,F) := by
    apply SpecialLinearGroup.mem_center_iff.mpr
    have hv : ((torusSL F e)⁻¹ * torusSL F d).val = Matrix.scalar (Fin 3) r := by
      rw [SpecialLinearGroup.coe_mul, hs, Matrix.mul_smul,
        ← SpecialLinearGroup.coe_mul, inv_mul_cancel]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    refine ⟨r, ?_, hv.symm⟩
    have hh := ((torusSL F e)⁻¹ * torusSL F d).property
    rw [hv] at hh
    simpa using hh
  exact (projection F).eq_iff.mpr (by rwa [projection_ker])



private theorem fieldSL_toGL (τ : F ≃+* F) (x : SL(3,F)) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map τ.toRingHom x) =
      GeneralLinearGroup.map τ.toRingHom (SpecialLinearGroup.toGL x) := Units.ext rfl

/-- Compatibility of coefficient transport with actual linear conjugation. -/
theorem field_linearConj (τ : F ≃+* F) (m : GL (Fin 3) F) :
    fieldAction F τ * linearConj F m =
      linearConj F (GeneralLinearGroup.map τ.toRingHom m) * fieldAction F τ := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, linearConj_mk]
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [fieldSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, fieldSL_toGL]

/-- Powers retain the actual coefficient factor; the actor need not be an involution. -/
theorem linear_field_power (m : GL (Fin 3) F) (σ : F ≃+* F) (j : ℕ) :
    ∃ m' : GL (Fin 3) F,
      (linearConj F m * fieldAction F σ) ^ j = linearConj F m' * fieldAction F (σ ^ j) := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨m',hm'⟩ := ih
    refine ⟨m' * GeneralLinearGroup.map (σ ^ j).toRingHom m, ?_⟩
    rw [pow_succ, hm', map_mul, pow_succ, map_mul]
    calc
      _ = linearConj F m' * (fieldAction F (σ ^ j) * linearConj F m) *
          fieldAction F σ := by group
      _ = _ := by rw [field_linearConj]; group

private theorem stable_linear_factor (m : GL (Fin 3) F) (β : MulAut PSL(3,F))
    (hβ : (unipotent F).map β.toMonoidHom = unipotent F)
    (h : (unipotent F).map (linearConj F m * β).toMonoidHom = unipotent F) :
    (unipotent F).map (linearConj F m).toMonoidHom = unipotent F := by
  have he : (linearConj F m * β).toMonoidHom =
      (linearConj F m).toMonoidHom.comp β.toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, hβ] at h
  exact h

/-- Sylow stability derives triangularity of the linear factor; no Cartan
stability is an input. -/
theorem linear_field_upperTriangular [CharP F 2] (m : GL (Fin 3) F) (σ : F ≃+* F)
    (h : (unipotent F).map (linearConj F m * fieldAction F σ).toMonoidHom = unipotent F) :
    m.val 1 0 = 0 ∧ m.val 2 0 = 0 ∧ m.val 2 1 = 0 :=
  NormalizerForm.linearConj_upperTriangular F m
    (stable_linear_factor m _ (fieldAction_unipotent F σ) h)

/-- A two-power bound for the full linear-field actor implies the same bound
for its coefficient automorphism. -/
theorem coefficient_pow_eq_one [CharP F 2] (m : GL (Fin 3) F) (σ : F ≃+* F) {j : ℕ}
    (hpow : (linearConj F m * fieldAction F σ) ^ j = 1) : σ ^ j = 1 := by
  obtain ⟨m',hm'⟩ := linear_field_power m σ j
  have he : linearConj F m' * fieldAction F (σ ^ j) = 1 := hm'.symm.trans hpow
  have hs : (unipotent F).map
      (linearConj F m' * fieldAction F (σ ^ j)).toMonoidHom = unipotent F := by
    rw [he]
    exact Subgroup.map_id _
  have ht := linear_field_upperTriangular m' (σ ^ j) hs
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have ha : linearConj F m' (torusMap F (Units.map (σ ^ j).toMonoidHom u,1)) *
        (torusMap F (u,1))⁻¹ ∈ unipotent F := by
      have hh := DFunLike.congr_fun he (torusMap F (u,1))
      simp only [MulAut.mul_apply, field_torusMap, map_one, MulAut.one_apply] at hh
      rw [hh, mul_inv_cancel]
      exact (unipotent F).one_mem
    have hp := parameters_eq_of_displacement m' ht _ _ ha
    exact congrArg Units.val (ResidualParameters.projective_axis_injective hp)


/-- The field contribution of an arbitrary linear-field actor fixing the
residual axes vanishes outside degrees two and six. -/
theorem linear_field_coefficient_eq_one [Finite F] [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hstable : (unipotent F).map
      (linearConj F m * fieldAction F σ).toMonoidHom = unipotent F)
    (hpow : (linearConj F m * fieldAction F σ) ^ (2 ^ k) = 1)
    (hfix : ∀ u ∈ pResidual 3 Fˣ,
      (linearConj F m * fieldAction F σ) (torusMap F (u,1)) *
        (torusMap F (u,1))⁻¹ ∈ unipotent F) : σ = 1 := by
  apply ResidualParameters.field_eq_one_of_fixed_axes hF hn2 hn6 σ
    (coefficient_pow_eq_one m σ hpow)
  intro u hu
  apply parameters_eq_of_displacement m (linear_field_upperTriangular m σ hstable)
  simpa only [MulAut.mul_apply, field_torusMap, map_one] using hfix u hu

/-- No triangular linear twist rescues a graph-field actor on the residual
quotient. The whole actor may have any order. -/
theorem linear_graph_field_not_fixed [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (hn2 : n ≠ 2) (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hstable : (unipotent F).map
      (linearConj F m * fieldAction F σ *
        OuterSolvable.OddPrimeCoverage.oppositionGraph F).toMonoidHom = unipotent F) :
    ¬ (∀ u ∈ pResidual 3 Fˣ,
      (linearConj F m * fieldAction F σ *
        OuterSolvable.OddPrimeCoverage.oppositionGraph F) (torusMap F (u,1)) *
        (torusMap F (u,1))⁻¹ ∈ unipotent F) := by
  have hβ : (unipotent F).map
      (fieldAction F σ * OuterSolvable.OddPrimeCoverage.oppositionGraph F).toMonoidHom =
        unipotent F := by
    change (unipotent F).map ((fieldAction F σ).toMonoidHom.comp
      (OuterSolvable.OddPrimeCoverage.oppositionGraph F).toMonoidHom) = _
    rw [← Subgroup.map_map, oppositionGraph_unipotent, fieldAction_unipotent]
  rw [mul_assoc] at hstable
  have ht := NormalizerForm.linearConj_upperTriangular F m
    (stable_linear_factor m _ hβ hstable)
  intro hfix
  apply ResidualParameters.graph_field_not_fixed hF hn hn2 σ
  intro u hu
  apply parameters_eq_of_displacement m ht
  simpa only [MulAut.mul_apply, oppositionGraph_torusMap, field_torusMap,
    inv_one, map_one, map_inv] using hfix u hu

private def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

private theorem graphSL_toGL (x : SL(3,F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

private theorem graph_linearConj (m : GL (Fin 3) F) :
    graph F * linearConj F m = linearConj F (inverseTransposeGL m) * graph F := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    change QuotientGroup.mk (graphSL F (linearConjSL F m x)) =
      QuotientGroup.mk (linearConjSL F (inverseTransposeGL m) (graphSL F x))
    congr 1
    apply SpecialLinearGroup.toGL_injective
    rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
      linearConjSL_toGL, graphSL_toGL]

private theorem field_commute_graph (τ : F ≃+* F) :
    Commute (fieldAction F τ) (graph F) := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, fieldAction_mk, graph_mk]
    rw [map_inv]
    congr 2

/-- The standard subgroup has the concrete linear-field-opposition normal form;
all compatibility identities are proved on the actual matrix carrier. -/
theorem standard_opposition_factorization (α : MulAut PSL(3,F)) (hα : α ∈ standard F) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      α = linearConj F m * fieldAction F σ ∨
      α = linearConj F m * fieldAction F σ * OuterSolvable.OddPrimeCoverage.oppositionGraph F :=
  NormalizerForm.standard_opposition_factorization F field_linearConj
    (fun m => ⟨inverseTransposeGL m, graph_linearConj m⟩) field_commute_graph α hα

/-- A standard two-power actor preserving U and fixing the residual axes is
inner-diagonal. The remaining linear two-part is a separate group calculation. -/
theorem standard_fixer_is_linear [Finite F] [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F)
    (hstable : (unipotent F).map α.toMonoidHom = unipotent F)
    (hpow : α ^ (2 ^ k) = 1)
    (hfix : ∀ u ∈ pResidual 3 Fˣ,
      α (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈ unipotent F) :
    α ∈ innerDiagonal F := by
  obtain ⟨m,σ,he | he⟩ := standard_opposition_factorization α hα
  · have hs := linear_field_coefficient_eq_one hF hn2 hn6 m σ
      (by rwa [← he]) (by rwa [← he]) (by rwa [← he])
    exact ⟨m, by simpa only [hs, map_one, mul_one] using he.symm⟩
  · exact False.elim (linear_graph_field_not_fixed hF hn hn2 m σ
      (by rwa [← he]) (by rwa [← he]))

end Matrix.PSL3.CartanActions.ResidualLinear
