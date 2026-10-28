module
public import Theory.LinearAlgebra.CubicSingerCentralizer
/-!
# Conjugacy of nonsplit scalar-cube matrices

Two ternary matrices with the same irreducible cubic annihilator are
multiplication by the same root on a cubic field, in possibly different
coordinates. A field-coordinate change conjugates them. Surjectivity of the
finite-field norm supplies a commuting determinant correction, so the
conjugator can be chosen in SL₃ over the original field.

Source: the Singer-orbit argument in Aschbacher–Smith A.3.18, printed p.53.
-/

public noncomputable section
open Matrix Polynomial
open scoped MatrixGroups
namespace Matrix.CubicSinger
variable {F : Type*} [Field F]

private theorem end_cube (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) :
    (Matrix.toLin' g.val)^3=algebraMap F _ z := by
  change (Matrix.toLinAlgEquiv' g.val)^3 = _
  rw [←map_pow,hc]
  rw [show Matrix.scalar (Fin 3) z = algebraMap F _ z by rfl]
  exact (Matrix.toLinAlgEquiv' (R := F)).commutes z

private theorem coordinates (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) (hn : ∀ a : F, a^3≠z) :
    ∃ e : AdjoinRoot (polynomial z) ≃ₗ[F] (Fin 3 → F),
      ∀ b, Matrix.toLin' g.val (e b)=e (AdjoinRoot.root (polynomial z)*b) := by
  let f := Matrix.toLin' g.val
  have hf := end_cube g z hc
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin 3 → F)
  let e := LinearEquiv.ofBijective (evaluation (action f z hf) v)
    (action_evaluation_bijective f z hf hn (by simp) v hv)
  refine ⟨e,?_⟩
  intro b
  change (f*action f z hf b) v=action f z hf (AdjoinRoot.root (polynomial z)*b) v
  rw [map_mul,action_root]

/-- Matrices with the same nonsplit scalar cube are conjugate over the
original coefficient field. -/
theorem conjugate_of_same_cube (g h : GL (Fin 3) F) (z : F)
    (hg : g.val^3=Matrix.scalar (Fin 3) z) (hh : h.val^3=Matrix.scalar (Fin 3) z)
    (hn : ∀ a : F, a^3≠z) : ∃ P : GL (Fin 3) F, P*g*P⁻¹=h := by
  obtain ⟨eg,heg⟩ := coordinates g z hg hn
  obtain ⟨eh,heh⟩ := coordinates h z hh hn
  let e := eg.symm.trans eh
  let P : GL (Fin 3) F := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hP : Matrix.toLin' P.val=e.toLinearMap := by
    have he := congrArg Units.val (GeneralLinearGroup.toLin.apply_symm_apply
      (LinearMap.GeneralLinearGroup.ofLinearEquiv e))
    exact he
  refine ⟨P,mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply Units.ext
  apply Matrix.toLinAlgEquiv'.injective
  change Matrix.toLinAlgEquiv' (P.val*g.val)=Matrix.toLinAlgEquiv' (h.val*P.val)
  rw [map_mul,map_mul]
  change Matrix.toLin' P.val*Matrix.toLin' g.val=Matrix.toLin' h.val*Matrix.toLin' P.val
  rw [hP]
  apply LinearMap.ext
  intro v
  obtain ⟨b,rfl⟩ := eg.surjective v
  change eh (eg.symm (Matrix.toLin' g.val (eg b))) =
    Matrix.toLin' h.val (eh (eg.symm (eg b)))
  rw [heg,eg.symm_apply_apply,eg.symm_apply_apply,heh]

/-- The centralizer of a nonsplit cubic has every prescribed nonzero
determinant, by surjectivity of the cubic field norm. -/
theorem exists_commuting_det [Finite F] (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) (hn : ∀ a : F, a^3≠z) (d : Fˣ) :
    ∃ c : GL (Fin 3) F, Commute c g ∧ GeneralLinearGroup.det c=d := by
  let E := AdjoinRoot (polynomial z)
  let : Fact (Irreducible (polynomial z)) := ⟨irreducible_polynomial z hn⟩
  let : Field E := inferInstance
  have hdE : Module.finrank F E=3 := cubic_finrank z
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let : Finite E := (Module.finite_iff_finite (R := F) (M := E)).mp inferInstance
  let f := Matrix.toLin' g.val
  have hf := end_cube g z hc
  let φ : E →ₐ[F] Matrix (Fin 3) (Fin 3) F :=
    Matrix.toLinAlgEquiv'.symm.toAlgHom.comp (action f z hf)
  have hφlin (b : E) : Matrix.toLinAlgEquiv' (φ b)=action f z hf b := by
    simp only [φ,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  have hroot : φ (AdjoinRoot.root (polynomial z))=g.val := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [hφlin]
    exact action_root f z hf
  obtain ⟨u,hu⟩ := FiniteField.unitsMap_norm_surjective F E d
  let c : GL (Fin 3) F := Units.map φ.toMonoidHom u
  refine ⟨c,?_,?_⟩
  · apply Units.ext
    change φ (u:E)*g.val=g.val*φ (u:E)
    rw [←hroot,←map_mul,←map_mul,mul_comm]
  · apply Units.ext
    change (φ (u:E)).det=(d:F)
    rw [←LinearMap.det_toLin']
    change LinearMap.det (Matrix.toLinAlgEquiv' (φ (u:E)))=(d:F)
    rw [hφlin,action_det f z hf hn (by simp)]
    exact congrArg Units.val hu

/-- The same-cube conjugator can be chosen in SL₃. -/
theorem special_conjugate_of_same_cube [Finite F] (g h : GL (Fin 3) F) (z : F)
    (hg : g.val^3=Matrix.scalar (Fin 3) z) (hh : h.val^3=Matrix.scalar (Fin 3) z)
    (hn : ∀ a : F, a^3≠z) :
    ∃ P : SL(3,F), SpecialLinearGroup.toGL P*g*(SpecialLinearGroup.toGL P)⁻¹=h := by
  obtain ⟨Q,hQ⟩ := conjugate_of_same_cube g h z hg hh hn
  obtain ⟨c,hc,hd⟩ := exists_commuting_det g z hg hn (GeneralLinearGroup.det Q)⁻¹
  have hdet : (Q*c).val.det=1 := by
    have hh : GeneralLinearGroup.det (Q*c)=1 := by rw [map_mul,hd,mul_inv_cancel]
    exact congrArg Units.val hh
  let P : SL(3,F) := ⟨(Q*c).val,hdet⟩
  have hP : SpecialLinearGroup.toGL P=Q*c := Units.ext rfl
  refine ⟨P,?_⟩
  rw [hP]
  calc
    Q*c*g*(Q*c)⁻¹ = Q*(c*g)*c⁻¹*Q⁻¹ := by group
    _ = Q*(g*c)*c⁻¹*Q⁻¹ := by rw [hc.eq]
    _ = Q*g*Q⁻¹ := by group
    _ = h := hQ
end Matrix.CubicSinger
