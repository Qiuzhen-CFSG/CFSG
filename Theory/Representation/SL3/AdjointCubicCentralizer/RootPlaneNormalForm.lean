module
public import Theory.SpecificGroups.PSL3.RootPlaneCubic
public import Theory.Representation.SL3.AdjointCubicCentralizer.OuterCubicFixed
public import Theory.LinearAlgebra.SplitSeparableEigenbasis
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The split normal form for root-plane-preserving outer cubics

The root-plane lift supplies a cube root of the scalar cube. A split separable
annihilator then gives an eigenbasis. Over the four-element field, three distinct
eigenvalues enumerate all units and have product one; the outer condition rules
out that determinant. Two eigenvalues therefore coincide, and permutation and
scalar normalization give the literal projective form `diag(ω,1,1)`.

The final theorem transports the ordinary adjoint action and gives its 256 fixed
points without assuming a diagonal marker or a conjugating matrix.
Source: Aschbacher--Smith B.4.14, printed p.98, with the cubic parabolic
calculation and the scalar-cube argument of A.3.18, printed pp.52--53.
-/

public noncomputable section
open Matrix Subgroup Polynomial
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Representation.SL3.AdjointCubicCentralizer.RootPlaneNormalForm
variable (F : Type*) [Field F]

private theorem permute_diagonal (P : GL (Fin 3) F) (d : Fin 3 → F)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ Q : GL (Fin 3) F, Q.val * Matrix.diagonal (fun i => d (σ i)) * Q⁻¹.val =
      P.val * Matrix.diagonal d * P⁻¹.val := by
  classical
  let R : GL (Fin 3) F := (Matrix.permMatrixHom (n := Fin 3) (R := F)).toHomUnits σ
  have hR (i j : Fin 3) : R.val i j = if i = σ j then 1 else 0 := by
    change ((σ⁻¹).permMatrix F) i j = _
    simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
      Equiv.Perm.inv_def,Equiv.symm_apply_eq]
  have he : R.val * Matrix.diagonal (fun i => d (σ i)) = Matrix.diagonal d * R.val := by
    ext i j
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,hR]
    split_ifs with h
    · simp [h]
    · simp
  refine ⟨P*R,?_⟩
  change (P.val*R.val)*Matrix.diagonal (fun i => d (σ i))*(R⁻¹.val*P⁻¹.val)=_
  rw [mul_assoc P.val,he]
  simp only [←mul_assoc,Units.mul_inv_cancel_right]

private theorem det_ne_one_of_outer (g : GL (Fin 3) F)
    (hout : linearConj F g ∉ MulAut.innerSubgroup PSL(3,F)) : Matrix.det g.val ≠ 1 := by
  intro hd
  let s : SL(3,F) := ⟨g.val,hd⟩
  have hs : SpecialLinearGroup.toGL s = g := Units.ext rfl
  apply hout
  rw [←hs,linearConj_toGL]
  exact ⟨Matrix.PSL3.projection F s,rfl⟩

variable [Finite F]

private theorem split_eigenbasis (hF : Nat.card F = 4)
    (g : GL (Fin 3) F) (z : Fˣ)
    (hc : g^3=GeneralLinearGroup.scalar (Fin 3) z) (a : F) (ha : a^3=(z:F)) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      P.val*Matrix.diagonal d*P⁻¹.val=g.val := by
  classical
  obtain ⟨w,hw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hw3 : orderOf w = 3 := by simpa [Nat.card_units,hF] using hw
  have hpw : IsPrimitiveRoot (w : F) 3 := IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_injective (Units.coeHom F) Units.val_injective w).trans hw3)
  have ha0 : a≠0 := by intro h; apply z.ne_zero; rw [←ha,h]; simp
  let p : F[X] := X^3-C (z:F)
  have hs : p.Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hpw ha
  have hp : p.Separable := by
    rw [show p = ∏ i ∈ Finset.range 3, (X-C ((w:F)^i*a)) from
      X_pow_sub_C_eq_prod hpw (by decide) ha]
    apply separable_prod_X_sub_C_iff'.mpr
    intro i hi j hj he
    exact hpw.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ ha0 he)
  let f := Matrix.toLin' g.val
  have heval : aeval f p = 0 := by
    have he : aeval g.val p = 0 := by
      simp only [p,map_sub,map_pow,aeval_X,aeval_C]
      rw [show g.val^3=Matrix.scalar (Fin 3) (z:F) from congrArg Units.val hc]
      simp [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply]
    change aeval (Matrix.toLinAlgEquiv' (R := F) g.val) p = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨b,μ,hb⟩ := Module.End.exists_eigenbasis_of_split_separable_annihilator f p
    (monic_X_pow_sub_C _ (by decide)) hs hp heval
  have hdim : Module.finrank F (Fin 3 → F)=3 := by simp
  let b' := b.reindex (finCongr hdim)
  let d : Fin 3 → F := fun i => μ ((finCongr hdim).symm i)
  have hd : LinearMap.toMatrix b' b' f = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb]
    · simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb,hij]
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F := ⟨s.toMatrix b',b'.toMatrix s,
    s.toMatrix_mul_toMatrix_flip b',b'.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P,d,?_⟩
  change s.toMatrix b' * Matrix.diagonal d * b'.toMatrix s = g.val
  rw [←hd,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s,f,LinearMap.toMatrix_eq_toMatrix']

variable [CharP F 2]

private theorem repeated_of_det_ne_one (hF : Nat.card F = 4) (d : Fin 3 → F)
    (hd : ∀ i, d i ≠ 0) (hdet : (∏ i, d i) ≠ 1) :
    d 0 = d 1 ∨ d 0 = d 2 ∨ d 1 = d 2 := by
  classical
  by_contra! hh
  let f : Fin 3 → Fˣ := fun i => Units.mk0 (d i) (hd i)
  have hi : Function.Injective f := by
    intro i j he
    have he' : d i = d j := congrArg Units.val he
    fin_cases i <;> fin_cases j <;> simp_all
  let := Fintype.ofFinite F
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hi, by simp [← Nat.card_eq_fintype_card, Nat.card_fin, Nat.card_units, hF]⟩
  have hp : (∏ i, f i) = (-1 : Fˣ) :=
    (Fintype.prod_bijective f hb f id (fun _ => rfl)).trans
      FiniteField.prod_univ_units_id_eq_neg_one
  apply hdet
  have hp' := congrArg Units.val hp
  simpa [f,CharTwo.neg_eq] using hp'

/-- Over the four-element field, a split outer cubic has two equal
eigenvalues and hence the marked projective diagonal normal form. -/
theorem diagonal_conjugacy_of_split (hF : Nat.card F = 4)
    (g : GL (Fin 3) F) (z : Fˣ)
    (hc : g^3 = GeneralLinearGroup.scalar (Fin 3) z) (a : F) (ha : a^3=(z:F))
    (hout : linearConj F g ∉ MulAut.innerSubgroup PSL(3,F)) :
    ∃ (P : GL (Fin 3) F) (ω : Fˣ),
      ProjGenLinGroup.mk P * ProjGenLinGroup.mk g * (ProjGenLinGroup.mk P)⁻¹ =
        ProjGenLinGroup.mk (diagonalUnit F ω) := by
  classical
  obtain ⟨P,d,hP⟩ := split_eigenbasis F hF g z hc a ha
  have hdet : Matrix.det (Matrix.diagonal d) = Matrix.det g.val := by
    rw [←hP,Matrix.det_mul,Matrix.det_mul]
    have hi : P.val * P⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel P)
    have hp : Matrix.det P.val * Matrix.det P⁻¹.val = 1 := by
      simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det hi
    symm
    calc
      _ = (Matrix.det P.val * Matrix.det P⁻¹.val) * Matrix.det (Matrix.diagonal d) := by ring
      _ = _ := by rw [hp,one_mul]
  have hn : ∀ i, d i ≠ 0 := by
    have hh := (GeneralLinearGroup.det g).ne_zero
    change Matrix.det g.val ≠ 0 at hh
    rw [←hdet,Matrix.det_diagonal] at hh
    exact fun i => Finset.prod_ne_zero_iff.mp hh i (Finset.mem_univ i)
  have hr := repeated_of_det_ne_one F hF d hn (by
    rw [←Matrix.det_diagonal,hdet]
    exact det_ne_one_of_outer F g hout)
  have hchoose : ∃ (Q : GL (Fin 3) F) (e : Fin 3 → F),
      e 1=e 2 ∧ (∀ i, e i ≠ 0) ∧ Q.val*Matrix.diagonal e*Q⁻¹.val=g.val := by
    rcases hr with h01 | h02 | h12
    · obtain ⟨Q,hQ⟩ := permute_diagonal F P d (Equiv.swap 0 2)
      exact ⟨Q,fun i => d (Equiv.swap 0 2 i),by change d 1 = d 0; exact h01.symm,
        fun i => hn _,hQ.trans hP⟩
    · obtain ⟨Q,hQ⟩ := permute_diagonal F P d (Equiv.swap 0 1)
      exact ⟨Q,fun i => d (Equiv.swap 0 1 i),by change d 0 = d 2; exact h02,
        fun i => hn _,hQ.trans hP⟩
    · exact ⟨P,d,h12,hn,hP⟩
  obtain ⟨Q,e,h12,he,hQ⟩ := hchoose
  let u : Fˣ := Units.mk0 (e 1) (he 1)
  let ω : Fˣ := Units.mk0 (e 0) (he 0) * u⁻¹
  have hm : Q⁻¹ * g * Q = GeneralLinearGroup.scalar (Fin 3) u * diagonalUnit F ω := by
    apply Units.ext
    change Q⁻¹.val*g.val*Q.val = Matrix.scalar (Fin 3) (u:F) * (diagonalUnit F ω).val
    rw [←hQ]
    simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalUnit,block,Matrix.scalar,Matrix.diagonal_mul,u,ω,h12,he,
        mul_comm,mul_left_comm]
  refine ⟨Q⁻¹,ω,?_⟩
  rw [←map_inv,←map_mul,←map_mul,inv_inv,hm,map_mul,ProjGenLinGroup.mk_scalar,one_mul]

/-- Every root-plane-preserving outer projective cubic over the four-element
field has the marked diagonal normal form. No conjugacy witness is an input. -/
theorem diagonal_conjugacy (hF : Nat.card F = 4)
    (actor : ProjGenLinGroup (Fin 3) F) (b : Bool) (hc : actor ^ 3 = 1)
    (hout : (pglEquivInnerDiagonal F actor).val ∉ MulAut.innerSubgroup PSL(3,F))
    (hroot : (Matrix.PSL3.RootPlaneGeometry.rootPlane F b).map
      (pglEquivInnerDiagonal F actor).val.toMonoidHom =
      Matrix.PSL3.RootPlaneGeometry.rootPlane F b) :
    ∃ (P : GL (Fin 3) F) (ω : Fˣ),
      ProjGenLinGroup.mk P * actor * (ProjGenLinGroup.mk P)⁻¹ =
        ProjGenLinGroup.mk (diagonalUnit F ω) := by
  obtain ⟨g,z,a,hg,hc',ha⟩ :=
    Matrix.PSL3.RootPlaneCubic.projective_cube_has_root F actor b hc hroot
  subst actor
  exact diagonal_conjugacy_of_split F hF g z hc' a ha hout

/-- The diagonal fixed-space bound now follows from the literal projective
cube, outer condition and root-plane preservation. -/
theorem fixed_card_ge_of_rootPlane {A M : Type*} [Group A] [Group M] [Finite M]
    [MulDistribMulAction A M] (hF : Nat.card F = 4)
    (actor : ProjGenLinGroup (Fin 3) F) (b : Bool) (hc : actor ^ 3 = 1)
    (hout : (pglEquivInnerDiagonal F actor).val ∉ MulAut.innerSubgroup PSL(3,F))
    (hroot : (Matrix.PSL3.RootPlaneGeometry.rootPlane F b).map
      (pglEquivInnerDiagonal F actor).val.toMonoidHom =
      Matrix.PSL3.RootPlaneGeometry.rootPlane F b)
    (a : A) (hgen : zpowers a = ⊤) (e : M ≃ TraceZero F)
    (he : ∀ v, e (a • v) = projectiveAdjoint F actor (e v)) :
    256 ≤ Nat.card (FixedPoints.subgroup A M) := by
  obtain ⟨P,ω,hP⟩ := diagonal_conjugacy F hF actor b hc hout hroot
  let model : OuterCubicFixedModel F :=
    { actor := actor
      rootSide := b
      actor_cube := hc
      outer := hout
      rootPlane_preserved := hroot
      diagonal := ω
      conjugator := P
      conjugacy := hP }
  exact OuterCubicFixedModel.fixed_card_ge F model hF a hgen e he

end Representation.SL3.AdjointCubicCentralizer.RootPlaneNormalForm
