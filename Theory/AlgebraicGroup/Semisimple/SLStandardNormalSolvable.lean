module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_6

/-!
Production helper module for `ag-sl-standard-normal-solvable-bot`.

The proof realizes the standard `SL` action as a rational representation using
matrix-entry and adjugate polynomial functions. Lie--Kolchin gives an eigenline
for the connected solvable subgroup. Normality and transitivity on projective
space make every subgroup element act trivially there, hence place the subgroup
in the scalar center. The roots-of-unity description makes that center finite,
and a connected finite closed subgroup is trivial.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

public theorem sl_standard_connected_normal_solvable_eq_bot
    {k : Type u} [Field k] [IsAlgClosed k] (m : ℕ)
    (R : ClosedSubgroup (slVarietyOf k (Fin (m + 1) → k)))
    (hRnormal : R.toSubgroup.Normal)
    (hRconnected : _root_.IsConnected
      (R : Set (Variety.Point (slVarietyOf k (Fin (m + 1) → k)))))
    (hRsolvable : Group.IsSolvable (Variety.Point R.carrierVariety)) :
    R.toSubgroup = ⊥ := by
  classical
  simp only [slVarietyOf] at R hRnormal hRconnected hRsolvable ⊢
  letI : AlgebraicGroup
      (slVariety k (Module.finrank k (Fin (m + 1) → k))) :=
    slAlgebraicGroup k (Module.finrank k (Fin (m + 1) → k))
  let n := Module.finrank k (Fin (m + 1) → k)
  let W := Fin n → k
  let idx : Fin n ≃ Fin (Module.finrank k W) :=
    finCongr (Module.finrank_fin_fun k).symm
  let b : Module.Basis (Fin (Module.finrank k W)) k W :=
    (Pi.basisFun k (Fin n)).reindex idx
  let action : Variety.Point (slVariety k n) →*
      LinearMap.GeneralLinearGroup k W :=
    SpecialLinearGroup.toGeneralLinearGroup.comp
      (Matrix.SpecialLinearGroup.toLin'_equiv.toMonoidHom.comp
        (slPointMulEquiv n).toMonoidHom)
  let ρ : RationalRepresentation (slVariety k n) W := ⟨action⟩
  let matrixCoefficient : Fin (Module.finrank k W) →
      Fin (Module.finrank k W) →
      (slVariety k n).PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.ofPolynomial _
      (MvPolynomial.X (ULift.up (idx.symm i, idx.symm j)))
  let inverseMatrixCoefficient : Fin (Module.finrank k W) →
      Fin (Module.finrank k W) →
      (slVariety k n).PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.ofPolynomial _
      (slInvPoly n (ULift.up (idx.symm i, idx.symm j)))
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        b.repr ((action g : Module.End k W) (b j)) i := by
    intro i j g
    dsimp [matrixCoefficient, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun]
    rw [evalPolynomial_X]
    dsimp [b, action]
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
      Pi.basisFun_repr]
    simp only [SpecialLinearGroup.coe_toGeneralLinearGroup_apply,
      Pi.basisFun_apply]
    rw [show SpecialLinearGroup.toLinearEquiv
        (Matrix.SpecialLinearGroup.toLin'_equiv ((slPointMulEquiv n) g)) =
        Matrix.SpecialLinearGroup.toLin' ((slPointMulEquiv n) g) by rfl]
    change g.val (ULift.up (idx.symm i, idx.symm j)) =
      Matrix.toLin' (↑((slPointMulEquiv n) g) : Matrix (Fin n) (Fin n) k)
        (Pi.single (idx.symm j) 1) (idx.symm i)
    simp [slPointMulEquiv_apply]
    rfl
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        b.repr ((((action g)⁻¹ : LinearMap.GeneralLinearGroup k W) :
          Module.End k W) (b j)) i := by
    intro i j g
    dsimp [inverseMatrixCoefficient, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun]
    dsimp [b, action]
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
      Pi.basisFun_repr]
    rw [← map_inv]
    simp only [SpecialLinearGroup.coe_toGeneralLinearGroup_apply,
      Pi.basisFun_apply]
    change evalPolynomial g.val
      (slInvPoly n (ULift.up (idx.symm i, idx.symm j))) = _
    rw [slInvPoly, evalPolynomial_slAdjugate]
    rw [show (Matrix.SpecialLinearGroup.toLin'_equiv
        ((slPointMulEquiv n) g))⁻¹ =
        Matrix.SpecialLinearGroup.toLin'_equiv
          (((slPointMulEquiv n) g)⁻¹) by simp]
    rw [show SpecialLinearGroup.toLinearEquiv
        (Matrix.SpecialLinearGroup.toLin'_equiv
          (((slPointMulEquiv n) g)⁻¹)) =
        Matrix.SpecialLinearGroup.toLin' (((slPointMulEquiv n) g)⁻¹) by rfl]
    have hval : (fun i' j' : Fin n => g.val (ULift.up (i', j'))) =
        (slPointEquiv n g).1 := rfl
    rw [hval]
    change Matrix.adjugate (slPointEquiv n g).1 (idx.symm i) (idx.symm j) =
      Matrix.toLin'
        (↑(((slPointMulEquiv n) g)⁻¹) : Matrix (Fin n) (Fin n) k)
        (Pi.single (idx.symm j) 1) (idx.symm i)
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [slPointMulEquiv_apply]
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b action matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  have hρ : IsRationalRepresentation ρ := by
    refine ⟨b, ?_, ?_⟩
    · simpa [glVarietyOf, W] using f
    · intro g
      change glPointEquivOf k W b (f.onPoints g) = action g
      exact glPointEquivOf_generalLinearRepresentationPoint b (action g)
  have hn : 0 < n := by
    simp [n]
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Inhabited (Fin n) := ⟨Classical.choice inferInstance⟩
  letI : Nontrivial W := Pi.nontrivial
  letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  have hRcarrierConnected : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    letI : ConnectedSpace
        {x : Variety.Point
          (slVariety k (Module.finrank k (Fin (m + 1) → k))) //
          x ∈ R.toSubgroup} :=
      Subtype.connectedSpace hRconnected
    letI : ConnectedSpace (Variety.Point R.carrierVariety) :=
      e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  obtain ⟨τ, hτρ, hτ⟩ :=
    rationalRepresentation_pullback_exists R.inclusion ρ hρ
  obtain ⟨χ, v, hv, heigen⟩ :=
    τ.exists_common_eigenvector_of_isSolvable_isConnected_public
      hτ hRsolvable hRcarrierConnected
  let D : Projectivization k W := Projectivization.mk k v hv
  have hfixD (y : Variety.Point R.carrierVariety) :
      (slPointMulEquiv n (R.inclusion.onPoints y)) • D = D := by
    rw [Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ hv).2
    refine ⟨χ y, ?_⟩
    have hy := heigen y
    rw [hτρ y] at hy
    change (action (R.inclusion.onPoints y) : Module.End k W) v = χ y • v at hy
    change (SpecialLinearGroup.toGeneralLinearGroup
      (Matrix.SpecialLinearGroup.toLin'_equiv
        (slPointMulEquiv n (R.inclusion.onPoints y)))).1 v = χ y • v at hy
    rw [SpecialLinearGroup.coe_toGeneralLinearGroup_apply] at hy
    change Matrix.SpecialLinearGroup.toLin'
      (slPointMulEquiv n (R.inclusion.onPoints y)) v = χ y • v at hy
    rw [Matrix.SpecialLinearGroup.toLin'_apply] at hy
    change (slPointMulEquiv n (R.inclusion.onPoints y)) • v = χ y • v at hy
    change χ y • v =
      (slPointMulEquiv n (R.inclusion.onPoints y)) • v
    exact hy.symm
  have hRcenter : ∀ x, x ∈ R.toSubgroup →
      slPointMulEquiv n x ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) := by
    intro x hx
    let A := slPointMulEquiv n x
    have hfixAll (E : Projectivization k W) : A • E = E := by
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
        (Matrix.SpecialLinearGroup (Fin n) k) D E
      let g0 : Variety.Point
          (slVariety k (Module.finrank k (Fin (m + 1) → k))) :=
        (slPointMulEquiv n).symm g
      have hconjmem : g0⁻¹ * x * g0 ∈ R.toSubgroup := by
        simpa using hRnormal.conj_mem x hx g0⁻¹
      let y : Variety.Point R.carrierVariety :=
        R.pointEquiv.symm ⟨g0⁻¹ * x * g0, hconjmem⟩
      have hyval : R.inclusion.onPoints y = g0⁻¹ * x * g0 := by
        change (R.pointEquiv y).val = g0⁻¹ * x * g0
        rw [R.pointEquiv.apply_symm_apply]
      have hyMatrix : slPointMulEquiv n (R.inclusion.onPoints y) =
          g⁻¹ * A * g := by
        rw [hyval]
        rw [map_mul, map_mul, map_inv]
        change (slPointMulEquiv n g0)⁻¹ * slPointMulEquiv n x *
          slPointMulEquiv n g0 = g⁻¹ * A * g
        rw [show slPointMulEquiv n g0 = g by
          dsimp [g0]
          exact (slPointMulEquiv n).apply_symm_apply g]
      have hyfix := hfixD y
      rw [hyMatrix] at hyfix
      rw [← hg]
      calc
        A • (g • D) = (A * g) • D := (mul_smul A g D).symm
        _ = (g * (g⁻¹ * A * g)) • D := by
          congr 1
          group
        _ = g • ((g⁻¹ * A * g) • D) := mul_smul _ _ _
        _ = g • D := by rw [hyfix]
    have hker : A ∈
        (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin n) k)
          (Projectivization k W)).ker := by
      rw [MonoidHom.mem_ker]
      ext E
      exact hfixAll E
    rw [Projectivization.SL_mulAction_ker] at hker
    exact hker
  let toCenter : R.toSubgroup →
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) := fun x =>
    ⟨slPointMulEquiv n x.1, hRcenter x.1 x.2⟩
  have toCenter_injective : Function.Injective toCenter := by
    intro x y hxy
    apply Subtype.ext
    apply (slPointMulEquiv n).injective
    exact congrArg Subtype.val hxy
  letI : NeZero (max (Fintype.card (Fin n)) 1) := ⟨by omega⟩
  letI : Finite (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k)) :=
    (Equiv.finite_iff
      Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv).mpr
        inferInstance
  letI : Finite R.toSubgroup :=
    Finite.of_injective toCenter toCenter_injective
  have hRfiniteSet :
      (R.toSubgroup : Set (Variety.Point
        (slVariety k (Module.finrank k (Fin (m + 1) → k))))).Finite :=
    Set.toFinite _
  let hT1 : T1Space
      (Variety.Point
        (slVariety k (Module.finrank k (Fin (m + 1) → k)))) :=
    ⟨fun x => Variety.isClosed_iff_isZariskiClosed.mpr
      (isZariskiClosed_singleton
        (slVariety k (Module.finrank k (Fin (m + 1) → k))) x)⟩
  have hRsubsingleton :
      (R.toSubgroup : Set (Variety.Point
        (slVariety k (Module.finrank k (Fin (m + 1) → k))))).Subsingleton := by
    rw [← Set.not_nontrivial_iff]
    intro hnontrivial
    exact hRfiniteSet.not_infinite
      (@IsPreconnected.infinite_of_nontrivial
        (Variety.Point
          (slVariety k (Module.finrank k (Fin (m + 1) → k))))
        inferInstance hT1 _ hRconnected.isPreconnected hnontrivial)
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_bot.mpr (hRsubsingleton hx R.toSubgroup.one_mem)
  · intro hx
    change x = 1 at hx
    subst x
    exact R.toSubgroup.one_mem

end Theory.AlgebraicGroup
