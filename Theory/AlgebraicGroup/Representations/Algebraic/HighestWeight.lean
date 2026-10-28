module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces

universe u v w

set_option linter.style.haveILetI false

/-! Root-data realizations and high-weight vectors. -/

namespace Theory.AlgebraicGroup

@[expose]
public def IsDominantWeight
    {k : Type u} [Field k]
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (D : RootGroupData G T) (weight : TorusWeight T) : Prop :=
  ∀ α ∈ D.simple, 0 ≤ D.weightPairing weight α

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def RepIsRootDatumRealization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (e : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T) : Prop :=
  ∀ α, weightEquiv (Multiplicative.ofAdd (P.root (e α))) = D.rootWeight α

@[expose]
public def IsBasedRootDatumRealization
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (base : P.Base)
    (rootEquiv : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T) : Prop :=
  RepIsRootDatumRealization D P rootEquiv weightEquiv ∧
    rootEquiv '' D.simple = (base.support : Set ι) ∧
    ∀ weight root,
      P.toLinearMap weight (P.coroot (rootEquiv root)) =
        D.weightPairing (weightEquiv (Multiplicative.ofAdd weight)) root

@[expose]
public def IsFundamentalWeightFamily
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (base : P.Base)
    (fundamentalWeight : base.support → X) : Prop := by
  classical
  exact ∀ i j : base.support,
    P.toLinearMap (fundamentalWeight i) (P.coroot j) = if i = j then 1 else 0

@[expose]
public noncomputable def fundamentalTorusWeight
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {P : RootPairing ι ℤ X Y} {base : P.Base}
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (fundamentalWeight : base.support → X) (i : base.support) : TorusWeight T :=
  weightEquiv (Multiplicative.ofAdd (fundamentalWeight i))

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def GeneratesInvariantLine
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (H : ClosedSubgroup K) (v : V) : Prop :=
  v ≠ 0 ∧ ∀ h, h ∈ H → ∃ c : k, (ρ.action h).1 v = c • v

@[expose]
public def IsHighWeightVectorForB
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (B : ClosedSubgroup K) (v : V) : Prop :=
  GeneratesInvariantLine ρ B v

@[expose]
public def HasHighWeight
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (B T : ClosedSubgroup K)
    (v : V) (χ : TorusWeight T) : Prop :=
  IsHighWeightVectorForB ρ B v ∧ IsWeightVector ρ T v χ

end

section

@[expose]
public def rootLattice
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) : AddSubgroup X :=
  AddSubgroup.closure (Set.range P.root)

@[expose]
public def cartanMap
    {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing ι ℤ X Y) (base : P.Base) :
    (base.support → ℤ) →+ (base.support → ℤ) :=
  AddMonoidHom.mk'
    (fun c i => ∑ j, c j * P.pairing j i)
    (by intro c d; ext i; simp [add_mul, Finset.sum_add_distrib])

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable def simpleCorootCoordinateEquiv
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) : X ≃ₗ[ℤ] (base.support → ℤ) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact P.toPerfPair ≪≫ₗ base.toCoweightBasis.dualBasis.equivFun

lemma simpleCorootCoordinateEquiv_apply
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (weight : X) (j : base.support) :
    simpleCorootCoordinateEquiv P base weight j =
      P.toLinearMap weight (P.coroot j) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  simp [simpleCorootCoordinateEquiv]

noncomputable def fundamentalWeight
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (i : base.support) : X := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact (simpleCorootCoordinateEquiv P base).symm (Pi.single i 1)

lemma fundamentalWeight_pairing
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) :
    IsFundamentalWeightFamily P base (fundamentalWeight P base) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  intro i j
  rw [← simpleCorootCoordinateEquiv_apply P base]
  simp [fundamentalWeight, Pi.single_apply, eq_comm]

lemma weight_eq_sum_fundamentalWeight
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (weight : X) :
    weight = ∑ j : base.support,
      (P.toLinearMap weight (P.coroot j)) • fundamentalWeight P base j := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  apply (simpleCorootCoordinateEquiv P base).injective
  funext i
  rw [map_sum]
  simp only [map_zsmul, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [simpleCorootCoordinateEquiv_apply, fundamentalWeight]
  · intro j _ hji
    simp [fundamentalWeight, hji]
  · simp

omit [IsAlgClosed k] in
lemma dominantWeight_iff_coordinates_nonnegative
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsRootSystem]
    (base : P.Base) (rootEquiv : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hRealizes : IsBasedRootDatumRealization D P base rootEquiv weightEquiv)
    (weight : X) :
    IsDominantWeight D (weightEquiv (Multiplicative.ofAdd weight)) ↔
      ∀ j : base.support, 0 ≤ P.toLinearMap weight (P.coroot j) := by
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro h j
    let root := rootEquiv.symm j.1
    have hroot : root ∈ D.simple := by
      have hj : j.1 ∈ rootEquiv '' D.simple := by
        rw [hRealizes.2.1]
        exact j.2
      rcases hj with ⟨α, hα, hαj⟩
      have hEq := congrArg rootEquiv.symm hαj
      simp only [Equiv.symm_apply_apply] at hEq
      change rootEquiv.symm j.1 ∈ D.simple
      rw [← hEq]
      exact hα
    have := h root hroot
    rw [← hRealizes.2.2 weight root] at this
    simpa [root] using this
  · intro h α hα
    have hsupp : rootEquiv α ∈ (base.support : Set ι) := by
      rw [← hRealizes.2.1]
      exact ⟨α, hα, rfl⟩
    let j : base.support := ⟨rootEquiv α, hsupp⟩
    rw [← hRealizes.2.2 weight α]
    exact h j

end

section

variable {k : Type u} [Field k]

/-- A fundamental weight transported through a based root-datum realization
is dominant for the corresponding positive system. -/
public theorem fundamentalTorusWeight_isDominant
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T)
    {ι X Y : Type*} [Finite ι]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y)
    (base : P.Base) (rootEquiv : D.Root ≃ ι)
    (weightEquiv : Multiplicative X ≃* TorusWeight T)
    (hRealizes : IsBasedRootDatumRealization D P base rootEquiv weightEquiv)
    (fundamentalWeight : base.support → X)
    (hFundamental : IsFundamentalWeightFamily P base fundamentalWeight)
    (first : base.support) :
    IsDominantWeight D
      (fundamentalTorusWeight weightEquiv fundamentalWeight first) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  intro α hα
  have hsupp : rootEquiv α ∈ base.support := by
    have himage : rootEquiv α ∈ rootEquiv '' D.simple := ⟨α, hα, rfl⟩
    rw [hRealizes.2.1] at himage
    exact himage
  let j : base.support := ⟨rootEquiv α, hsupp⟩
  change 0 ≤ D.weightPairing
    (weightEquiv (Multiplicative.ofAdd (fundamentalWeight first))) α
  rw [← hRealizes.2.2 (fundamentalWeight first) α]
  change 0 ≤ P.toLinearMap (fundamentalWeight first) (P.coroot (rootEquiv α))
  rw [hFundamental first j]
  split <;> norm_num

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def glLinearMatrixCoefficient
    {V : Type v} [AddCommGroup V] [Module k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (φ : Module.Dual k V) (v : V) :
    Variety.PolynomialFunction (glVariety (Module.finrank k V) : Variety k) :=
  ⟨fun x => ∑ i, ∑ j, (φ (e i) * e.repr v j) * x.val (Sum.inl (i, j)), by
    refine ⟨∑ i, ∑ j, MvPolynomial.C (φ (e i)) * MvPolynomial.C (e.repr v j) *
      MvPolynomial.X (Sum.inl (i, j)), ?_⟩
    intro x
    rw [evalPolynomial_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [evalPolynomial_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [evalPolynomial_mul, evalPolynomial_mul, evalPolynomial_X]
    simp [evalPolynomial]⟩

private lemma glLinearMatrixCoefficient_apply
    {V : Type v} [AddCommGroup V] [Module k V]
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (φ : Module.Dual k V) (v : V)
    (x : Variety.Point (glVariety (Module.finrank k V) : Variety k)) :
    glLinearMatrixCoefficient e φ v x = φ ((glPointEquivOf k V e x).1 v) := by
  have hcoord (i j : Fin (Module.finrank k V)) :
      x.val (Sum.inl (i, j)) = e.repr ((glPointEquivOf k V e x).1 (e j)) i := by
    rw [show glPointEquivOf k V e x =
        Matrix.GeneralLinearGroup.toLin' e (glPointEquiv (Module.finrank k V) x) by rfl]
    change x.val (Sum.inl (i, j)) = e.repr
      ((Matrix.GeneralLinearGroup.toLin' e
        (glPointEquiv (Module.finrank k V) x)).toLinearEquiv (e j)) i
    rw [Matrix.GeneralLinearGroup.toLin'_apply]
    simp [Fintype.linearCombination_apply, Matrix.mulVec, glPointEquiv,
      glMatrixOfPoint, dotProduct, Finsupp.single_apply]
  have hmatrix : LinearMap.toMatrix e e
      ((glPointEquivOf k V e x).1 : V →ₗ[k] V) =
      fun i j => x.val (Sum.inl (i, j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    exact (hcoord i j).symm
  change (∑ i, ∑ j, (φ (e i) * e.repr v j) * x.val (Sum.inl (i, j))) = _
  rw [← e.sum_repr ((glPointEquivOf k V e x).1 v), map_sum]
  simp only [map_smul, smul_eq_mul]
  have hrepr := LinearMap.toMatrix_mulVec_repr e e
    ((glPointEquivOf k V e x).1 : V →ₗ[k] V) v
  rw [hmatrix] at hrepr
  have hrepr_i (i : Fin (Module.finrank k V)) := congrFun hrepr i
  simp only [Matrix.mulVec, dotProduct] at hrepr_i
  apply Finset.sum_congr rfl
  intro i _
  calc
    ∑ j, φ (e i) * e.repr v j * x.val (Sum.inl (i, j)) =
        φ (e i) * ∑ j, x.val (Sum.inl (i, j)) * e.repr v j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j, x.val (Sum.inl (i, j)) * e.repr v j) * φ (e i) := by ring
    _ = e.repr ((glPointEquivOf k V e x).1 v) i * φ (e i) := by
      exact congrArg (fun z => z * φ (e i)) (hrepr_i i)

private lemma invariantLine_torusWeight_existsUnique
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (H : ClosedSubgroup K) (v : V) (hv : GeneratesInvariantLine ρ H v) :
    ∃! χ : TorusWeight H, IsWeightVector ρ H v χ := by
  obtain ⟨φ, hφv⟩ := Module.Projective.exists_dual_eq_one k hv.1
  obtain ⟨e, f, hf⟩ := hρ
  let scalarGL := glLinearMatrixCoefficient e φ v
  let representationMorphism : AlgebraicGroup.Morphism H.carrierVariety (glVarietyOf k V) :=
    f.comp H.inclusion
  let scalar : Variety.PolynomialFunction H.carrierVariety :=
    Variety.PolynomialFunction.pullback representationMorphism.toVariety scalarGL
  have scalar_apply (h : Variety.Point H.carrierVariety) :
    scalar h = φ ((ρ.action (H.includePoint h)).1 v) := by
    rw [show scalar h = scalarGL (representationMorphism.onPoints h) by rfl]
    have hgl : scalarGL (representationMorphism.onPoints h) =
        φ ((glPointEquivOf k V e (representationMorphism.onPoints h)).1 v) := by
      simpa [scalarGL, glVarietyOf] using
        (glLinearMatrixCoefficient_apply e φ v (representationMorphism.onPoints h))
    have hrepr : glPointEquivOf k V e (representationMorphism.onPoints h) =
        ρ.action (H.includePoint h) := by
      change glPointEquivOf k V e (f.onPoints (H.includePoint h)) = _
      exact hf _
    rw [hgl, hrepr]
  have action_eq_scalar (h : Variety.Point H.carrierVariety) :
      (ρ.action (H.includePoint h)).1 v = scalar h • v := by
    have hh : H.includePoint h ∈ H := (H.pointEquiv h).property
    obtain ⟨c, hc⟩ := hv.2 (H.includePoint h) hh
    have hscalar : scalar h = c := by
      rw [scalar_apply, hc, map_smul, hφv, smul_eq_mul, mul_one]
    rw [hscalar, hc]
  have scalar_one : scalar (1 : Variety.Point H.carrierVariety) = 1 := by
    rw [scalar_apply]
    change φ ((ρ.action 1).1 v) = 1
    simpa using hφv
  have scalar_mul (g h : Variety.Point H.carrierVariety) :
      scalar (g * h) = scalar g * scalar h := by
    rw [scalar_apply]
    have hinclude : H.includePoint (g * h) = H.includePoint g * H.includePoint h :=
      H.inclusion.onPoints.map_mul g h
    rw [hinclude, map_mul]
    change φ ((ρ.action (H.includePoint g)).1
      ((ρ.action (H.includePoint h)).1 v)) = _
    rw [action_eq_scalar h, map_smul, action_eq_scalar g, smul_smul, map_smul, hφv]
    simp [mul_comm]
  have scalar_mul_inv (h : Variety.Point H.carrierVariety) :
      scalar h * scalar h⁻¹ = 1 := by
    rw [← scalar_mul]
    simpa using scalar_one
  let scalarUnit (h : Variety.Point H.carrierVariety) : kˣ :=
    ⟨scalar h, scalar h⁻¹, scalar_mul_inv h, by
      rw [mul_comm]
      exact scalar_mul_inv h⟩
  let pointMap (h : Variety.Point H.carrierVariety) : Variety.Point (KMult k) :=
    (dPointEquiv 1).symm (fun _ => scalarUnit h)
  have pointMap_entry (h : Variety.Point H.carrierVariety) :
      (dPointEquiv 1 (pointMap h) 0 : k) = scalar h := by rfl
  let character : TorusWeight H := {
    toVariety := {
      toFun := pointMap
      regular := by
        intro c
        cases c with
        | inl i =>
            rcases i with ⟨i⟩
            rcases i with ⟨⟩
            rcases scalar.representedBy with ⟨p, hp⟩
            exact ⟨p, fun h => by
              change scalar h = evalPolynomial h.val p
              exact hp h⟩
        | inr i =>
            rcases i with ⟨i⟩
            rcases i with ⟨⟩
            let scalarInv : Variety.PolynomialFunction H.carrierVariety :=
              Variety.PolynomialFunction.pullback
                (AlgebraicGroup.invMorphism H.carrierVariety) scalar
            rcases scalarInv.representedBy with ⟨p, hp⟩
            exact ⟨p, fun h => by
              change scalar h⁻¹ = evalPolynomial h.val p
              change scalarInv h = evalPolynomial h.val p
              exact hp h⟩ }
    map_one := by
      apply (dPointEquiv 1).injective
      ext i
      fin_cases i
      change scalar 1 = 1
      exact scalar_one
    map_mul := by
      intro g h
      apply (dPointEquiv 1).injective
      ext i
      fin_cases i
      change scalar (g * h) = scalar g * scalar h
      exact scalar_mul g h }
  refine ⟨character, ?_, ?_⟩
  · exact ⟨hv.1, fun h => by
      rw [action_eq_scalar]
      change scalar h • v = (dPointEquiv 1 (pointMap h) 0 : k) • v
      rw [pointMap_entry]⟩
  · intro χ hχ
    apply TorusCharacter.pointCharacter_injective
    ext h
    have hvχ := hχ.2 h
    rw [action_eq_scalar h] at hvχ
    have hs : scalar h = χ.pointCharacter h :=
      smul_left_injective k hv.1 hvχ
    change χ.pointCharacter h = (dPointEquiv 1 (pointMap h) 0 : k)
    rw [pointMap_entry]
    exact hs.symm

public theorem invariantLine_torusWeight_existsUnique_public
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (H : ClosedSubgroup K) (v : V) (hv : GeneratesInvariantLine ρ H v) :
    ∃! χ : TorusWeight H, IsWeightVector ρ H v χ :=
  invariantLine_torusWeight_existsUnique ρ hρ H v hv

end

section

variable {k : Type u} [Field k]

/-- Pure tensors multiply torus weights and preserve Borel semi-invariance. -/
public lemma tensorProduct_hasHighWeight_tmul
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    {V₁ : Type v} {V₂ : Type w}
    [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : RationalRepresentation K V₁) (ρ₂ : RationalRepresentation K V₂)
    (ρTensor : RationalRepresentation K (TensorProduct k V₁ V₂))
    (hTensor : IsTensorProductRepresentation ρ₁ ρ₂ ρTensor)
    (v₁ : V₁) (v₂ : V₂) (χ₁ χ₂ : TorusWeight T)
    (hv₁ : HasHighWeight ρ₁ B T v₁ χ₁)
    (hv₂ : HasHighWeight ρ₂ B T v₂ χ₂) :
    HasHighWeight ρTensor B T (TensorProduct.tmul k v₁ v₂) (χ₁ * χ₂) := by
  have htensor_ne : TensorProduct.tmul k v₁ v₂ ≠ 0 := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv₁.1.1
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one k hv₂.1.1
    intro h
    have h' := congrArg (TensorProduct.lift (f.smulRight g)) h
    simp [hf, hg] at h'
  constructor
  · constructor
    · exact htensor_ne
    · intro b hb
      obtain ⟨c₁, hc₁⟩ := hv₁.1.2 b hb
      obtain ⟨c₂, hc₂⟩ := hv₂.1.2 b hb
      refine ⟨c₁ * c₂, ?_⟩
      rw [hTensor, hc₁, hc₂]
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      rw [smul_smul, mul_comm]
  · constructor
    · exact htensor_ne
    · intro t
      rw [hTensor, hv₁.2.2 t, hv₂.2.2 t]
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      rw [smul_smul, mul_comm]
      change _ = ((χ₁.pointCharacter t * χ₂.pointCharacter t) • v₁) ⊗ₜ[k] v₂
      rfl

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A cyclic high-weight representation has an irreducible quotient retaining
the high-weight vector and its weight. This is GLS3, Theorem 1.14.6(d). -/
public theorem highWeight_cyclicQuotient_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (B T : ClosedSubgroup K) (v : V) (χ : TorusWeight T)
    (hv : HasHighWeight ρ B T v χ) (hgen : IsCyclicRepresentation ρ v) :
    ∃ W : Submodule k V, IsInvariantSubmodule ρ W ∧ v ∉ W ∧
      ∃ σ : RationalRepresentation K (V ⧸ W),
        IsQuotientRepresentation ρ W σ ∧
        IsRationalRepresentation σ ∧
        IsAlgebraicallyIrreducibleRepresentation σ ∧
        HasHighWeight σ B T (Submodule.Quotient.mk v) χ := by
  classical
  let Candidate : ℕ → Prop := fun n =>
    ∃ W : Submodule k V,
      IsInvariantSubmodule ρ W ∧ v ∉ W ∧ Module.finrank k W = n
  have hvne : v ≠ 0 := hv.1.1
  have hCandidateZero : Candidate 0 := by
    refine ⟨⊥, ?_, ?_, ?_⟩
    · intro g x hx
      change x = 0 at hx
      subst x
      simp
    · simpa using hvne
    · simp
  let maximalRank := Nat.findGreatest Candidate (Module.finrank k V)
  have hCandidateMaximal : Candidate maximalRank := by
    exact Nat.findGreatest_spec (Nat.zero_le _) hCandidateZero
  obtain ⟨W, hWInvariant, hvW, hWrank⟩ := hCandidateMaximal
  have hWMaximal {S : Submodule k V}
      (hWS : W ≤ S) (hSInvariant : IsInvariantSubmodule ρ S) (hvS : v ∉ S) :
      S = W := by
    have hSCandidate : Candidate (Module.finrank k S) :=
      ⟨S, hSInvariant, hvS, rfl⟩
    have hSrankLe : Module.finrank k S ≤ maximalRank :=
      Nat.le_findGreatest (Submodule.finrank_le S) hSCandidate
    symm
    apply Submodule.eq_of_le_of_finrank_le hWS
    simpa [hWrank] using hSrankLe
  obtain ⟨σ, hσQuotient, hσRational⟩ :=
    rationalRepresentation_quotient_exists ρ hρ W hWInvariant
  let q : V →ₗ[k] V ⧸ W := W.mkQ
  have hq_apply (x : V) : q x = Submodule.Quotient.mk x := rfl
  have hqvne : q v ≠ 0 := by
    rw [hq_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hvW
  have hqHighWeight : HasHighWeight σ B T (q v) χ := by
    constructor
    · constructor
      · exact hqvne
      · intro b hb
        obtain ⟨c, hc⟩ := hv.1.2 b hb
        refine ⟨c, ?_⟩
        rw [hq_apply, hσQuotient]
        change Submodule.Quotient.mk ((ρ.action b).1 v) =
          Submodule.Quotient.mk (c • v)
        rw [hc]
    · constructor
      · exact hqvne
      · intro t
        rw [hq_apply, hσQuotient]
        change Submodule.Quotient.mk
            ((ρ.action (T.includePoint t)).1 v) =
          Submodule.Quotient.mk (χ.pointCharacter t • v)
        rw [hv.2.2 t]
  have hσIrreducible : IsAlgebraicallyIrreducibleRepresentation σ := by
    intro Q hQInvariant
    let S : Submodule k V := Q.comap q
    have hSInvariant : IsInvariantSubmodule ρ S := by
      intro g x hx
      have hact := hQInvariant g (q x) hx
      rw [hq_apply, hσQuotient] at hact
      exact hact
    have hWS : W ≤ S := by
      intro x hx
      change q x ∈ Q
      rw [show q x = 0 by
        rw [hq_apply, Submodule.Quotient.mk_eq_zero]
        exact hx]
      exact Q.zero_mem
    by_cases hqvQ : q v ∈ Q
    · right
      have hSTop : S = ⊤ := hgen S hSInvariant hqvQ
      apply top_unique
      intro y _
      refine Submodule.Quotient.induction_on W y ?_
      intro x
      have hxS : x ∈ S := by rw [hSTop]; exact Submodule.mem_top
      exact hxS
    · left
      have hvS : v ∉ S := hqvQ
      have hSW : S = W := hWMaximal hWS hSInvariant hvS
      apply le_antisymm
      · intro y hy
        refine Submodule.Quotient.induction_on W y ?_ hy
        intro x hxQ
        have hxS : x ∈ S := hxQ
        rw [hSW] at hxS
        rw [show Submodule.Quotient.mk x = 0 by
          rw [Submodule.Quotient.mk_eq_zero]
          exact hxS]
        exact Submodule.zero_mem _
      · exact bot_le
  exact ⟨W, hWInvariant, hvW, σ, hσQuotient, hσRational,
    hσIrreducible, hqHighWeight⟩

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma invariantLine_fixed_of_unipotent_subgroup
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (H U : ClosedSubgroup K) (v : V)
    (hv : GeneratesInvariantLine ρ H v) (hUH : U ≤ H)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    ∀ u, u ∈ U → (ρ.action u).1 v = v := by
  obtain ⟨χ, hχ, -⟩ := invariantLine_torusWeight_existsUnique ρ hρ H v hv
  have hmap (x : Variety.Point U.carrierVariety) :
      U.inclusion.onPoints x ∈ H :=
    hUH (U.pointEquiv x).property
  let inclusionUH : AlgebraicGroup.Morphism U.carrierVariety H.carrierVariety :=
    U.inclusion.codRestrictClosedSubgroup H hmap
  let χU : TorusCharacter U.carrierVariety := χ.comp inclusionUH
  intro u hu
  let uU : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨u, hu⟩
  let uH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨u, hUH hu⟩
  have huU : U.inclusion.onPoints uU = u := by
    change (U.pointEquiv uU).val = u
    simp [uU]
  have huH : H.inclusion.onPoints uH = u := by
    change (H.pointEquiv uH).val = u
    simp [uH]
  have hinclusionUH : inclusionUH.onPoints uU = uH := by
    apply H.inclusion_injective
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    rw [huU, huH]
  have hχUunipotent : IsUnipotentElement (KMult k) (χU.onPoints uU) :=
    morphism_preserves_unipotentElement χU uU (hU uU)
  have hχUone : χU.onPoints uU = 1 :=
    semisimple_unipotent_eq_one (χU.onPoints uU) (dVariety_all_semisimple 1 (χU.onPoints uU)) hχUunipotent
  have hscalar : χ.pointCharacter uH = 1 := by
    have hpoint := congrArg (fun q : Variety.Point (KMult k) => (dPointEquiv 1 q 0 : k)) hχUone
    change (dPointEquiv 1 (χ.onPoints (inclusionUH.onPoints uU)) 0 : k) = 1 at hpoint
    rw [hinclusionUH] at hpoint
    exact hpoint
  have hweight := hχ.2 uH
  have huH' : H.includePoint uH = u := huH
  rw [huH'] at hweight
  rw [hscalar] at hweight
  simpa using hweight

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A high-weight vector in a finite-dimensional rational representation
survives in an irreducible composition factor with the same weight. -/
public theorem highWeight_compositionFactor_exists
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (B T : ClosedSubgroup K) (v : V) (χ : TorusWeight T)
    (hv : HasHighWeight ρ B T v χ) :
    ∃ C : Submodule k V, ∃ Q : Submodule k C,
      ∃ σ : RationalRepresentation K (C ⧸ Q),
        IsCompositionFactorOf ρ σ ∧ ∃ z, HasHighWeight σ B T z χ := by
  classical
  let C : Submodule k V :=
    sInf {W : Submodule k V | IsInvariantSubmodule ρ W ∧ v ∈ W}
  have hCInvariant : IsInvariantSubmodule ρ C := by
    intro g x hx
    exact Submodule.mem_sInf.2 fun W hW =>
      hW.1 g x (Submodule.mem_sInf.1 hx W hW)
  have hvC : v ∈ C := by
    apply Submodule.mem_sInf.2
    intro W hW
    exact hW.2
  obtain ⟨τ, hτRestrict, hτRational⟩ :=
    rationalRepresentation_restriction_exists ρ hρ C hCInvariant
  let vC : C := ⟨v, hvC⟩
  have hvC_high : HasHighWeight τ B T vC χ := by
    constructor
    · constructor
      · intro hvCzero
        exact hv.1.1 (congrArg Subtype.val hvCzero)
      · intro b hb
        obtain ⟨c, hc⟩ := hv.1.2 b hb
        refine ⟨c, Subtype.ext ?_⟩
        exact (hτRestrict b vC).trans hc
    · constructor
      · intro hvCzero
        exact hv.2.1 (congrArg Subtype.val hvCzero)
      · intro t
        apply Subtype.ext
        exact (hτRestrict (T.includePoint t) vC).trans (hv.2.2 t)
  have hτCyclic : IsCyclicRepresentation τ vC := by
    intro Q hQInvariant hvQ
    apply top_unique
    intro y _
    let S : Submodule k V := Q.map C.subtype
    have hSInvariant : IsInvariantSubmodule ρ S := by
      intro g x hx
      rcases hx with ⟨q, hq, rfl⟩
      refine ⟨(τ.action g).1 q, hQInvariant g q hq, ?_⟩
      exact hτRestrict g q
    have hvS : v ∈ S := ⟨vC, hvQ, rfl⟩
    have hCS : C ≤ S := sInf_le ⟨hSInvariant, hvS⟩
    have hyS : y.1 ∈ S := hCS y.2
    obtain ⟨q, hq, hqy⟩ := hyS
    have hqeq : q = y := Subtype.ext hqy
    simpa [hqeq] using hq
  obtain ⟨Q, _hQInvariant, _hvQ, σ, hσQuotient, hσRational,
      hσAlgebraicallyIrreducible, hσHigh⟩ :=
    highWeight_cyclicQuotient_exists τ hτRational B T vC χ hvC_high hτCyclic
  refine ⟨C, Q, σ, ?_, Submodule.Quotient.mk vC, hσHigh⟩
  constructor
  · exact ⟨hσRational, hσAlgebraicallyIrreducible⟩
  · refine ⟨C, inferInstance, inferInstance, τ, C.subtype, Q.mkQ,
      C.subtype_injective, Q.mkQ_surjective, hτRestrict, ?_⟩
    intro g x
    exact (hσQuotient g x).symm

end

section

open scoped TensorProduct

variable {k : Type u} [Field k]

private noncomputable def torusWeightPointEvaluation
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (t : Variety.Point T.carrierVariety) : TorusWeight T →* k where
  toFun weight := weight.pointCharacter t
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Example 1.14.9(e): exterior powers carry the induced action, and a nonzero
exterior product of high-weight vectors has the product of their weights. -/
public theorem exteriorPower_highWeight_representation
    {K : Variety k} [AlgebraicGroup K] (T B : ClosedSubgroup K)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (i : ℕ)
    (vectors : Fin i → V) (weights : Fin i → TorusWeight T)
    (hvectors : ∀ j, HasHighWeight ρ B T (vectors j) (weights j))
    (hwedge : exteriorPower.ιMulti k i vectors ≠ 0) :
    ∃ σ : RationalRepresentation K (⋀[k]^i V),
      (∀ g x, (σ.action g).1 x =
        exteriorPower.map i ((ρ.action g).1 : V →ₗ[k] V) x) ∧
      HasHighWeight σ B T (exteriorPower.ιMulti k i vectors) (∏ j, weights j) := by
  refine ⟨exteriorPowerRepresentation ρ i, exteriorPowerRepresentation_action ρ i, ?_⟩
  constructor
  · constructor
    · exact hwedge
    · intro b hb
      choose scalars hscalars using fun j => (hvectors j).1.2 b hb
      refine ⟨∏ j, scalars j, ?_⟩
      rw [exteriorPowerRepresentation_action, exteriorPower.map_apply_ιMulti]
      change exteriorPower.ιMulti k i
        (fun j => (ρ.action b).1 (vectors j)) =
          (∏ j, scalars j) • exteriorPower.ιMulti k i vectors
      rw [show (fun j => (ρ.action b).1 (vectors j)) =
          fun j => scalars j • vectors j by
            funext j
            exact hscalars j]
      exact (exteriorPower.ιMulti k i).map_smul_univ scalars vectors
  · constructor
    · exact hwedge
    · intro t
      rw [exteriorPowerRepresentation_action, exteriorPower.map_apply_ιMulti]
      change exteriorPower.ιMulti k i
        (fun j => (ρ.action (T.includePoint t)).1 (vectors j)) =
          (∏ j, weights j).pointCharacter t • exteriorPower.ιMulti k i vectors
      rw [show (fun j => (ρ.action (T.includePoint t)).1 (vectors j)) =
          fun j => (weights j).pointCharacter t • vectors j by
            funext j
            exact (hvectors j).2.2 t]
      rw [show (∏ j, weights j).pointCharacter t =
        ∏ j, (weights j).pointCharacter t by
          exact map_prod (torusWeightPointEvaluation T t) weights Finset.univ]
      exact (exteriorPower.ιMulti k i).map_smul_univ
        (fun j => (weights j).pointCharacter t) vectors

end

end Theory.AlgebraicGroup
