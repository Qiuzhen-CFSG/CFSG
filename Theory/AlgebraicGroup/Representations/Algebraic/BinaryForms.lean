module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Theory.AlgebraicGroup.Representations.Algebraic.HighestWeight
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural

universe u

namespace Theory.AlgebraicGroup

section

/-- Binary homogeneous polynomials of total degree `n`. -/
public abbrev BinaryHomogeneousPolynomial
    (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k n

public noncomputable instance binaryHomogeneousPolynomial_moduleFinite
    (k : Type u) [Field k] (n : ℕ) :
    Module.Finite k (BinaryHomogeneousPolynomial k n) :=
  Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg (Fin 2) k n)

end

/-! Binary-form substitutions and actions. -/

section

open MvPolynomial

variable {k : Type u} [Field k]

@[expose]
public noncomputable def binaryLinearSubstitution
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (i : Fin 2) :
    MvPolynomial (Fin 2) k :=
  ∑ j, C (g.1 (Pi.single i 1) j) * X j

public lemma binaryLinearSubstitution_isHomogeneous
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (i : Fin 2) :
    (binaryLinearSubstitution g i).IsHomogeneous 1 := by
  unfold binaryLinearSubstitution
  apply IsHomogeneous.sum
  intro j hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

@[expose]
public noncomputable def binarySubstitute
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.bind₁ (binaryLinearSubstitution g)

public lemma binarySubstitute_mem
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) {n : ℕ}
    (p : BinaryHomogeneousPolynomial k n) :
    binarySubstitute g p.1 ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) k n := by
  change (MvPolynomial.eval₂ C (binaryLinearSubstitution g) p.1).IsHomogeneous n
  simpa using p.2.eval₂ _ _ (fun r => isHomogeneous_C _ _)
    (binaryLinearSubstitution_isHomogeneous g)

public lemma binarySubstitute_binaryLinearSubstitution
    (g h : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (i : Fin 2) :
    binarySubstitute g (binaryLinearSubstitution h i) =
      binaryLinearSubstitution (g * h) i := by
  simp only [binarySubstitute, binaryLinearSubstitution, map_sum, map_mul,
    MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp_rw [← mul_assoc, ← map_mul]
  rw [← Finset.sum_mul, ← map_sum]
  have hcoeff :
      ∑ j, h.1 (Pi.single i 1) j * g.1 (Pi.single j 1) l =
        (g * h).1 (Pi.single i 1) l := by
    rw [show (g * h).1 (Pi.single i 1) = g.1 (h.1 (Pi.single i 1)) by rfl]
    rw [show h.1 (Pi.single i 1) =
        ∑ j, h.1 (Pi.single i 1) j • Pi.single j 1 by
      ext q
      simp [Pi.single_apply]]
    simp only [map_sum, LinearMap.map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp [Pi.single_apply]
  rw [hcoeff]

public lemma binarySubstitute_mul
    (g h : LinearMap.GeneralLinearGroup k (Fin 2 → k))
    (p : MvPolynomial (Fin 2) k) :
    binarySubstitute g (binarySubstitute h p) = binarySubstitute (g * h) p := by
  change MvPolynomial.bind₁ (binaryLinearSubstitution g)
      (MvPolynomial.bind₁ (binaryLinearSubstitution h) p) =
    MvPolynomial.bind₁ (binaryLinearSubstitution (g * h)) p
  rw [MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.bind₁_X_right]
  exact binarySubstitute_binaryLinearSubstitution g h i

public lemma binaryLinearSubstitution_one (i : Fin 2) :
    binaryLinearSubstitution (1 : LinearMap.GeneralLinearGroup k (Fin 2 → k)) i = X i := by
  unfold binaryLinearSubstitution
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

public lemma binarySubstitute_one (p : MvPolynomial (Fin 2) k) :
    binarySubstitute (1 : LinearMap.GeneralLinearGroup k (Fin 2 → k)) p = p := by
  change MvPolynomial.bind₁ (binaryLinearSubstitution 1) p = p
  rw [show binaryLinearSubstitution
      (1 : LinearMap.GeneralLinearGroup k (Fin 2 → k)) = X by
    funext i
    exact binaryLinearSubstitution_one i]
  exact AlgHom.congr_fun MvPolynomial.bind₁_X_left p

@[expose]
public noncomputable def binaryHomogeneousPolynomialLinearMap
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (n : ℕ) :
    BinaryHomogeneousPolynomial k n →ₗ[k] BinaryHomogeneousPolynomial k n :=
  LinearMap.codRestrict _
    ((binarySubstitute g).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) k n).subtype)
    (binarySubstitute_mem g)

@[simp]
public lemma binaryHomogeneousPolynomialLinearMap_apply
    (g : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (n : ℕ)
    (p : BinaryHomogeneousPolynomial k n) :
    (binaryHomogeneousPolynomialLinearMap g n p).1 = binarySubstitute g p.1 :=
  rfl

public lemma binaryHomogeneousPolynomialLinearMap_mul
    (g h : LinearMap.GeneralLinearGroup k (Fin 2 → k)) (n : ℕ) :
    binaryHomogeneousPolynomialLinearMap (g * h) n =
      (binaryHomogeneousPolynomialLinearMap g n).comp
        (binaryHomogeneousPolynomialLinearMap h n) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact (binarySubstitute_mul g h p.1).symm

public lemma binaryHomogeneousPolynomialLinearMap_one (n : ℕ) :
    binaryHomogeneousPolynomialLinearMap
      (1 : LinearMap.GeneralLinearGroup k (Fin 2 → k)) n = LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact binarySubstitute_one p.1

@[expose]
public noncomputable def binaryHomogeneousPolynomialGeneralLinearGroupHom
    (n : ℕ) :
    LinearMap.GeneralLinearGroup k (Fin 2 → k) →*
      LinearMap.GeneralLinearGroup k (BinaryHomogeneousPolynomial k n) where
  toFun g := {
    val := binaryHomogeneousPolynomialLinearMap g n
    inv := binaryHomogeneousPolynomialLinearMap g⁻¹ n
    val_inv := by
      change (binaryHomogeneousPolynomialLinearMap g n).comp
          (binaryHomogeneousPolynomialLinearMap g⁻¹ n) = LinearMap.id
      rw [← binaryHomogeneousPolynomialLinearMap_mul,
        mul_inv_cancel, binaryHomogeneousPolynomialLinearMap_one]
    inv_val := by
      change (binaryHomogeneousPolynomialLinearMap g⁻¹ n).comp
          (binaryHomogeneousPolynomialLinearMap g n) = LinearMap.id
      rw [← binaryHomogeneousPolynomialLinearMap_mul,
        inv_mul_cancel, binaryHomogeneousPolynomialLinearMap_one] }
  map_one' := by
    apply Units.ext
    exact binaryHomogeneousPolynomialLinearMap_one n
  map_mul' g h := Units.ext <| by
    change binaryHomogeneousPolynomialLinearMap (g * h) n =
      (binaryHomogeneousPolynomialLinearMap g n).comp
        (binaryHomogeneousPolynomialLinearMap h n)
    exact binaryHomogeneousPolynomialLinearMap_mul g h n

end

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def binaryExponentEquiv (n : ℕ) :
    {d : Fin 2 →₀ ℕ // d.degree = n} ≃ Fin (n + 1) where
  toFun d := ⟨d.1 0, by
    have hsum : d.1 0 + d.1 1 = n := by
      simpa [Finsupp.degree_eq_sum] using d.2
    omega⟩
  invFun i := ⟨Finsupp.equivFunOnFinite.symm
      (fun j => if j = 0 then i.1 else n - i.1), by
    rw [Finsupp.degree_eq_sum]
    simp [Fin.sum_univ_two, Nat.add_sub_of_le (Nat.le_of_lt_succ i.2)]⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.equivFunOnFinite.injective
    funext j
    fin_cases j
    · simp
    · have hsum : d.1 0 + d.1 1 = n := by
        simpa [Finsupp.degree_eq_sum] using d.2
      simp
      omega
  right_inv i := by
    apply Fin.ext
    simp

@[expose]
public noncomputable def addMonoidSupportedEquivFinsuppSupported
    (s : Set (Fin 2 →₀ ℕ)) :
    AddMonoidAlgebra.supported k k s ≃ₗ[k] Finsupp.supported k k s where
  toFun p := ⟨(AddMonoidAlgebra.coeffLinearEquiv k) p.1, p.2⟩
  invFun p := ⟨(AddMonoidAlgebra.coeffLinearEquiv k).symm p.1, by
    have hp : (p.1.support : Set (Fin 2 →₀ ℕ)) ⊆ s := p.2
    change (((AddMonoidAlgebra.coeffLinearEquiv k)
      ((AddMonoidAlgebra.coeffLinearEquiv k).symm p.1)).support :
        Set (Fin 2 →₀ ℕ)) ⊆ s
    rw [(AddMonoidAlgebra.coeffLinearEquiv k).apply_symm_apply]
    exact hp⟩
  left_inv p := by
    apply Subtype.ext
    exact (AddMonoidAlgebra.coeffLinearEquiv k).symm_apply_apply p.1
  right_inv p := by
    apply Subtype.ext
    exact (AddMonoidAlgebra.coeffLinearEquiv k).apply_symm_apply p.1
  map_add' p q := by
    apply Subtype.ext
    exact (AddMonoidAlgebra.coeffLinearEquiv k).map_add p.1 q.1
  map_smul' r p := by
    apply Subtype.ext
    exact (AddMonoidAlgebra.coeffLinearEquiv k).map_smul r p.1

@[expose]
public noncomputable def binaryHomogeneousPolynomialBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) k (BinaryHomogeneousPolynomial k n) :=
  let s : Set (Fin 2 →₀ ℕ) := {d | d.degree = n}
  let e0 : BinaryHomogeneousPolynomial k n ≃ₗ[k]
      AddMonoidAlgebra.supported k k s :=
    LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) k n)
  let e1 : AddMonoidAlgebra.supported k k s ≃ₗ[k]
      Finsupp.supported k k s :=
    addMonoidSupportedEquivFinsuppSupported s
  let e2 : Finsupp.supported k k s ≃ₗ[k] s →₀ k :=
    Finsupp.supportedEquivFinsupp s
  let e3 : (s →₀ k) ≃ₗ[k] (Fin (n + 1) →₀ k) :=
    Finsupp.domLCongr (binaryExponentEquiv n)
  Finsupp.basisSingleOne.map (e0.trans (e1.trans (e2.trans e3))).symm

public lemma binaryHomogeneousPolynomial_finrank (n : ℕ) :
    Module.finrank k (BinaryHomogeneousPolynomial k n) = n + 1 := by
  rw [Module.finrank_eq_card_basis
    (binaryHomogeneousPolynomialBasis (k := k) n)]
  simp

end

/-! Binary-form representations. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def binaryHomogeneousPolynomialRepresentation
    {K : Variety k} [AlgebraicGroup K]
    (hKSL : AlgebraicGroup.Iso K (slVariety k 2)) (n : ℕ) :
    RationalRepresentation K (BinaryHomogeneousPolynomial k n) where
  action :=
    (binaryHomogeneousPolynomialGeneralLinearGroupHom n).comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp
        (Matrix.SpecialLinearGroup.toGL.comp
          ((specialLinearPointMulEquiv (k := k) 2).toMonoidHom.comp
            hKSL.hom.onPoints)))

@[expose]
public def IsBinaryHomogeneousPolynomialRepresentation
    {K : Variety k} [AlgebraicGroup K]
    (hKSL : AlgebraicGroup.Iso K (slVariety k 2)) (n : ℕ)
    (ρ : RationalRepresentation K (BinaryHomogeneousPolynomial k n)) : Prop :=
  ∀ g p, (ρ.action g).1 p =
    binaryHomogeneousPolynomialLinearMap
      (Matrix.GeneralLinearGroup.toLin
        (Matrix.SpecialLinearGroup.toGL
          (specialLinearPointMulEquiv (k := k) 2 (hKSL.hom.onPoints g)))) n p

public lemma binaryHomogeneousPolynomialRepresentation_spec
    {K : Variety k} [AlgebraicGroup K]
    (hKSL : AlgebraicGroup.Iso K (slVariety k 2)) (n : ℕ) :
    IsBinaryHomogeneousPolynomialRepresentation hKSL n
      (binaryHomogeneousPolynomialRepresentation hKSL n) := by
  intro g p
  rfl

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def binaryHighestMonomial (n : ℕ) :
    BinaryHomogeneousPolynomial k n :=
  ⟨MvPolynomial.X 0 ^ n, MvPolynomial.isHomogeneous_X_pow 0 n⟩

omit [IsAlgClosed k] in
lemma binaryHighestMonomial_ne_zero (n : ℕ) :
    binaryHighestMonomial (k := k) n ≠ 0 := by
  intro h
  have hpoly :
      (MvPolynomial.X (0 : Fin 2) ^ n : MvPolynomial (Fin 2) k) = 0 :=
    congrArg Subtype.val h
  simp at hpoly

public theorem binaryHighestMonomial_hasHighWeight
    {K : Variety k} [AlgebraicGroup K]
    (hKSL : AlgebraicGroup.Iso K (slVariety k 2))
    (B T : ClosedSubgroup K) (lambdaOne : TorusWeight T)
    (hUpper : ∀ b, b ∈ B →
      (specialLinearPointMulEquiv (k := k) 2
        (hKSL.hom.onPoints b)).1 1 0 = 0)
    (hDiagonal : ∀ t : Variety.Point T.carrierVariety,
      (specialLinearPointMulEquiv (k := k) 2
        (hKSL.hom.onPoints (T.includePoint t))).1 0 1 = 0 ∧
      (specialLinearPointMulEquiv (k := k) 2
        (hKSL.hom.onPoints (T.includePoint t))).1 1 0 = 0)
    (hLambda : ∀ t : Variety.Point T.carrierVariety,
      (lambdaOne.pointCharacter t : k) =
        (specialLinearPointMulEquiv (k := k) 2
          (hKSL.hom.onPoints (T.includePoint t))).1 0 0)
    (n : ℕ) :
    HasHighWeight
      (binaryHomogeneousPolynomialRepresentation hKSL n) B T
      (binaryHighestMonomial (k := k) n) (lambdaOne ^ n) := by
  constructor
  · constructor
    · exact binaryHighestMonomial_ne_zero n
    · intro b hb
      let g := Matrix.GeneralLinearGroup.toLin
        (Matrix.SpecialLinearGroup.toGL
          (specialLinearPointMulEquiv (k := k) 2 (hKSL.hom.onPoints b)))
      refine ⟨(g.1 (Pi.single 0 1) 0) ^ n, ?_⟩
      rw [binaryHomogeneousPolynomialRepresentation_spec hKSL n]
      apply Subtype.ext
      unfold binaryHighestMonomial
      simp only [binaryHomogeneousPolynomialLinearMap_apply]
      change binarySubstitute g (MvPolynomial.X 0 ^ n) =
        ((g.1 (Pi.single 0 1) 0) ^ n) • MvPolynomial.X 0 ^ n
      rw [MvPolynomial.smul_eq_C_mul, map_pow]
      simp only [binarySubstitute, MvPolynomial.bind₁_X_right]
      have hg10 : g.1 (Pi.single 0 1) 1 = 0 := by
        simpa [g, Pi.single_apply] using hUpper b hb
      simp [binaryLinearSubstitution, Fin.sum_univ_two, hg10, mul_pow,
        map_pow]
  · constructor
    · exact binaryHighestMonomial_ne_zero n
    · intro t
      let g := Matrix.GeneralLinearGroup.toLin
        (Matrix.SpecialLinearGroup.toGL
          (specialLinearPointMulEquiv (k := k) 2
            (hKSL.hom.onPoints (T.includePoint t))))
      rw [binaryHomogeneousPolynomialRepresentation_spec hKSL n]
      apply Subtype.ext
      unfold binaryHighestMonomial
      simp only [binaryHomogeneousPolynomialLinearMap_apply]
      change binarySubstitute g (MvPolynomial.X 0 ^ n) =
        (((lambdaOne ^ n).pointCharacter t : k)) •
          MvPolynomial.X 0 ^ n
      rw [MvPolynomial.smul_eq_C_mul, map_pow]
      simp only [binarySubstitute, MvPolynomial.bind₁_X_right]
      have hg10 : g.1 (Pi.single 0 1) 1 = 0 := by
        simpa [g, Pi.single_apply] using (hDiagonal t).2
      have hg00 : g.1 (Pi.single 0 1) 0 =
          (lambdaOne.pointCharacter t : k) := by
        simpa [g, Pi.single_apply] using (hLambda t).symm
      have hcharpow :
          (((lambdaOne ^ n).pointCharacter t : k)) =
            (lambdaOne.pointCharacter t : k) ^ n := by
        induction n with
        | zero =>
            rw [pow_zero, pow_zero]
            change (1 : k) = 1
            rfl
        | succ n ih =>
            rw [pow_succ, pow_succ]
            change (((lambdaOne ^ n).pointCharacter t : k) *
                (lambdaOne.pointCharacter t : k)) =
              (lambdaOne.pointCharacter t : k) ^ n *
                (lambdaOne.pointCharacter t : k)
            rw [ih]
      simp [binaryLinearSubstitution, Fin.sum_univ_two, hg10, hg00,
        mul_pow, hcharpow]

end

end Theory.AlgebraicGroup
