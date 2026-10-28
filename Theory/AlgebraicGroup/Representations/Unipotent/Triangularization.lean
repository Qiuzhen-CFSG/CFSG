module

public import Theory.AlgebraicGroup.Instance.U
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Representations.Unipotent.Flag

universe u v w

namespace Theory.AlgebraicGroup

namespace Subrepresentation

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The adapted-basis matrix of a stable-chain representation satisfies the
project's upper-triangular predicate. -/
private lemma representation_toMatrix_basis_is_tTriangular
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (g : Γ) :
    tTriangular n (LinearMap.toMatrix b b (ρ g)) := by
  intro i j hji
  exact representation_toMatrix_basis_belowDiagonal_eq_zero
    ρ b F hstable hb g hji

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Powers of an upper-triangular matrix have diagonal entries equal to the
corresponding powers of the original diagonal entries. -/
private lemma tTriangular_pow_apply_diag
    (n : ℕ) {A : Matrix (Fin n) (Fin n) k}
    (hA : tTriangular n A) (m : ℕ) (i : Fin n) :
    (A ^ m) i i = (A i i) ^ m := by
  have htriPow : ∀ r : ℕ, tTriangular n (A ^ r) := by
    intro r
    induction r with
    | zero =>
        intro a b hab
        simp [ne_of_gt hab]
    | succ r ihr =>
        rw [pow_succ]
        exact tTriangular_mul n ihr hA
  induction m with
  | zero => simp
  | succ m ihm =>
      rw [pow_succ, Matrix.mul_apply]
      have hsum : (∑ j : Fin n, (A ^ m) i j * A j i) =
          (A ^ m) i i * A i i := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          by_cases hlt : j < i
          · rw [htriPow m hlt, zero_mul]
          · have hij : i < j :=
              lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hji)
            rw [hA hij, mul_zero]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      rw [hsum, ihm]
      simp [pow_succ]

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Pointwise unipotence forces every adapted upper-triangular matrix diagonal
entry to equal one. -/
private lemma representation_toMatrix_basis_diag_eq_one_of_pointwise_unipotent
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    (g : Γ) (i : Fin n) :
    (LinearMap.toMatrix b b (ρ g)) i i = 1 := by
  have htri : tTriangular n (LinearMap.toMatrix b b (ρ g)) :=
    representation_toMatrix_basis_is_tTriangular ρ b F hstable hb g
  let B : Matrix (Fin n) (Fin n) k :=
    LinearMap.toMatrix b b (ρ g - 1)
  have hB : tTriangular n B := by
    intro p q hpq
    dsimp [B]
    rw [map_sub, LinearMap.toMatrix_one, Matrix.sub_apply]
    simp [htri hpq, ne_of_gt hpq]
  obtain ⟨m, hm⟩ :=
    (LinearMap.isNilpotent_toMatrix_iff b (ρ g - 1)).mpr (hunipotent g)
  have hpow : (B ^ m) i i = 0 := by
    exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M i i) hm
  have hpow' : (B i i) ^ m = 0 := by
    rw [tTriangular_pow_apply_diag n hB m i] at hpow
    exact hpow
  have hzero : B i i = 0 := eq_zero_of_pow_eq_zero hpow'
  have hdiag : B i i = (LinearMap.toMatrix b b (ρ g)) i i - 1 := by
    dsimp [B]
    rw [map_sub, LinearMap.toMatrix_one, Matrix.sub_apply]
    simp
  rw [hdiag] at hzero
  exact sub_eq_zero.mp hzero

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- A pointwise-unipotent representation is unitriangular in the adapted
stable-chain basis. -/
public lemma representation_toMatrix_basis_is_uUnipotent_of_pointwise_unipotent
    (ρ : Representation k Γ V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1))
    (g : Γ) :
    uUnipotent n (LinearMap.toMatrix b b (ρ g)) := by
  constructor
  · exact representation_toMatrix_basis_is_tTriangular ρ b F hstable hb g
  · intro i
    exact representation_toMatrix_basis_diag_eq_one_of_pointwise_unipotent
      ρ b F hstable hb hunipotent g i

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The adapted-basis matrix of a pointwise-unipotent general-linear
representation lies in the existing unitriangular matrix subgroup. -/
private lemma representation_toMatrix_basis_mem_uUnipotentGL_of_pointwise_unipotent
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent ((ρ g : Module.End k V) - 1))
    (g : Γ) :
    ((Matrix.GeneralLinearGroup.toLin' b).symm (ρ g)) ∈ uUnipotentGL k n := by
  let ρ₀ : Representation k Γ V :=
    { toFun := fun g => (ρ g : Module.End k V)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }
  have hstable₀ : ∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ₀ g) := by
    intro m g x hx
    exact hstable m g hx
  have hU : uUnipotent n (LinearMap.toMatrix b b (ρ₀ g)) :=
    representation_toMatrix_basis_is_uUnipotent_of_pointwise_unipotent
      ρ₀ b F hstable₀ hb (fun g => hunipotent g) g
  change uUnipotent n
    (((Matrix.GeneralLinearGroup.toLin' b).symm (ρ g) : GL (Fin n) k) :
      Matrix (Fin n) (Fin n) k)
  have hmatrix :
      (((Matrix.GeneralLinearGroup.toLin' b).symm (ρ g) : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) =
        LinearMap.toMatrix b b ((ρ g : Module.End k V)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hx := (Matrix.GeneralLinearGroup.toLin' b).apply_symm_apply (ρ g)
    have h := congrArg (fun y : LinearMap.GeneralLinearGroup k V =>
        b.repr (y.toLinearEquiv (b j)) i) hx
    rw [Matrix.GeneralLinearGroup.toLin'_apply] at h
    simpa [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
      Finsupp.single_apply] using h
  rw [hmatrix]
  exact hU

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The adapted-basis matrices assemble into a monoid homomorphism with values
in the existing unitriangular subgroup. -/
private lemma representation_to_uUnipotentGL_hom_of_pointwise_unipotent
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent ((ρ g : Module.End k V) - 1)) :
    ∃ φ : Γ →* uUnipotentGL k n, ∀ g : Γ,
      (φ g : GL (Fin n) k) = (Matrix.GeneralLinearGroup.toLin' b).symm (ρ g) := by
  let φ : Γ →* uUnipotentGL k n :=
    { toFun := fun g =>
        ⟨(Matrix.GeneralLinearGroup.toLin' b).symm (ρ g),
          representation_toMatrix_basis_mem_uUnipotentGL_of_pointwise_unipotent
            ρ b F hstable hb hunipotent g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro g h
        apply Subtype.ext
        simp }
  refine ⟨φ, ?_⟩
  intro g
  rfl

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A finite-dimensional pointwise-unipotent representation has an adapted
basis and a subgroup-valued unitriangular representation in that basis. -/
public lemma exists_adapted_basis_uUnipotentGL_hom_of_pointwise_unipotent
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (hunipotent : ∀ g : Γ, IsNilpotent ((ρ g : Module.End k V) - 1)) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V,
      ∃ F : ℕ → Submodule k V,
        (∀ (m : ℕ) (hm : m ≤ Module.finrank k V),
          F m = Submodule.span k (Set.range fun l : Fin m =>
            b (Fin.castLE hm l))) ∧
        (∀ (m : ℕ) (g : Γ), F m ≤ (F m).comap (ρ g : Module.End k V)) ∧
        ∃ φ : Γ →* uUnipotentGL k (Module.finrank k V),
          ∀ g : Γ,
            (φ g : GL (Fin (Module.finrank k V)) k) =
              (Matrix.GeneralLinearGroup.toLin' b).symm (ρ g) := by
  let ρ₀ : Representation k Γ V :=
    { toFun := fun g => (ρ g : Module.End k V)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }
  obtain ⟨F, hdim, hmono⟩ :=
    exists_finrank_strictMono_chain_of_pointwise_unipotent ρ₀ hunipotent
  let F' : ℕ → Submodule k V := fun m =>
    (F ⟨min m (Module.finrank k V), by omega⟩).toSubmodule
  have hmono' : Monotone F' := by
    intro m l hml
    dsimp [F']
    exact hmono.monotone (min_le_min hml le_rfl)
  have hdim' : ∀ i : ℕ,
      Module.finrank k (F' i) = min i (Module.finrank k V) := by
    intro i
    dsimp [F']
    exact hdim _
  have hstable' : ∀ (m : ℕ) (g : Γ),
      F' m ≤ (F' m).comap (ρ g : Module.End k V) := by
    intro m g
    dsimp [F']
    intro x hx
    exact (F ⟨min m (Module.finrank k V), by omega⟩).apply_mem_toSubmodule g hx
  obtain ⟨b, hb⟩ :=
    exists_basis_adapted_to_full_submodule_chain F' hmono' hdim'
  obtain ⟨φ, hφ⟩ := representation_to_uUnipotentGL_hom_of_pointwise_unipotent
    ρ b F' hstable' hb hunipotent
  exact ⟨b, F', hb, hstable', φ, hφ⟩

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- Injectivity of the original general-linear representation transfers to its
adapted-basis subgroup-valued representation. -/
public lemma representation_to_uUnipotentGL_hom_injective_of_injective
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ n),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent ((ρ g : Module.End k V) - 1))
    (hinjective : Function.Injective ρ) :
    ∃ φ : Γ →* uUnipotentGL k n,
      (∀ g : Γ,
        (φ g : GL (Fin n) k) = (Matrix.GeneralLinearGroup.toLin' b).symm (ρ g)) ∧
      Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := representation_to_uUnipotentGL_hom_of_pointwise_unipotent
    ρ b F hstable hb hunipotent
  refine ⟨φ, hφ, ?_⟩
  intro g h hgh
  apply hinjective
  have hgh' := congrArg (fun x : uUnipotentGL k n =>
      (x : GL (Fin n) k)) hgh
  rw [hφ g, hφ h] at hgh'
  simpa using congrArg (Matrix.GeneralLinearGroup.toLin' b) hgh'

end

section

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [IsAlgClosed k] [Group Γ] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [FiniteDimensional k V] in
/-- The `uVariety` coordinates reconstructed from the subgroup-valued
adapted-basis hom agree with the regular general-linear representation point. -/
public lemma representation_to_uVarietyPoint_coordinates_eq_generalLinearRepresentationPoint
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (F : ℕ → Submodule k V)
    (hstable : ∀ (m : ℕ) (g : Γ),
      F m ≤ (F m).comap (ρ g : Module.End k V))
    (hb : ∀ (m : ℕ) (hm : m ≤ Module.finrank k V),
      F m = Submodule.span k (Set.range fun l : Fin m =>
        b (Fin.castLE hm l)))
    (hunipotent : ∀ g : Γ, IsNilpotent ((ρ g : Module.End k V) - 1)) :
    ∃ φ : Γ →* uUnipotentGL k (Module.finrank k V),
      (∀ g : Γ,
        (φ g : GL (Fin (Module.finrank k V)) k) =
          (Matrix.GeneralLinearGroup.toLin' b).symm (ρ g)) ∧
      (∀ (g : Γ) (i j : Fin (Module.finrank k V)),
        ((uPointEquiv k (Module.finrank k V)).symm (φ g)).val
            (ULift.up (i, j)) =
          (generalLinearRepresentationPoint b (ρ g)).val (Sum.inl (i, j))) := by
  obtain ⟨φ, hφ⟩ := representation_to_uUnipotentGL_hom_of_pointwise_unipotent
    ρ b F hstable hb hunipotent
  refine ⟨φ, hφ, ?_⟩
  intro g i j
  rw [uPointEquiv_symm_val, hφ g, generalLinearRepresentationPoint_matrix]
  have hx := (Matrix.GeneralLinearGroup.toLin' b).apply_symm_apply (ρ g)
  have h := congrArg (fun y : LinearMap.GeneralLinearGroup k V =>
      b.repr (y.toLinearEquiv (b j)) i) hx
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h
  simpa [Fintype.linearCombination_apply, Matrix.mulVec, dotProduct,
    Finsupp.single_apply] using h

end

end Subrepresentation

end Theory.AlgebraicGroup
