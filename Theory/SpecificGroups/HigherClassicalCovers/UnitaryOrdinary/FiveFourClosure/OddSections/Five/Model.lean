module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourFormTransport
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The diagonal torus and coordinate permutations in SU₅(4)

The determinant-one norm-one diagonal torus is parametrized by four independent
fifth roots of unity: coordinate zero is the inverse product of the other four.
This gives its actual matrix embedding and order 5⁴. In characteristic two every
coordinate permutation has determinant one. Conjugation permutes the five
coordinates, including the distinguished coordinate zero.

Swapping two coordinates different from zero swaps the corresponding torus
basis elements. The central-extension swapping lemma therefore makes the full
torus preimage abelian in every central cover. The remaining lifting contract
asks for a section compatible with all coordinate permutations; it is an
explicit further obligation, not a consequence of abelianness alone.

The subgroup `monomial` adjoins the literal coordinate five-cycle. Its order
and the equivariant torus lift feed the transfer argument in the parent module.
Source: Aschbacher--Smith I.1.4(4), `refs/quasithin.pdf`, printed p.408;
GLS III Section 6.1, `refs/KGroup/GLS3/chapter6.tex`.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five

variable (C : Type*) [CommGroup C]

@[expose] def coordinateProduct : (Fin 5 → C) →* C where
  toFun a := ∏ i, a i
  map_one' := by simp
  map_mul' a b := Finset.prod_mul_distrib

abbrev Coordinates := (coordinateProduct C).ker

@[expose] def coordinatesEquiv : (Fin 4 → C) ≃* Coordinates C where
  toFun a := ⟨Fin.cons (∏ i, a i)⁻¹ a, by
    change ∏ i, Fin.cons (∏ i, a i)⁻¹ a i = 1
    simp [Fin.prod_univ_succ]⟩
  invFun a i := a.val i.succ
  left_inv a := rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have ha : ∏ i, a.val i = 1 := a.property
    rw [Fin.prod_univ_succ] at ha
    exact (eq_inv_of_mul_eq_one_left ha).symm
  map_mul' a b := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    simp [Finset.prod_mul_distrib, mul_comm]

@[expose] def permute (σ : Equiv.Perm (Fin 5)) (a : Coordinates C) : Coordinates C :=
  ⟨(fun i => a.val (σ⁻¹ i)), by
    change ∏ i, a.val (σ⁻¹ i) = 1
    rw [Equiv.prod_comp]
    exact a.property⟩

@[expose] def root (i j : Fin 5) (u : C) : Coordinates C :=
  ⟨Pi.mulSingle i u * Pi.mulSingle j u⁻¹, by
    change ∏ k, (Pi.mulSingle i u : Fin 5 → C) k * (Pi.mulSingle j u⁻¹ : Fin 5 → C) k = 1
    simp [Finset.prod_mul_distrib]⟩

theorem permute_root (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) (u : C) :
    permute C σ (root C i j u) = root C (σ i) (σ j) u := by
  apply Subtype.ext
  funext k
  simp only [permute, root, Pi.mul_apply, Pi.mulSingle_apply]
  simp [Equiv.symm_apply_eq]

theorem coordinatesEquiv_single (i : Fin 4) (u : C) :
    coordinatesEquiv C (Pi.mulSingle i u) = root C i.succ 0 u := by
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · change (∏ j, (Pi.mulSingle i u : Fin 4 → C) j)⁻¹ = _
    simp [root]
  · change (Pi.mulSingle i u : Fin 4 → C) j = _
    simp [root, Pi.mulSingle_apply]

variable {F : Type*} [Field F]

abbrev DiagonalCoordinates (F : Type*) [Field F] := Coordinates (rootsOfUnity 5 F)

private def diagonalGL : DiagonalCoordinates F →* GL (Fin 5) F where
  toFun a := ⟨Matrix.diagonal (fun i => ((a.val i).val : F)),
    Matrix.diagonal (fun i => (((a.val i).val)⁻¹ : Fˣ)), by
      simp only [diagonal_mul_diagonal]
      convert diagonal_one using 1
      congr 1
      funext i
      exact Units.mul_inv (a.val i).val, by
      simp only [diagonal_mul_diagonal]
      convert diagonal_one using 1
      congr 1
      funext i
      exact Units.inv_mul (a.val i).val⟩
  map_one' := by apply Units.ext; exact diagonal_one
  map_mul' a b := by apply Units.ext; exact (diagonal_mul_diagonal _ _).symm

private theorem diagonalGL_mem (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (a : DiagonalCoordinates F) :
    diagonalGL a ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · change J.conjTranspose (Matrix.diagonal (fun i => ((a.val i).val : F))) * J.form *
      Matrix.diagonal (fun i => ((a.val i).val : F)) = J.form
    rw [hJ, mul_one]
    have ha : J.conjTranspose (Matrix.diagonal (fun i => ((a.val i).val : F))) =
        Matrix.diagonal (fun i => J.conj ((a.val i).val : F)) := by
      ext i j
      by_cases h : i = j <;> simp [HermitianForm.conjTranspose, h, Ne.symm]
    rw [ha, diagonal_mul_diagonal]
    convert diagonal_one using 1
    congr 1
    funext i
    rw [hconj, ← pow_succ]
    exact (mem_rootsOfUnity' 5 (a.val i).val).mp (a.val i).property
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    change (Matrix.diagonal (fun i => ((a.val i).val : F))).det = 1
    rw [Matrix.det_diagonal]
    have hp : ∏ i, a.val i = 1 := a.property
    have ha := congrArg (fun u : rootsOfUnity 5 F => (u.val : F)) hp
    simpa using ha

def diagonal (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) : DiagonalCoordinates F →* J.specialSubgroup :=
  diagonalGL.codRestrict J.specialSubgroup (diagonalGL_mem J hJ hconj)

theorem diagonal_val (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (a : DiagonalCoordinates F) :
    (diagonal J hJ hconj a).val.val = Matrix.diagonal (fun i => ((a.val i).val : F)) := by rfl

theorem diagonal_injective (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) : Function.Injective (diagonal J hJ hconj) := by
  intro a b hab
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Units.ext
  simpa only [diagonal_val, Matrix.diagonal_apply_eq] using congrArg (fun A : J.specialSubgroup => A.val.val i i) hab

abbrev torus (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) : Subgroup J.specialSubgroup :=
  (diagonal J hJ hconj).range

theorem card_torus [Finite F] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (hF : Nat.card F = 16) :
    Nat.card (torus J hJ hconj) = 5^4 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (diagonal_injective J hJ hconj)).toEquiv,
    ← Nat.card_congr (coordinatesEquiv (rootsOfUnity 5 F)).toEquiv,
    Nat.card_fun, Nat.card_fin]
  rw [FiniteField.card_rootsOfUnity_of_dvd F 5 (by rw [hF]; norm_num)]

private def permutationGL : Equiv.Perm (Fin 5) →* GL (Fin 5) F :=
  (Matrix.permMatrixHom (R := F)).toHomUnits

private theorem permutationGL_val (σ : Equiv.Perm (Fin 5)) :
    (permutationGL (F := F) σ).val = (1 : Matrix (Fin 5) (Fin 5) F).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id := by
  change (σ⁻¹).permMatrix F = _
  ext i j
  simp [Equiv.Perm.permMatrix, Matrix.submatrix, Matrix.one_apply]

def permutation [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1) :
    Equiv.Perm (Fin 5) →* J.specialSubgroup :=
  (permutationGL (F := F)).codRestrict J.specialSubgroup (by
    intro σ
    rw [J.mem_specialSubgroup_iff]
    constructor
    · change J.conjTranspose (permutationGL σ).val * J.form * (permutationGL σ).val = J.form
      rw [hJ, mul_one, permutationGL_val]
      have ha : J.conjTranspose ((1 : Matrix (Fin 5) (Fin 5) F).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id) =
          (1 : Matrix (Fin 5) (Fin 5) F).submatrix id (σ⁻¹ : Equiv.Perm (Fin 5)) := by
        ext i j
        simp [HermitianForm.conjTranspose, Matrix.submatrix, Matrix.one_apply, eq_comm]
      rw [ha, Matrix.submatrix_mul_equiv, one_mul, Matrix.submatrix_id_id]
    · apply Units.ext
      rw [GeneralLinearGroup.val_det_apply]
      change ((σ⁻¹).permMatrix F).det = 1
      rw [Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h, CharTwo.neg_eq])

theorem permutation_val [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (σ : Equiv.Perm (Fin 5)) :
    (permutation J hJ σ).val.val =
      (1 : Matrix (Fin 5) (Fin 5) F).submatrix (σ⁻¹ : Equiv.Perm (Fin 5)) id :=
  permutationGL_val σ

theorem permutation_injective [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1) :
    Function.Injective (permutation J hJ) := by
  intro σ τ he
  apply inv_injective
  apply Equiv.ext
  intro i
  by_contra hi
  change σ.symm i ≠ τ.symm i at hi
  have hh := congrArg (fun A : J.specialSubgroup => A.val.val i (σ⁻¹ i)) he
  simp [permutation_val, Matrix.submatrix, Matrix.one_apply, hi, Ne.symm] at hh

theorem permutation_diagonal [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (σ : Equiv.Perm (Fin 5))
    (a : DiagonalCoordinates F) :
    permutation J hJ σ * diagonal J hJ hconj a * (permutation J hJ σ)⁻¹ =
      diagonal J hJ hconj (permute (rootsOfUnity 5 F) σ a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change (permutationGL σ).val * Matrix.diagonal (fun i => ((a.val i).val : F)) =
    Matrix.diagonal (fun i => (((permute (rootsOfUnity 5 F) σ a).val i).val : F)) *
      (permutationGL σ).val
  rw [permutationGL_val]
  ext i j
  simp only [mul_diagonal, diagonal_mul, Matrix.submatrix_apply, Matrix.one_apply, id_eq]
  by_cases h : σ.symm i = j
  · simp [h, permute]
  · simp [h]

theorem permutation_root [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (σ : Equiv.Perm (Fin 5))
    (i j : Fin 5) (u : rootsOfUnity 5 F) :
    permutation J hJ σ * diagonal J hJ hconj (root _ i j u) * (permutation J hJ σ)⁻¹ =
      diagonal J hJ hconj (root _ (σ i) (σ j) u) := by
  rw [permutation_diagonal, permute_root]

theorem permutation_mem_normalizer [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) (σ : Equiv.Perm (Fin 5)) :
    permutation J hJ σ ∈ normalizer (torus J hJ hconj : Set J.specialSubgroup) := by
  apply mem_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨permute _ σ a, (permutation_diagonal J hJ hconj σ a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨permute _ σ⁻¹ a, ?_⟩
    rw [← permutation_diagonal, ha, map_inv]
    group

private theorem pi_generates {C G : Type*} [CommGroup C] [Group G]
    (t : (Fin 4 → C) →* G) (u : C) (hu : ∀ a, a ∈ zpowers u) :
    closure (Set.range (fun i : Fin 4 => t (Pi.mulSingle i u))) = t.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro g ⟨a, rfl⟩
    have hs (i : Fin 4) : t (Pi.mulSingle i (a i)) ∈
        closure (Set.range (fun i : Fin 4 => t (Pi.mulSingle i u))) := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hu (a i))
      rw [← hk, Pi.mulSingle_zpow, map_zpow]
      exact zpow_mem (subset_closure (Set.mem_range_self i)) _
    rw [← Finset.univ_prod_mulSingle a]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul]
    exact mul_mem (hs 0) (mul_mem (hs 1) (mul_mem (hs 2) (hs 3)))

theorem torus_preimage_commutative [Finite F] [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    {E : Type*} [Group E] (f : E →* J.specialSubgroup) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) :
    IsMulCommutative ((torus J hJ hconj).comap f) := by
  let C := rootsOfUnity 5 F
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := C)
  let t : (Fin 4 → C) →* J.specialSubgroup :=
    (diagonal J hJ hconj).comp (coordinatesEquiv C).toMonoidHom
  have hgen : closure (Set.range (fun i : Fin 4 => t (Pi.mulSingle i u))) =
      torus J hJ hconj := by
    rw [pi_generates t u hu, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (coordinatesEquiv C).surjective, ← MonoidHom.range_eq_map]
  have hroot (i : Fin 4) : t (Pi.mulSingle i u) =
      diagonal J hJ hconj (root C i.succ 0 u) := by
    dsimp only [t, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [coordinatesEquiv_single]
  apply PerfectCentralCovering.isMulCommutative_comap_of_swapped_generators
    f hf hk (torus J hJ hconj) (fun i => t (Pi.mulSingle i u)) hgen
    (fun i j => (Commute.all _ _).map t) ?_ (by decide : Nat.Coprime 5 2) ?_
  · intro i j hij
    refine ⟨permutation J hJ (Equiv.swap i.succ j.succ), ?_, ?_⟩ <;>
      rw [hroot, hroot, permutation_root] <;>
      simp [C, Equiv.swap_apply_of_ne_of_ne, Fin.succ_ne_zero, Ne.symm]
  · intro i
    rw [← map_pow, ← Pi.mulSingle_pow]
    have hu5 : u^5 = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact (mem_rootsOfUnity' 5 u.val).mp u.property
    simp [hu5]

abbrev cycle [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1) :
    J.specialSubgroup := permutation J hJ (finRotate 5)

abbrev monomial [CharP F 2] (J : HermitianForm 5 F) (hJ : J.form = 1)
    (hconj : ∀ x, J.conj x = x^4) : Subgroup J.specialSubgroup :=
  torus J hJ hconj ⊔ zpowers (cycle J hJ)

/-- A section of the actual diagonal torus compatible with every lift of every
coordinate permutation. The existence of this section remains to be proved. -/
@[expose] def HasPermutationTorusLift [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    {E : Type*} [Group E] (d : PerfectCentralCovering.Cover E J.specialSubgroup) : Prop :=
  ∃ s : DiagonalCoordinates F →* E,
    d.toMonoidHom.comp s = diagonal J hJ hconj ∧
    ∀ (σ : Equiv.Perm (Fin 5)) (b : E), d.toMonoidHom b = permutation J hJ σ →
      ∀ a, b * s a * b⁻¹ = s (permute _ σ a)

theorem torus_preimage_commutative_of_card [Finite F]
    (J : HermitianForm 5 F) (hJ : J.form = 1) (hconj : ∀ x, J.conj x = x^4)
    (hF : Nat.card F = 16) {E : Type*} [Group E]
    (d : PerfectCentralCovering.Cover E J.specialSubgroup) :
    IsMulCommutative ((torus J hJ hconj).comap d.toMonoidHom) := by
  let : CharP F 2 := Theory.SpecificGroups.UnitaryFive.charP_two_of_card_sixteen hF
  exact torus_preimage_commutative J hJ hconj d.toMonoidHom d.surjective d.ker_le_center

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Five
