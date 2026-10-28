module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The actual diagonal-and-swap subgroup of GL2

A unit ζ defines two diagonal matrices and the coordinate-swap involution.
Their actual generated subgroup has cardinality 2*(orderOf ζ)^2. The
definitions expose the matrix entries for determinant and Hermitian-form
membership checks in the linear and unitary models.

The diagonal base is an injective image of zpowers(ζ) × zpowers(ζ). Its
generators give the two diagonal matrices. The coordinate swap interchanges
the two entries, hence normalizes the base, and its off-diagonal entry
shows it lies outside. The external-involution cardinality theorem then
counts the join. No field finiteness or source-group recognition is assumed.

These shared matrix calculations underlie ABG II.2 Lemma1(i),(ii), article
p17. Source-facing wreathed presentations and Sylow maximality are proved
by their separate consumers.
-/

namespace Matrix.GeneralLinearGroup
open scoped Matrix
variable (F : Type*) [Field F]

@[expose] public def diagonalPair : Fˣ × Fˣ →* GL (Fin 2) F where
  toFun a :=
    { val := !![(a.1 : F), 0; 0, (a.2 : F)]
      inv := !![((a.1⁻¹ : Fˣ) : F), 0; 0, ((a.2⁻¹ : Fˣ) : F)]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

public theorem diagonalPair_val (a b : Fˣ) :
    (diagonalPair F (a, b)).val = !![(a : F), 0; 0, (b : F)] := rfl

public theorem diagonalPair_injective : Function.Injective (diagonalPair F) := by
  intro a b h
  apply Prod.ext
  · exact Units.ext (congrArg (fun A : GL (Fin 2) F => A.val 0 0) h)
  · exact Units.ext (congrArg (fun A : GL (Fin 2) F => A.val 1 1) h)

@[expose] public def coordinateSwap : GL (Fin 2) F where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

public theorem coordinateSwap_val : (coordinateSwap F).val = !![0, 1; 1, 0] := rfl

@[simp] public theorem coordinateSwap_inv : (coordinateSwap F)⁻¹ = coordinateSwap F := by
  apply Units.ext
  rfl

@[simp] public theorem coordinateSwap_sq : coordinateSwap F ^ 2 = 1 := by
  rw [pow_two, ← coordinateSwap_inv F]
  exact inv_mul_cancel _

public theorem coordinateSwap_conj_diagonalPair (a b : Fˣ) :
    coordinateSwap F * diagonalPair F (a, b) * (coordinateSwap F)⁻¹ =
      diagonalPair F (b, a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalPair, coordinateSwap, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] public def diagonalSwapSubgroup (ζ : Fˣ) : Subgroup (GL (Fin 2) F) :=
  Subgroup.closure {diagonalPair F (ζ, 1), diagonalPair F (1, ζ), coordinateSwap F}

private def baseHom (ζ : Fˣ) : Subgroup.zpowers ζ × Subgroup.zpowers ζ →* GL (Fin 2) F :=
  (diagonalPair F).comp ((Subgroup.zpowers ζ).subtype.prodMap (Subgroup.zpowers ζ).subtype)

private theorem baseHom_injective (ζ : Fˣ) : Function.Injective (baseHom F ζ) := by
  intro a b h
  have hh := diagonalPair_injective F h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))

private theorem baseHom_range_eq (ζ : Fˣ) :
    (baseHom F ζ).range = Subgroup.closure {diagonalPair F (ζ, 1), diagonalPair F (1, ζ)} := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨i, hi⟩ := a.property
    obtain ⟨j, hj⟩ := b.property
    have hprod : baseHom F ζ (a,b) = diagonalPair F (ζ,1) ^ i * diagonalPair F (1,ζ) ^ j := by
      change diagonalPair F (a.val, b.val) = _
      rw [← map_zpow, ← map_zpow, ← map_mul]
      apply congrArg (diagonalPair F)
      ext <;> simp [hi, hj]
    rw [hprod]
    exact Subgroup.mul_mem _
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j)
  · rw [Subgroup.closure_le]
    intro x hx
    rcases (by simpa using hx : x = diagonalPair F (ζ,1) ∨ x = diagonalPair F (1,ζ)) with rfl | rfl
    · exact ⟨(⟨ζ, Subgroup.mem_zpowers ζ⟩, 1), rfl⟩
    · exact ⟨(1, ⟨ζ, Subgroup.mem_zpowers ζ⟩), rfl⟩

private theorem swap_not_mem_base (ζ : Fˣ) : coordinateSwap F ∉ (baseHom F ζ).range := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun A : GL (Fin 2) F => A.val 0 1) ha
  exact zero_ne_one h

private theorem swap_mem_normalizer_base (ζ : Fˣ) :
    coordinateSwap F ∈ Subgroup.normalizer (baseHom F ζ).range := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro A
  constructor
  · rintro ⟨⟨a,b⟩, rfl⟩
    exact ⟨(b,a), (coordinateSwap_conj_diagonalPair F a b).symm⟩
  · intro h
    obtain ⟨⟨a,b⟩, hab⟩ := h
    refine ⟨(b,a), ?_⟩
    have hh := congrArg (fun B : GL (Fin 2) F => coordinateSwap F * B * (coordinateSwap F)⁻¹) hab
    change coordinateSwap F * diagonalPair F (a,b) * (coordinateSwap F)⁻¹ =
      coordinateSwap F * (coordinateSwap F * A * (coordinateSwap F)⁻¹) * (coordinateSwap F)⁻¹ at hh
    rw [coordinateSwap_conj_diagonalPair] at hh
    have hww : coordinateSwap F * coordinateSwap F = 1 := by
      simpa only [pow_two] using coordinateSwap_sq F
    change diagonalPair F (b,a) = A
    calc
      _ = coordinateSwap F * (coordinateSwap F * A * (coordinateSwap F)⁻¹) * (coordinateSwap F)⁻¹ := hh
      _ = (coordinateSwap F * coordinateSwap F) * A * (coordinateSwap F * coordinateSwap F)⁻¹ := by group
      _ = A := by rw [hww]; simp

public theorem diagonalSwapSubgroup_card (ζ : Fˣ) :
    Nat.card (diagonalSwapSubgroup F ζ) = 2 * orderOf ζ ^ 2 := by
  have heq : diagonalSwapSubgroup F ζ = (baseHom F ζ).range ⊔ Subgroup.zpowers (coordinateSwap F) := by
    unfold diagonalSwapSubgroup
    rw [baseHom_range_eq, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [heq, Subgroup.card_sup_zpowers_of_normalizing_involution _ _
    (coordinateSwap_sq F) (swap_not_mem_base F ζ) (swap_mem_normalizer_base F ζ)]
  rw [← Nat.card_congr (MonoidHom.ofInjective (baseHom_injective F ζ)).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ← pow_two]

end Matrix.GeneralLinearGroup

