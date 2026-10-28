module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.PointRoots

/-!
# Obstruction to the point-radical strict-rank fixed-space assertion

Write g(u,v,z) for the actual point-radical matrix. The tensor
w = e₀ ⊗ e₁ + e₁ ⊗ e₀ is fixed whenever σ(v)=v. Its fixer inside the
point radical contains all g(u,v,z) with arbitrary u,z and v in {0,1}.
These are 2|F|² distinct elements, so this elementary subgroup has binary rank
at least 2n+1 when |F|=2ⁿ. Nevertheless its invariants strictly contain the
point tensor space. It meets every subgroup of order |F| in the radical.
Thus taking an arbitrary nonidentity element from each contained root cannot
force the claimed one-dimensional fixed space.

The final theorem transports this obstruction through `TensorIdentification`:
there is an elementary actor of rank greater than 4s whose binary fixed
dimension exceeds s. This refutes the proposed intermediate strict-rank
contract. It does not refute K.3.4.2, whose actor also satisfies the small-ratio
hypothesis; excluding those actors requires a different estimate or additional
source hypotheses.

Source being checked: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

@[expose] public section
open scoped Matrix TensorProduct
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
noncomputable def crossMatrix : Mat (F := F) :=
  Matrix.single (.inl 0) (.inl 1) 1 + Matrix.single (.inl 1) (.inl 0) 1

lemma coordinates_symm_crossMatrix :
    coordinates.symm (crossMatrix (F := F)) = e 0 ⊗ₜ[F] e 1 + e 1 ⊗ₜ[F] e 0 := by
  apply coordinates.injective
  rw [LinearEquiv.apply_symm_apply, map_add, coordinates_tmul, coordinates_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, Matrix.single, Matrix.vecMulVec, Theory.SpecificGroups.SymplecticFour.e]

lemma crossMatrix_fixed (σ : F ≃+* F) (u v z : F) (hv : σ v = v) :
    matrixAction σ (pointRadicalElement u v z).val crossMatrix = crossMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMatrix, matrixAction, pointRadicalElement, pointRadicalMatrix,
      Matrix.mul_apply, Matrix.single, Fintype.sum_sum_type, Fin.sum_univ_two,
      hv, CharTwo.add_self_eq_zero]

noncomputable def matrixFixer (σ : F ≃+* F) (X : Mat (F := F)) : Subgroup (Sp F) where
  carrier := {g | matrixAction σ g X = X}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change matrixAction σ (a*b) X = X
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro g hg
    change matrixAction σ g⁻¹ X = X
    have hh := congrArg (matrixAction σ g⁻¹) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh.symm

noncomputable def largePointFixer (σ : F ≃+* F) : Subgroup (Sp F) :=
  SymplecticConjugatePair.pointRadical ⊓ matrixFixer σ crossMatrix

lemma largePointFixer_le (σ : F ≃+* F) :
    largePointFixer σ ≤ SymplecticConjugatePair.pointRadical := inf_le_left

noncomputable def largePointFixerInjection (σ : F ≃+* F) :
    (F × F) × Bool → largePointFixer σ := fun p =>
  ⟨(pointRadicalElement p.1.1 (if p.2 then 1 else 0) p.1.2).val,
    ⟨(mem_pointRadical_iff _).mpr ⟨_, _, _, rfl⟩,
      crossMatrix_fixed σ _ _ _ (by cases p.2 <;> simp)⟩⟩

lemma largePointFixerInjection_injective (σ : F ≃+* F) :
    Function.Injective (largePointFixerInjection σ) := by
  rintro ⟨⟨u,z⟩,b⟩ ⟨⟨u',z'⟩,b'⟩ he
  have hu := congrArg (fun g : largePointFixer σ => g.val.val (.inl 1) (.inr 0)) he
  have hz := congrArg (fun g : largePointFixer σ => g.val.val (.inl 0) (.inr 0)) he
  have hb := congrArg (fun g : largePointFixer σ => g.val.val (.inr 1) (.inr 0)) he
  change u = u' at hu
  change z = z' at hz
  have hbb : b = b' := by
    cases b <;> cases b' <;> simp_all [largePointFixerInjection, pointRadicalElement,
      pointRadicalMatrix]
  exact Prod.ext (Prod.ext hu hz) hbb

lemma largePointFixer_rank {n : ℕ} (hF : Nat.card F = 2^n) (σ : F ≃+* F) :
    2*n < rank (largePointFixer σ) := by
  have hc := Nat.card_le_card_of_injective _ (largePointFixerInjection_injective σ)
  have hb : 2^(2*n+1) ≤ Nat.card (largePointFixer σ) := by
    simpa [Nat.card_prod, hF, pow_add, pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc, pow_two] using hc
  have hl := Nat.le_log_of_pow_le (by decide : 1 < 2) hb
  change 2*n+1 ≤ rank (largePointFixer σ) at hl
  omega

lemma pointTensorSpace_coordinate_zero (w : pointTensorSpace (F := F)) :
    coordinates w.val (.inl 0) (.inl 1) = 0 := by
  obtain ⟨t, ht⟩ := w.property
  rw [← ht]
  clear ht w
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | tmul a b =>
    rw [TensorProduct.map_tmul, coordinates_tmul]
    have hb := (mem_point_iff b.val).mp b.property
    simp [Matrix.vecMulVec, hb.1]

lemma crossTensor_not_mem_pointTensorSpace :
    coordinates.symm (crossMatrix (F := F)) ∉ pointTensorSpace := by
  intro hw
  have he := pointTensorSpace_coordinate_zero ⟨_, hw⟩
  rw [LinearEquiv.apply_symm_apply] at he
  simp [crossMatrix, Matrix.single] at he

lemma crossTensor_invariant (σ : F ≃+* F) :
    coordinates.symm (crossMatrix (F := F)) ∈
      Representation.invariants ((twistedTensor σ).comp (largePointFixer σ).subtype) := by
  intro g
  apply coordinates.injective
  change coordinates (twistedTensor σ g.val (coordinates.symm crossMatrix)) = _
  rw [coordinates_action, LinearEquiv.apply_symm_apply]
  exact g.property.2

lemma largePointFixer_invariants_ne (σ : F ≃+* F) :
    Representation.invariants ((twistedTensor σ).comp (largePointFixer σ).subtype) ≠
      pointTensorSpace := by
  intro he
  exact crossTensor_not_mem_pointTensorSpace (he ▸ crossTensor_invariant σ)

/-- A large elementary subgroup fixing an extra tensor. In particular, strict
rank above 2n alone does not give the full point radical's fixed space. -/
theorem largePointFixer_counterexample {n : ℕ} (hF : Nat.card F = 2^n)
    (σ : F ≃+* F) :
    largePointFixer σ ≤ SymplecticConjugatePair.pointRadical ∧
      IsElementaryTwo (largePointFixer σ) ∧ 2*n < rank (largePointFixer σ) ∧
      1 < Module.finrank F (Representation.invariants
        ((twistedTensor σ).comp (largePointFixer σ).subtype)) := by
  have hr := largePointFixer_rank hF σ
  have hA : largePointFixer σ ≠ ⊥ := by intro he; simp [he] at hr
  have hY : SymplecticConjugatePair.pointRadical (F := F) ≠ ⊥ := by
    intro he
    exact hA (le_bot_iff.mp (he ▸ largePointFixer_le σ))
  refine ⟨largePointFixer_le σ,
    (IsElementaryTwo.of_le ⟨hY, pointRadical_elementary⟩ (largePointFixer_le σ) hA), hr, ?_⟩
  have hlt := Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne (pointTensorSpace_le_subgroup_invariants σ (largePointFixer_le σ))
      (largePointFixer_invariants_ne σ).symm)
  rwa [pointTensorSpace_finrank] at hlt

/-- The counterexample meets every subgroup of field order in the radical,
hence in particular every literal root contained in the radical. -/
theorem largePointFixer_meets_roots {n : ℕ} (hF : Nat.card F = 2^n)
    (σ : F ≃+* F) (R : Subgroup (Sp F)) (hR : Nat.card R = Nat.card F)
    (hRY : R ≤ SymplecticConjugatePair.pointRadical) : largePointFixer σ ⊓ R ≠ ⊥ :=
  radical_root_intersection hF (largePointFixer_le σ) card_pointRadical hR hRY
    (largePointFixer_rank hF σ)
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- The invalid strict-rank fixed-dimension contract also fails after actual
Galois descent, with the literal subgroup transport from the task statement. -/
theorem TensorIdentification.exists_point_subgroup_fixed_finrank_gt {s : ℕ}
    (h : TensorIdentification ρ F s) (hs : 0 < s) :
    ∃ A : Subgroup (Sp F), A ≤ SymplecticConjugatePair.pointRadical ∧
      IsElementaryTwo A ∧ 4*s < rank A ∧ s < Module.finrank (ZMod 2)
        (fixedSpace ρ (A.map h.groupEquiv.symm.toMonoidHom)) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hA, he, hr, hf⟩ := TensorGeometry.Equality.largePointFixer_counterexample
    h.field_card h.sigma.toRingEquiv
  refine ⟨_, hA, he, by omega, ?_⟩
  rw [h.fixed_finrank ρ]
  simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left hf hs
end CFSG.Quasithin.ChapterK.Symplectic
