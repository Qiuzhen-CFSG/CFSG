module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality.PlaneRoots
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent

/-!
# The full point radical on the twisted symplectic tensor

The point tensor space is the image of the tensor product of the actual point
inclusions. It has defining-field dimension one. In matrix coordinates the two
short-root families (u,0,0) and (0,v,0), using 1 and a scalar moved by the twist,
force every entry except (e₀,e₀) to vanish. This proves the fixed-space theorem
for the whole point radical. Actual scalar descent gives binary fixed dimension
s and codimension 15s through the published tensor identification.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
The analogous assertion for all subgroups of rank greater than 2n is false;
`PointRoots.RankObstruction` gives a checked counterexample. No subgroup
fixed-space equality is inferred from root intersection alone here.
-/

@[expose] public section
open scoped Matrix TensorProduct
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
noncomputable def pointTensorSpace : Submodule F (Vector F ⊗[F] Vector F) :=
  LinearMap.range (TensorProduct.map (point F).subtype (point F).subtype)
omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
theorem pointTensorSpace_finrank : Module.finrank F (pointTensorSpace (F := F)) = 1 := by
  rw [pointTensorSpace, LinearMap.finrank_range_of_inj
    (TensorProduct.map_injective_of_flat_flat _ _ (point F).subtype_injective
      (point F).subtype_injective), Module.finrank_tensorProduct, finrank_point]

private lemma twist_pair_zero (σ : F ≃+* F) (t : F) (ht : σ t ≠ t)
    (a b : F) (h1 : a + b = 0) (h2 : t*a + σ t*b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    have hh : (σ t - t) * b = 0 := by linear_combination h2 - t*h1
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ht)
  exact ⟨by simpa [hb] using h1, hb⟩

private lemma point_matrix_fixed (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    (X : Mat (F := F))
    (h : ∀ g : SymplecticConjugatePair.pointRadical (F := F), matrixAction σ g.val X = X) :
    X = X (.inl 0) (.inl 0) • Matrix.single (.inl 0) (.inl 0) 1 := by
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra! hn
    apply hne
    ext t
    exact hn t
  have hu (c : F) := h ⟨(pointRadicalElement c 0 0).val,
    (mem_pointRadical_iff _).mpr ⟨c, 0, 0, rfl⟩⟩
  have hv (c : F) := h ⟨(pointRadicalElement 0 c 0).val,
    (mem_pointRadical_iff _).mpr ⟨0, c, 0, rfl⟩⟩
  have h22 : X (.inr 0) (.inr 0) = 0 := by
    simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using congrArg (fun M => M (.inl 1) (.inr 0)) (hu 1)
  have h23 : X (.inr 0) (.inr 1) = 0 := by
    simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using congrArg (fun M => M (.inl 1) (.inr 1)) (hu 1)
  have h32 : X (.inr 1) (.inr 0) = 0 := by
    simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using congrArg (fun M => M (.inl 0) (.inr 0)) (hu 1)
  have h33 : X (.inr 1) (.inr 1) = 0 := by
    simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using congrArg (fun M => M (.inl 0) (.inr 1)) (hu 1)
  have h30_03 : X (.inr 1) (.inl 0) = 0 ∧ X (.inl 0) (.inr 1) = 0 := by
    apply twist_pair_zero σ t ht
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h33, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 0)) (hu 1)
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h33, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 0)) (hu t)
  have h31_02 : X (.inr 1) (.inl 1) = 0 ∧ X (.inl 0) (.inr 0) = 0 := by
    apply twist_pair_zero σ t ht
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h32, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 1)) (hu 1)
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h32, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 1)) (hu t)
  have h20_13 : X (.inr 0) (.inl 0) = 0 ∧ X (.inl 1) (.inr 1) = 0 := by
    apply twist_pair_zero σ t ht
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h23, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 1) (.inl 0)) (hu 1)
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h23, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 1) (.inl 0)) (hu t)
  have h21_12 : X (.inr 0) (.inl 1) = 0 ∧ X (.inl 1) (.inr 0) = 0 := by
    apply twist_pair_zero σ t ht
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h22, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 1) (.inl 1)) (hu 1)
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h22, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 1) (.inl 1)) (hu t)
  have h11 : X (.inl 1) (.inl 1) = 0 := by
    simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] using congrArg (fun M => M (.inl 0) (.inl 1)) (hv 1)
  have h10_01 : X (.inl 1) (.inl 0) = 0 ∧ X (.inl 0) (.inl 1) = 0 := by
    apply twist_pair_zero σ t ht
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h11, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 0)) (hv 1)
    · simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h11, add_assoc, mul_comm] using
        congrArg (fun M => M (.inl 0) (.inl 0)) (hv t)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single, h22, h23, h32, h33, h30_03.1, h30_03.2,
      h31_02.1, h31_02.2, h20_13.1, h20_13.2, h21_12.1, h21_12.2,
      h11, h10_01.1, h10_01.2]

lemma pointTensorSpace_eq_span : pointTensorSpace (F := F) = F ∙ (e 0 ⊗ₜ[F] e 0) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | tmul a b =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a.property
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp b.property
      rw [TensorProduct.map_tmul]
      change a.val ⊗ₜ[F] b.val ∈ _
      rw [← hc, ← hd, TensorProduct.smul_tmul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    intro w hw
    have he : w = e (F := F) 0 ⊗ₜ[F] e 0 := Set.mem_singleton_iff.mp hw
    subst w
    exact ⟨(⟨e 0, Submodule.mem_span_singleton_self _⟩ : point F) ⊗ₜ[F]
      (⟨e 0, Submodule.mem_span_singleton_self _⟩ : point F), rfl⟩

lemma pointTensorSpace_le_invariants (σ : F ≃+* F) :
    pointTensorSpace (F := F) ≤ Representation.invariants
      ((twistedTensor σ).comp SymplecticConjugatePair.pointRadical.subtype) := by
  rw [pointTensorSpace_eq_span, Submodule.span_le]
  intro w hw g
  have he : w = e (F := F) 0 ⊗ₜ[F] e 0 := Set.mem_singleton_iff.mp hw
  subst w
  apply coordinates.injective
  change coordinates (twistedTensor σ g.val (e 0 ⊗ₜ[F] e 0)) = coordinates (e 0 ⊗ₜ[F] e 0)
  rw [coordinates_action, coordinates_tmul]
  obtain ⟨u,v,z,hg⟩ := (mem_pointRadical_iff g.val).mp g.property
  rw [← hg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.vecMulVec, Theory.SpecificGroups.SymplecticFour.e]

theorem point_tensor_invariants (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F) :
    Representation.invariants
      ((twistedTensor σ).comp SymplecticConjugatePair.pointRadical.subtype) =
      pointTensorSpace (F := F) := by
  apply le_antisymm ?_ (pointTensorSpace_le_invariants σ)
  intro w hw
  have hm := point_matrix_fixed σ hne (coordinates w) (fun g => by
    rw [← coordinates_action]
    exact congrArg coordinates (hw g))
  rw [pointTensorSpace_eq_span]
  apply Submodule.mem_span_singleton.mpr
  refine ⟨coordinates w (.inl 0) (.inl 0), ?_⟩
  apply coordinates.injective
  rw [map_smul, coordinates_tmul]
  have he : Matrix.vecMulVec (e (F := F) 0) (e 0) = Matrix.single (.inl 0) (.inl 0) 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec, Matrix.single, Theory.SpecificGroups.SymplecticFour.e]
  rw [he]
  exact hm.symm

theorem point_tensor_fixed_finrank (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F) :
    Module.finrank F (Representation.invariants
      ((twistedTensor σ).comp SymplecticConjugatePair.pointRadical.subtype)) = 1 := by
  rw [point_tensor_invariants σ hne, pointTensorSpace_finrank]

lemma pointTensorSpace_le_subgroup_invariants (σ : F ≃+* F)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical) :
    pointTensorSpace (F := F) ≤ Representation.invariants ((twistedTensor σ).comp A.subtype) :=
  fun _ hw a => pointTensorSpace_le_invariants σ hw ⟨a.val, hA a.property⟩

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- The complete point radical fixes one Schur-field dimension in the descended module. -/
theorem TensorIdentification.point_fixed_finrank {s : ℕ}
    (h : TensorIdentification ρ F s) :
    Module.finrank (ZMod 2) (fixedSpace ρ
      (SymplecticConjugatePair.pointRadical.map h.groupEquiv.symm.toMonoidHom)) = s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hne : h.sigma.toRingEquiv ≠ RingEquiv.refl F := by
    intro he
    apply h.sigma_ne
    ext t
    exact DFunLike.congr_fun he t
  rw [h.fixed_finrank ρ, TensorGeometry.Equality.point_tensor_fixed_finrank
    h.sigma.toRingEquiv hne, mul_one]

theorem TensorIdentification.point_fixedCodim {s : ℕ}
    (h : TensorIdentification ρ F s) :
    fixedCodim ρ (SymplecticConjugatePair.pointRadical.map
      h.groupEquiv.symm.toMonoidHom) = 15*s := by
  have hh := fixedCodim_add_finrank ρ
    (SymplecticConjugatePair.pointRadical.map h.groupEquiv.symm.toMonoidHom)
  rw [h.point_fixed_finrank ρ, h.binary_finrank] at hh
  omega

end CFSG.Quasithin.ChapterK.Symplectic
