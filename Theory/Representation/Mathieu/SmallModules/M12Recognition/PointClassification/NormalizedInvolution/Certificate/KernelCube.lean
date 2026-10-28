module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.NormReduction

/-!
# The cube of the binary M₁₁ point annihilator

The certified adapted coordinates have three upper triangular layers, each
consisting of ten copies of the actual point module. Lift vectors supported in
the first n layers to the literal group algebra modulo `elevenIdeal`.

Generator compatibility, A/B generation, and linearity show that every algebra
element preserves these lifted layers and acts on each successive layer by its
point-representation image. A reference-kernel element therefore lowers the
filtration. Three such elements annihilate the lifted class of 1, proving that
their product belongs to the norm ideal.

Only congruences in the actual two-sided ideal are used: the candidate matrices
need not be assumed to define a group representation. The two independent
certificates supply the literal quotient lift and its augmentation layers.

Source application: the James input to Aschbacher–Smith G.7.3(2), printed
p.348/PDF p.359, citing James, J. Algebra 27 (1973), 57–111.
-/

public section

open scoped BigOperators MonoidAlgebra
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
namespace CertificateCube
open CertificateData CertificateFiltration

private def coordinateEquiv : (Fin 3 × Fin 10 × Fin 10) ≃ Fin 300 where
  toFun i := coordinate i.1 i.2.1 i.2.2
  invFun i := (⟨i.val / 100, by omega⟩,
    ⟨i.val % 100 / 10, by omega⟩, ⟨i.val % 10, by omega⟩)
  left_inv := by
    rintro ⟨a, b, c⟩
    dsimp [coordinate]
    congr 1
    · apply Fin.ext; dsimp; omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  right_inv i := by apply Fin.ext; dsimp [coordinate]; omega

private theorem sum_coordinates (f : Fin 300 → ZMod 2) :
    ∑ i, f i = ∑ a : Fin 3, ∑ b : Fin 10, ∑ c : Fin 10, f (coordinate a b c) := by
  have h := (Equiv.sum_comp coordinateEquiv f).symm
  change (∑ i, f i) = ∑ i : Fin 3 × Fin 10 × Fin 10,
    f (coordinate i.1 i.2.1 i.2.2) at h
  simpa only [Fintype.sum_prod_type] using h

private def Supported (n : ℕ) (v : Space) : Prop :=
  ∀ i, 100 * n ≤ i.val → v i = 0

private def slice (v : Space) (a : Fin 3) (b : Fin 10) : Fin 10 → ZMod 2 :=
  fun c => v (coordinate a b c)

private theorem transformed_supported (s : Fin 2) (n : ℕ) (v : Space)
    (hv : Supported n v) : Supported n ((transformedMatrix s).mulVec v) := by
  intro i hi
  change ∑ j, transformedMatrix s i j * v j = 0
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : 100 * n ≤ j.val
  · rw [hv j hj, mul_zero]
  · rw [lower_blocks s i j (by omega), zero_mul]

private theorem transformed_slice (s : Fin 2) (a : Fin 3) (b : Fin 10)
    (v : Space) (hv : Supported (a.val + 1) v) :
    slice ((transformedMatrix s).mulVec v) a b =
      (augmentationMatrix (generator s)).mulVec (slice v a b) := by
  ext r
  change (∑ j, transformedMatrix s (coordinate a b r) j * v j) = _
  rw [sum_coordinates]
  rw [Finset.sum_eq_single a]
  · simp only [diagonal_blocks]
    rw [Finset.sum_eq_single b]
    · simp only [↓reduceIte]
      rfl
    · intro c _ hc
      simp only [if_neg (Ne.symm hc), zero_mul, Finset.sum_const_zero]
    · simp
  · intro c _ hc
    apply Finset.sum_eq_zero
    intro d _
    apply Finset.sum_eq_zero
    intro j _
    rcases lt_or_gt_of_ne (show c.val ≠ a.val from fun h => hc (Fin.ext h)) with h | h
    · rw [lower_blocks s _ _ (by dsimp [coordinate]; omega), zero_mul]
    · rw [hv _ (by dsimp [coordinate]; omega), mul_zero]
  · simp

local notation "R" => (ZMod 2)[M11]

private noncomputable def adaptedLift (v : Space) : R := lift (adaptedCoordinates v)

private theorem adaptedLift_add (v w : Space) :
    adaptedLift (v + w) = adaptedLift v + adaptedLift w := by
  simp only [adaptedLift, map_add]

private theorem adaptedLift_smul (c : ZMod 2) (v : Space) :
    adaptedLift (c • v) = c • adaptedLift v := by
  simp only [adaptedLift, map_smul]

private theorem adaptedLift_zero : adaptedLift 0 = 0 := by
  simp only [adaptedLift, map_zero]

-- Witnesses are kept modulo the ideal, so no relations for a candidate
-- representation on the 300-dimensional coordinate space are needed.
private def Compatible (x : R) : Prop :=
  ∀ (a : Fin 3) (v : Space), Supported (a.val + 1) v →
    ∃ w : Space, Supported (a.val + 1) w ∧
      (∀ b : Fin 10, pointCoordinates (slice w a b) =
        pointRepresentation.asAlgebraHom x (pointCoordinates (slice v a b))) ∧
      x * adaptedLift v - adaptedLift w ∈ elevenIdeal

private theorem compatible_one : Compatible 1 := by
  intro a v hv
  refine ⟨v, hv, ?_, ?_⟩
  · intro b
    simp only [map_one, Module.End.one_apply]
  · simpa only [one_mul, sub_self] using elevenIdeal.zero_mem

private theorem compatible_generator (s : Fin 2) :
    Compatible (MonoidAlgebra.single (generator s) 1) := by
  intro a v hv
  refine ⟨(transformedMatrix s).mulVec v, transformed_supported s _ v hv, ?_, ?_⟩
  · intro b
    rw [transformed_slice s a b v hv, pointCoordinates_equivariant,
      Representation.asAlgebraHom_single_one]
  · simp only [adaptedLift]
    rw [← adaptedCoordinates_intertwines]
    have h := NormReduction.generator_lift_sub_mem s (adaptedCoordinates v)
    -- Keep the large certificate maps abstract during coercion normalization.
    generalize hl : lift = L at h ⊢
    generalize he : adaptedCoordinates = E at h ⊢
    exact h

private theorem compatible_mul {x y : R} (hx : Compatible x) (hy : Compatible y) :
    Compatible (x * y) := by
  intro a v hv
  obtain ⟨w, hw, hd, hI⟩ := hy a v hv
  obtain ⟨u, hu, he, hJ⟩ := hx a w hw
  refine ⟨u, hu, ?_, ?_⟩
  · intro b
    rw [he b, hd b, map_mul, Module.End.mul_apply]
  · have h : x * y * adaptedLift v - adaptedLift u =
        x * (y * adaptedLift v - adaptedLift w) +
        (x * adaptedLift w - adaptedLift u) := by
      simp only [mul_sub, mul_assoc]
      abel
    rw [h]
    exact elevenIdeal.add_mem (elevenIdeal.mul_mem_left x _ hI) hJ

private theorem compatible_add {x y : R} (hx : Compatible x) (hy : Compatible y) :
    Compatible (x + y) := by
  intro a v hv
  obtain ⟨w, hw, hd, hI⟩ := hx a v hv
  obtain ⟨u, hu, he, hJ⟩ := hy a v hv
  refine ⟨w + u, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.add_apply, hw i hi, hu i hi, add_zero]
  · intro b
    change pointCoordinates (slice w a b + slice u a b) = _
    rw [map_add, hd b, he b, map_add, LinearMap.add_apply]
  · rw [adaptedLift_add, add_mul, show x * adaptedLift v + y * adaptedLift v -
        (adaptedLift w + adaptedLift u) =
        (x * adaptedLift v - adaptedLift w) + (y * adaptedLift v - adaptedLift u) by abel]
    exact elevenIdeal.add_mem hI hJ

private theorem compatible_smul (c : ZMod 2) {x : R} (hx : Compatible x) :
    Compatible (c • x) := by
  intro a v hv
  obtain ⟨w, hw, hd, hI⟩ := hx a v hv
  refine ⟨c • w, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.smul_apply, hw i hi, smul_zero]
  · intro b
    change pointCoordinates (c • slice w a b) = _
    rw [map_smul, hd b, map_smul, LinearMap.smul_apply]
  · rw [adaptedLift_smul, smul_mul_assoc, ← smul_sub]
    exact NormReduction.smul_mem_elevenIdeal c hI

private theorem generators_monoid_closure :
    Submonoid.closure (Set.range generator) = ⊤ := by
  have hr : Set.range generator = {m11GeneratorAInM11, m11GeneratorBInM11} := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      fin_cases s <;> simp [generator]
    · intro hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨0, by simp [generator]⟩
      · obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, by simp [generator]⟩
  rw [hr, ← Subgroup.closure_toSubmonoid_of_finite, m11_generators_closure_eq_top]
  rfl

private theorem compatible_single (g : M11) :
    Compatible (MonoidAlgebra.single g 1) := by
  apply Submonoid.induction_of_closure_eq_top_left
    (motive := fun g => Compatible (MonoidAlgebra.single g 1)) generators_monoid_closure g
  · simpa only [← MonoidAlgebra.one_def] using compatible_one
  · rintro _ ⟨s, rfl⟩ y hy
    simpa only [MonoidAlgebra.single_mul_single, one_mul] using
      compatible_mul (compatible_generator s) hy

private theorem compatible_all (x : R) : Compatible x := by
  induction x using MonoidAlgebra.induction_on with
  | of g => exact compatible_single g
  | add x y hx hy => exact compatible_add hx hy
  | smul c x hx => exact compatible_smul c hx

private def InLayer (n : ℕ) (x : R) : Prop :=
  ∃ v : Space, Supported n v ∧ x - adaptedLift v ∈ elevenIdeal

private theorem inLayer_three (x : R) : InLayer 3 x := by
  obtain ⟨v, hv⟩ := NormReduction.exists_lift x
  refine ⟨adaptedCoordinates.symm v, ?_, ?_⟩
  · intro i hi
    omega
  · simpa only [adaptedLift, LinearEquiv.apply_symm_apply] using hv

private theorem supported_lower (a : Fin 3) (v : Space)
    (hv : Supported (a.val + 1) v) (hz : ∀ b, pointCoordinates (slice v a b) = 0) :
    Supported a.val v := by
  intro i hi
  by_cases h : 100 * (a.val + 1) ≤ i.val
  · exact hv i h
  · let b : Fin 10 := ⟨i.val % 100 / 10, by omega⟩
    let r : Fin 10 := ⟨i.val % 10, by omega⟩
    have he : coordinate a b r = i := by
      apply Fin.ext
      dsimp [coordinate, b, r]
      omega
    have hv0 : slice v a b = 0 := pointCoordinates.injective (by
      rw [hz b, map_zero])
    have hc := congrFun hv0 r
    simpa only [slice, he, Pi.zero_apply] using hc

private theorem kernel_lowers {x : R} (hx : x ∈ referenceKernel)
    (a : Fin 3) {y : R} (hy : InLayer (a.val + 1) y) : InLayer a.val (x * y) := by
  obtain ⟨v, hv, hI⟩ := hy
  obtain ⟨w, hw, hd, hJ⟩ := compatible_all x a v hv
  have hx0 : pointRepresentation.asAlgebraHom x = 0 := hx
  refine ⟨w, supported_lower a w hw ?_, ?_⟩
  · intro b
    rw [hd b, hx0, LinearMap.zero_apply]
  · have h : x * y - adaptedLift w =
        x * (y - adaptedLift v) + (x * adaptedLift v - adaptedLift w) := by
      rw [mul_sub]
      abel
    rw [h]
    exact elevenIdeal.add_mem (elevenIdeal.mul_mem_left x _ hI) hJ

private theorem inLayer_zero {x : R} (hx : InLayer 0 x) : x ∈ elevenIdeal := by
  obtain ⟨v, hv, hx⟩ := hx
  have hv0 : v = 0 := by ext i; exact hv i (by omega)
  simpa only [hv0, adaptedLift_zero, sub_zero] using hx

private theorem kernel_cube (x y z : R) (hx : x ∈ referenceKernel)
    (hy : y ∈ referenceKernel) (hz : z ∈ referenceKernel) :
    x * y * z ∈ elevenIdeal := by
  have h₂ : InLayer 2 z := by
    have h : InLayer 2 (z * 1) := kernel_lowers hz ⟨2, by decide⟩ (inLayer_three 1)
    simpa only [mul_one] using h
  have h₁ : InLayer 1 (y * z) := kernel_lowers hy ⟨1, by decide⟩ h₂
  have h₀ : InLayer 0 (x * (y * z)) := kernel_lowers hx ⟨0, by decide⟩ h₁
  simpa only [mul_assoc] using inLayer_zero h₀

end CertificateCube

/-- Every product of three elements annihilating the actual binary point
module lies in the two-sided ideal generated by the marked eleven-norm. -/
theorem referenceKernel_cube_le_elevenIdeal :
    ∀ x ∈ referenceKernel, ∀ y ∈ referenceKernel, ∀ z ∈ referenceKernel,
      x * y * z ∈ elevenIdeal := by
  intro x hx y hy z hz
  exact CertificateCube.kernel_cube x y z hx hy hz

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
