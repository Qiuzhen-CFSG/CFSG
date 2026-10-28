module

public import Theory.AlgebraicGroup.PluckerOrbit.Eigenvalue
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Finite projective images of regular coordinate maps

An irreducible affine variety cannot be covered by finitely many proper closed
linear-dependence loci. Consequently, a regular vector-valued map whose nonzero
values represent finitely many projective points has all its values on one
line. This proves the highest-weight multiplicity step in Borel IV, 13.8 once
the actual cocharacter endpoints are known to belong to the finite fixed locus.
-/

public noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit

universe u
variable {k : Type u} [Field k] {ι : Type}
variable {V : Variety k}

private def dependencyLocus (F : ι → V.PolynomialFunction) (w : ι → k) :
    Set (Variety.Point V) := {x | ∀ i j, F i x * w j = F j x * w i}

private theorem dependencyLocus_closed (F : ι → V.PolynomialFunction) (w : ι → k) :
    IsClosed (dependencyLocus F w) := by
  have heq : dependencyLocus F w =
      ⋂ i, ⋂ j, {x : Variety.Point V |
        (F i * algebraMap k V.PolynomialFunction (w j) -
          F j * algebraMap k V.PolynomialFunction (w i)) x = 0} := by
    ext x
    simp only [dependencyLocus, Set.mem_ofPred_eq, Set.mem_iInter]
    congr! 2 with i j
    change _ ↔ F i x * (algebraMap k V.PolynomialFunction (w j)) x -
      F j x * (algebraMap k V.PolynomialFunction (w i)) x = 0
    rw [polynomialFunction_algebraMap_apply, polynomialFunction_algebraMap_apply]
    exact sub_eq_zero.symm
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    Variety.PolynomialFunction.zeroSet_isClosed _

private theorem mem_dependencyLocus_of_mk_eq (F : ι → V.PolynomialFunction)
    (x : Variety.Point V) (hx : (fun i => F i x) ≠ 0) (p : ℙ k (ι → k))
    (hp : Projectivization.mk k (fun i => F i x) hx = p) : x ∈ dependencyLocus F p.rep := by
  rw [← p.mk_rep] at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ hx p.rep_nonzero).mp hp
  intro i j
  have hi := congr_fun ha i
  have hj := congr_fun ha j
  simp only [Pi.smul_apply, smul_eq_mul] at hi hj
  rw [← hi, ← hj]
  ring

/-- A regular vector-valued map from an irreducible variety with finite
projective image takes all its values on one of those lines. -/
theorem exists_common_line_of_finite_projective_image
    (hV : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (F : ι → V.PolynomialFunction)
    (S : Set (ℙ k (ι → k))) (hS : S.Finite)
    (hne : ∃ x : Variety.Point V, (fun i => F i x) ≠ 0)
    (himage : ∀ (x : Variety.Point V) (hx : (fun i => F i x) ≠ 0),
      Projectivization.mk k (fun i => F i x) hx ∈ S) :
    ∃ p ∈ S, ∀ x : Variety.Point V, ∃ a : k, (fun i => F i x) = a • p.rep := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  let p₀ := Projectivization.mk k (fun i => F i x₀) hx₀
  have hp₀ : p₀ ∈ S := himage x₀ hx₀
  let C : ℙ k (ι → k) → Set (Variety.Point V) := fun p => dependencyLocus F p.rep
  let t := hS.toFinset.image C
  have ht : ∀ Z ∈ t, IsClosed Z := by
    intro Z hZ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hZ
    exact dependencyLocus_closed F p.rep
  have hcover : (Set.univ : Set (Variety.Point V)) ⊆ ⋃₀ (t : Set (Set (Variety.Point V))) := by
    intro x _
    by_cases hx : (fun i => F i x) = 0
    · refine Set.mem_sUnion.mpr ⟨C p₀, Finset.mem_image.mpr
        ⟨p₀, hS.mem_toFinset.mpr hp₀, rfl⟩, ?_⟩
      intro i j
      have hi : F i x = 0 := congr_fun hx i
      have hj : F j x = 0 := congr_fun hx j
      simp [hi, hj]
    · let p := Projectivization.mk k (fun i => F i x) hx
      refine Set.mem_sUnion.mpr ⟨C p, Finset.mem_image.mpr
        ⟨p, hS.mem_toFinset.mpr (himage x hx), rfl⟩, ?_⟩
      exact mem_dependencyLocus_of_mk_eq F x hx p rfl
  obtain ⟨Z, hZ, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hV t ht hcover
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hZ
  refine ⟨p, hS.mem_toFinset.mp hp, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, p.rep j ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using p.rep_nonzero
  intro x
  refine ⟨F j x / p.rep j, ?_⟩
  funext i
  have hminor := hsub (Set.mem_univ x) i j
  simp only [Pi.smul_apply, smul_eq_mul]
  apply (mul_right_cancel₀ hj)
  rw [hminor]
  field_simp

/-- The linear span of the values in the finite-image theorem is one-dimensional. -/
theorem finrank_span_eq_one_of_finite_projective_image
    (hV : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (F : ι → V.PolynomialFunction)
    (S : Set (ℙ k (ι → k))) (hS : S.Finite)
    (hne : ∃ x : Variety.Point V, (fun i => F i x) ≠ 0)
    (himage : ∀ (x : Variety.Point V) (hx : (fun i => F i x) ≠ 0),
      Projectivization.mk k (fun i => F i x) hx ∈ S) :
    Module.finrank k (Submodule.span k (Set.range fun x : Variety.Point V =>
      (fun i => F i x))) = 1 := by
  obtain ⟨p, _, hp⟩ := exists_common_line_of_finite_projective_image hV F S hS hne himage
  have heq : Submodule.span k (Set.range fun x : Variety.Point V => (fun i => F i x)) =
      Submodule.span k {p.rep} := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := hp x
      change (fun i => F i x) ∈ Submodule.span k {p.rep}
      rw [ha]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      obtain ⟨x, hx⟩ := hne
      obtain ⟨a, ha⟩ := hp x
      have ha0 : a ≠ 0 := by
        intro hz
        rw [hz, zero_smul] at ha
        exact hx ha
      have hrep : p.rep = a⁻¹ • (fun i => F i x) := by
        rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hrep]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  rw [heq]
  exact finrank_span_singleton p.rep_nonzero

/-- One coordinate cuts out exactly the nonzero locus of a regular map with
finite projective image. Its nonempty open locus has one constant projective
value. -/
theorem exists_open_constant_projective_value
    (hV : IsIrreducible (Set.univ : Set (Variety.Point V)))
    (F : ι → V.PolynomialFunction)
    (S : Set (ℙ k (ι → k))) (hS : S.Finite)
    (hne : ∃ x : Variety.Point V, (fun i => F i x) ≠ 0)
    (himage : ∀ (x : Variety.Point V) (hx : (fun i => F i x) ≠ 0),
      Projectivization.mk k (fun i => F i x) hx ∈ S) :
    ∃ p ∈ S, ∃ j : ι,
      IsOpen {x : Variety.Point V | F j x ≠ 0} ∧
      (∃ x : Variety.Point V, F j x ≠ 0) ∧
      (∀ x : Variety.Point V, (fun i => F i x) ≠ 0 ↔ F j x ≠ 0) ∧
      ∀ (x : Variety.Point V) (hx : (fun i => F i x) ≠ 0),
        Projectivization.mk k (fun i => F i x) hx = p := by
  obtain ⟨p, hpS, hp⟩ := exists_common_line_of_finite_projective_image hV F S hS hne himage
  obtain ⟨j, hj⟩ : ∃ j, p.rep j ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using p.rep_nonzero
  have hiff (x : Variety.Point V) : (fun i => F i x) ≠ 0 ↔ F j x ≠ 0 := by
    obtain ⟨a, ha⟩ := hp x
    have hjx : F j x = a * p.rep j := congr_fun ha j
    rw [ha, hjx]
    simp [smul_eq_zero, p.rep_nonzero, hj]
  refine ⟨p, hpS, j, (F j).zeroSet_isClosed.isOpen_compl, ?_, hiff, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hiff x).mp hx⟩
  · intro x hx
    rw [← p.mk_rep]
    obtain ⟨a, ha⟩ := hp x
    exact (Projectivization.mk_eq_mk_iff' k _ _ hx p.rep_nonzero).mpr ⟨a, ha.symm⟩

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
