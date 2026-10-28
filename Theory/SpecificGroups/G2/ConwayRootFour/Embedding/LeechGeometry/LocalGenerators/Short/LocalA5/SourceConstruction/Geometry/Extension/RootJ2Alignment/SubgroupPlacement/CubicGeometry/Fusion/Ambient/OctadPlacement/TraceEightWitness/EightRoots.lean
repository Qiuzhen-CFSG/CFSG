module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral

/-!
# Integral signs from eight E₈ roots

Eight Leech vectors with Gram matrix twice the E₈ Cartan matrix span a
copy of √2 E₈. Its Cartan matrix has an integral inverse. The corresponding
integral dual vectors pair with the roots as twice the identity, so they
construct twice the rational orthogonal projection using integral Leech
pairings. Thus subtracting that projection from the identity preserves the
whole integral Leech lattice, including its glue. Its trace is 24 - 16 = 8.

An ambient isometry preserving the root span commutes with this sign.
For a cubic, forward preservation of the integral root lattice suffices;
the inverse acts by the square. The final theorem supplies the literal
trace-eight witness from these root data.

Source context: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5,
pp.132–134, studies the rank-eight octad sublattice. The matrix uses the
Bourbaki E₈ numbering (plate VII), also used by Mathlib's `CartanMatrix.E₈`.
The projection proof here is an elementary conditional construction.
Existence of an invariant copy for an arbitrary polynomial cubic is kept
separate as `StableE8RootsExist`; neither 25.9 nor Chapter 9 Exercise 6
is asserted to prove that converse.
-/

open Atlas.Lattices Atlas.Codes
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

@[expose] public noncomputable section

/-- The E₈ Cartan matrix in Bourbaki numbering. -/
def e8Gram : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2,0,-1,0,0,0,0,0; 0,2,0,-1,0,0,0,0; -1,0,2,-1,0,0,0,0;
     0,-1,-1,2,-1,0,0,0; 0,0,0,-1,2,-1,0,0; 0,0,0,0,-1,2,-1,0;
     0,0,0,0,0,-1,2,-1; 0,0,0,0,0,0,-1,2]

/-- An integral inverse, checked by a small matrix product. -/
def e8Inverse : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4,5,7,10,8,6,4,2; 5,8,10,15,12,9,6,3; 7,10,14,20,16,12,8,4;
     10,15,20,30,24,18,12,6; 8,12,16,24,20,15,10,5; 6,9,12,18,15,12,8,4;
     4,6,8,12,10,8,6,3; 2,3,4,6,5,4,3,2]

theorem e8Inverse_mul_gram : e8Inverse * e8Gram = 1 := by decide

theorem e8Inverse_symm (i j : Fin 8) : e8Inverse i j = e8Inverse j i := by
  have h : e8Inverse.transpose = e8Inverse := by decide
  exact (congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => M i j) h).symm

theorem e8Gram_diag (i : Fin 8) : e8Gram i i = 2 := by
  fin_cases i <;> rfl

/-- Eight actual Leech vectors spanning a copy of √2 E₈. -/
structure E8Roots where
  root : Fin 8 → leech
  gram : ∀ i j, leechIntegralPairing (root i) (root j) = 2 * e8Gram i j

namespace E8Roots
variable (s : E8Roots)

theorem root_norm (i : Fin 8) : integerDot (s.root i).val (s.root i).val = 32 := by
  rw [← leechIntegralPairing_mul, s.gram, e8Gram_diag]
  norm_num

def vector (i : Fin 8) : RationalCoordinates := rationalEmbedding (s.root i).val

/-- Twice the dual basis; all coefficients are integers. -/
def dualRoot (i : Fin 8) : leech := ∑ j, e8Inverse i j • s.root j

def dualVector (i : Fin 8) : RationalCoordinates := rationalEmbedding (s.dualRoot i).val

theorem vector_pairing (i j : Fin 8) :
    rationalForm (s.vector i) (s.vector j) = 2 * (e8Gram i j : ℚ) := by
  rw [vector, vector, ← leechIntegralPairing_rational, s.gram]
  push_cast
  rfl

theorem dualVector_eq (i : Fin 8) :
    s.dualVector i = ∑ j, (e8Inverse i j : ℚ) • s.vector j := by
  ext k
  simp [dualVector, dualRoot, vector, rationalEmbedding, Finset.sum_apply]

theorem dual_pairing (i j : Fin 8) :
    rationalForm (s.dualVector i) (s.vector j) = if i = j then 2 else 0 := by
  rw [s.dualVector_eq]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, s.vector_pairing]
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => M i j)
    e8Inverse_mul_gram
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  have hq : ∑ k, (e8Inverse i k : ℚ) * (e8Gram k j : ℚ) =
      if i = j then 1 else 0 := by exact_mod_cast h
  calc
    _ = 2 * ∑ k, (e8Inverse i k : ℚ) * (e8Gram k j : ℚ) := by
      rw [Finset.mul_sum]
      congr 1
      ext k
      ring
    _ = _ := by rw [hq]; split_ifs <;> norm_num

/-- The certificate really has eight independent roots. -/
theorem vectors_independent : LinearIndependent ℚ s.vector := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := congrArg (fun x => rationalForm (s.dualVector i) x) ha
  simp only [map_sum, map_smul, smul_eq_mul, s.dual_pairing, map_zero] at h
  simpa [mul_ite] using h

private theorem form_symm (x y : RationalCoordinates) : rationalForm x y = rationalForm y x := by
  simp [rationalForm, dotProductBilin, dotProduct, mul_comm]

/-- Twice the orthogonal projection onto these eight roots. -/
def doubleProjection : RationalCoordinates →ₗ[ℚ] RationalCoordinates :=
  ∑ i, (rationalForm (s.dualVector i)).smulRight (s.vector i)

theorem doubleProjection_apply (x : RationalCoordinates) :
    s.doubleProjection x = ∑ i, rationalForm (s.dualVector i) x • s.vector i := by
  simp [doubleProjection]

theorem doubleProjection_vector (j : Fin 8) :
    s.doubleProjection (s.vector j) = (2 : ℚ) • s.vector j := by
  classical
  simp [s.doubleProjection_apply, s.dual_pairing]

theorem doubleProjection_selfAdjoint (x y : RationalCoordinates) :
    rationalForm (s.doubleProjection x) y = rationalForm x (s.doubleProjection y) := by
  simp only [s.doubleProjection_apply, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [s.dualVector_eq, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h := e8Inverse_symm i j
  rw [h, form_symm x (s.vector i)]
  ring

theorem doubleProjection_squared (x : RationalCoordinates) :
    s.doubleProjection (s.doubleProjection x) = (2 : ℚ) • s.doubleProjection x := by
  rw [s.doubleProjection_apply x, map_sum]
  simp only [map_smul, s.doubleProjection_vector, smul_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_smul, mul_comm]

/-- Integrality follows from the integral E₈ inverse and the integral Leech pairing. -/
theorem doubleProjection_integral (x : RationalCoordinates) (hx : x ∈ rationalLeech) :
    s.doubleProjection x ∈ rationalLeech := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [s.doubleProjection_apply]
  apply Submodule.sum_mem
  intro i _
  change rationalForm (rationalEmbedding (s.dualRoot i).val) (rationalEmbedding a) •
    s.vector i ∈ rationalLeech
  rw [← leechIntegralPairing_rational (s.dualRoot i) ⟨a, ha⟩]
  rw [Int.cast_smul_eq_zsmul ℚ]
  exact rationalLeech.smul_mem _ ⟨(s.root i).val, (s.root i).prop, rfl⟩

def reflection : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates :=
  { (LinearMap.id - s.doubleProjection) with
    invFun := fun x => x - s.doubleProjection x
    left_inv := by
      intro x
      change x - s.doubleProjection x - s.doubleProjection (x - s.doubleProjection x) = x
      rw [map_sub, s.doubleProjection_squared, two_smul]
      abel
    right_inv := by
      intro x
      change x - s.doubleProjection x - s.doubleProjection (x - s.doubleProjection x) = x
      rw [map_sub, s.doubleProjection_squared, two_smul]
      abel }

theorem reflection_apply (x : RationalCoordinates) :
    s.reflection x = x - s.doubleProjection x := rfl

theorem reflection_form (x y : RationalCoordinates) :
    rationalForm (s.reflection x) (s.reflection y) = rationalForm x y := by
  simp only [s.reflection_apply, map_sub, LinearMap.sub_apply]
  rw [s.doubleProjection_selfAdjoint x y,
    s.doubleProjection_selfAdjoint x (s.doubleProjection y), s.doubleProjection_squared]
  simp only [map_smul, smul_eq_mul]
  ring

def rationalReflection : rationalLatticeIsometries :=
  ⟨s.reflection, s.reflection_form, fun x => by
    constructor
    · intro hx
      exact rationalLeech.sub_mem hx (s.doubleProjection_integral x hx)
    · intro hx
      have hh := rationalLeech.sub_mem hx (s.doubleProjection_integral _ hx)
      change s.reflection (s.reflection x) ∈ rationalLeech at hh
      simpa only [show s.reflection (s.reflection x) = x from s.reflection.left_inv x] using hh⟩

/-- The sign on the root span, restricted to the actual integral Leech lattice. -/
def integralReflection : LeechIsometryGroup := fullIsometryEquiv.symm s.rationalReflection

theorem integralReflection_extension :
    rationalExtension s.integralReflection.val = s.reflection := by
  exact congrArg Subtype.val (fullIsometryEquiv.apply_symm_apply s.rationalReflection)

theorem integralReflection_sq : s.integralReflection ^ 2 = 1 := by
  apply fullIsometryEquiv.injective
  rw [map_pow, map_one, show fullIsometryEquiv s.integralReflection = s.rationalReflection from
    fullIsometryEquiv.apply_symm_apply _]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact s.reflection.left_inv x

theorem integralReflection_trace : rationalLeechTrace s.integralReflection = 8 := by
  unfold rationalLeechTrace
  rw [s.integralReflection_extension]
  change LinearMap.trace ℚ RationalCoordinates (LinearMap.id - s.doubleProjection) = 8
  rw [map_sub, LinearMap.trace_id]
  have ht : LinearMap.trace ℚ RationalCoordinates s.doubleProjection = 16 := by
    norm_num [doubleProjection, s.dual_pairing]
  rw [ht]
  norm_num [RationalCoordinates, Omega, Fintype.card_prod, Fintype.card_fin]


def span : Submodule ℚ RationalCoordinates := Submodule.span ℚ (Set.range s.vector)

theorem span_finrank : Module.finrank ℚ s.span = 8 := by
  change Module.finrank ℚ (Submodule.span ℚ (Set.range s.vector)) = 8
  exact finrank_span_eq_card s.vectors_independent

theorem vector_mem_span (i : Fin 8) : s.vector i ∈ s.span :=
  Submodule.subset_span ⟨i, rfl⟩

theorem doubleProjection_mem_span (x : RationalCoordinates) :
    s.doubleProjection x ∈ s.span := by
  rw [s.doubleProjection_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (s.vector_mem_span i)

theorem doubleProjection_on_span {x : RationalCoordinates} (hx : x ∈ s.span) :
    s.doubleProjection x = (2 : ℚ) • x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact s.doubleProjection_vector i
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy, smul_add]
  | smul a x _ hx => simp [map_smul, hx, smul_smul, mul_comm]

theorem reflection_on_span {x : RationalCoordinates} (hx : x ∈ s.span) :
    s.reflection x = -x := by
  rw [s.reflection_apply, s.doubleProjection_on_span hx, two_smul]
  abel

/-- Preservation of the root span makes its sign commute with an ambient isometry. -/
theorem doubleProjection_commutes (r : LeechIsometryGroup)
    (hstable : s.span.map (rationalExtension r.val).toLinearMap = s.span)
    (x : RationalCoordinates) :
    s.doubleProjection (rationalExtension r.val x) =
      rationalExtension r.val (s.doubleProjection x) := by
  let R := rationalExtension r.val
  have hm {y : RationalCoordinates} (hy : y ∈ s.span) : R y ∈ s.span := by
    rw [← hstable]
    exact ⟨y, hy, rfl⟩
  let z := s.doubleProjection (R x) - R (s.doubleProjection x)
  have hz : z ∈ s.span := s.span.sub_mem (s.doubleProjection_mem_span _) (hm (s.doubleProjection_mem_span _))
  have hzorth (y : RationalCoordinates) (hy : y ∈ s.span) : rationalForm z y = 0 := by
    rw [← hstable] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    change rationalForm (s.doubleProjection (R x) - R (s.doubleProjection x)) (R w) = 0
    rw [map_sub, LinearMap.sub_apply, s.doubleProjection_selfAdjoint,
      s.doubleProjection_on_span (hm hw)]
    change rationalForm (rationalExtension r.val x) ((2 : ℚ) • rationalExtension r.val w) -
      rationalForm (rationalExtension r.val (s.doubleProjection x)) (rationalExtension r.val w) = 0
    rw [map_smul, rationalExtension_form, rationalExtension_form,
      s.doubleProjection_selfAdjoint, s.doubleProjection_on_span hw, map_smul]
    simp
  have hz0 : z = 0 := by
    by_contra hn
    exact (ne_of_gt (rationalForm_positive z hn)) (hzorth z hz)
  exact sub_eq_zero.mp hz0

theorem integralReflection_commutes (r : LeechIsometryGroup)
    (hstable : s.span.map (rationalExtension r.val).toLinearMap = s.span) :
    Commute r s.integralReflection := by
  change r * s.integralReflection = s.integralReflection * r
  apply fullIsometryEquiv.injective
  rw [map_mul, map_mul]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change rationalExtension r.val (rationalExtension s.integralReflection.val x) =
    rationalExtension s.integralReflection.val (rationalExtension r.val x)
  rw [s.integralReflection_extension, s.reflection_apply, s.reflection_apply, map_sub,
    s.doubleProjection_commutes r hstable]

/-- Integral span membership gives rational span membership with the literal embedding. -/
theorem embedding_mem_span {x : leech} (hx : x ∈ Submodule.span ℤ (Set.range s.root)) :
    rationalEmbedding x.val ∈ s.span := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact s.vector_mem_span i
  | zero => simp
  | add x y _ _ hx hy => simpa using s.span.add_mem hx hy
  | smul a x _ hx =>
    have he : rationalEmbedding (a • x).val = (a : ℚ) • rationalEmbedding x.val := by
      ext i
      simp [rationalEmbedding]
    rw [he]
    exact s.span.smul_mem (a : ℚ) hx

/-- Forward preservation of the rational root span suffices for a cubic. -/
theorem stable_of_rational_root_action (r : LeechIsometryGroup) (hr : r ^ 3 = 1)
    (hroot : ∀ i, rationalExtension r.val (s.vector i) ∈ s.span) :
    s.span.map (rationalExtension r.val).toLinearMap = s.span := by
  have hf {x : RationalCoordinates} (hx : x ∈ s.span) :
      rationalExtension r.val x ∈ s.span := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hroot i
    | zero => simp
    | add x y _ _ hx hy => simpa using s.span.add_mem hx hy
    | smul a x _ hx => simpa using s.span.smul_mem a hx
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hf hy
  · intro hx
    refine ⟨rationalExtension r.val (rationalExtension r.val x), hf (hf hx), ?_⟩
    have hp : fullIsometryExtension r ^ 3 = 1 := by rw [← map_pow, hr, map_one]
    exact congrArg (fun g : rationalLatticeIsometries => g.val x) hp

/-- Integral root-lattice preservation is one sufficient way to establish span preservation. -/
theorem stable_of_root_action (r : LeechIsometryGroup) (hr : r ^ 3 = 1)
    (hroot : ∀ i, r.val (s.root i) ∈ Submodule.span ℤ (Set.range s.root)) :
    s.span.map (rationalExtension r.val).toLinearMap = s.span := by
  apply s.stable_of_rational_root_action r hr
  intro i
  rw [vector, rationalExtension_agrees]
  exact s.embedding_mem_span (hroot i)

/-- Rational span preservation suffices; integrality of the sign is already proved. -/
theorem traceEight_witness_of_rational_root_action (r : LeechIsometryGroup) (hr : r ^ 3 = 1)
    (hroot : ∀ i, rationalExtension r.val (s.vector i) ∈ s.span) :
    TraceEightInvolution s.integralReflection ∧ Commute r s.integralReflection :=
  ⟨⟨s.integralReflection_sq, s.integralReflection_trace⟩,
    s.integralReflection_commutes r (s.stable_of_rational_root_action r hr hroot)⟩

/-- Literal integral root-action data supplies all three witness clauses. -/
theorem traceEight_witness_of_root_action (r : LeechIsometryGroup) (hr : r ^ 3 = 1)
    (hroot : ∀ i, r.val (s.root i) ∈ Submodule.span ℤ (Set.range s.root)) :
    TraceEightInvolution s.integralReflection ∧ Commute r s.integralReflection :=
  ⟨⟨s.integralReflection_sq, s.integralReflection_trace⟩,
    s.integralReflection_commutes r (s.stable_of_root_action r hr hroot)⟩

end E8Roots

/-- The remaining lattice existence problem. The data are eight short vectors
with a specified Gram matrix and an invariant rational span, not a supplied involution. -/
def StableE8RootsExist : Prop :=
  ∀ r : LeechIsometryGroup, orderOf r = 3 →
    (∀ x : leech, r.val (r.val x) + r.val x + x = 0) →
    ∃ s : E8Roots, ∀ i, rationalExtension r.val (s.vector i) ∈ s.span

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
