module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.Flag
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.QuotientCoordinates.Checks

/-!
# Coordinates on the three natural induced Mathieu quotients

The checked inverse identifies the saved columns with a basis of the literal
22-slot, three-dimensional F₄ carrier. The checked generator conjugations and
vanishing lower blocks preserve the first 15 and 60 columns. Finite-dimensional
injectivity gives preservation by inverse generators, and the native generation
theorem gives preservation by the whole triple cover. Thus the orbit spans in
`fieldFlag` equal the ordinary spans of those columns.

Projection onto each successive block is surjective and has kernel exactly the
preceding flag term inside the next term. The first isomorphism theorem gives an
actual equivalence on `FieldFactor`; the diagonal-block identities prove that
it intertwines both literal quotient actions with `factorMatrix`. In particular,
the actual quotient dimensions are 15, 45, and 6. No simplicity premise is used.

Source context: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16 and Theorem 6.6/Table 6.7. The candidate coordinates, conventions and
original ATLAS attribution are preserved in `NaturalFiltration/source/README.md`.
All finite certificates are checked in `QuotientCoordinates.Checks`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
namespace QuotientCertificate

open Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

/-- Flatten the literal 22-by-3 carrier in the order `3*i+j`. -/
def flatten : Space ≃ₗ[Field] (Fin 66 → Field) where
  toFun v k := v (flatIndex.symm k).1 (flatIndex.symm k).2
  invFun v i k := v (flatIndex (i,k))
  left_inv v := by funext i k; simp only [Equiv.symm_apply_apply]
  right_inv v := by
    funext k
    change v (flatIndex (flatIndex.symm k)) = v k
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma flatten_apply (v : Space) (i : Fin 22) (k : Fin 3) :
    flatten v (flatIndex (i,k)) = v i k := by
  change v (flatIndex.symm (flatIndex (i,k))).1
    (flatIndex.symm (flatIndex (i,k))).2 = _
  rw [Equiv.symm_apply_apply]

lemma flatten_generator (j : Fin 2) (v : Space) :
    flatten (fieldRepresentation .natural (ambientGenerator j) v) =
      (generatorMatrix j).mulVec (flatten v) := by
  funext x
  obtain ⟨⟨i,p⟩, rfl⟩ := flatIndex.surjective x
  obtain ⟨i, rfl⟩ := (ambientPermutation j).surjective i
  rw [flatten_apply]
  change representation .natural (ambientGenerator j) v (ambientPermutation j i) p = _
  rw [generator_apply]
  change (SchreierCertificate.naturalMatrix
    (SchreierCertificate.schreierIndex i j)).mulVec (v i) p = _
  simp only [Matrix.mulVec, dotProduct]
  rw [← flatIndex.sum_comp]
  simp only [Fintype.sum_prod_type, generator_entries, flatten_apply, ite_mul,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- The inverse of the certified adapted basis, before unflattening slots. -/
def matrixCoordinates : (Fin 66 → Field) ≃ₗ[Field] (Fin 66 → Field) :=
  { inverseMatrix.mulVecLin with
    invFun := basisMatrix.mulVec
    left_inv := fun v => by
      change basisMatrix.mulVec (inverseMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, basis_mul_inverse, Matrix.one_mulVec]
    right_inv := fun v => by
      change inverseMatrix.mulVec (basisMatrix.mulVec v) = v
      rw [Matrix.mulVec_mulVec, inverse_mul_basis, Matrix.one_mulVec] }

def adaptedEquiv : Space ≃ₗ[Field] (Fin 66 → Field) := flatten.trans matrixCoordinates

lemma adaptedEquiv_symm_basis (k : Fin 66) :
    adaptedEquiv.symm (Pi.single k 1) = basisVector k := by
  funext i p
  change basisMatrix.mulVec (Pi.single k 1) (flatIndex (i,p)) = _
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [basis_entries]
  simp only [basisVector, flatIndex, finProdFinEquiv, Equiv.coe_fn_mk]
  congr 1
  omega

lemma adaptedEquiv_basis (k : Fin 66) : adaptedEquiv (basisVector k) = Pi.single k 1 := by
  rw [← adaptedEquiv_symm_basis, LinearEquiv.apply_symm_apply]

lemma adaptedEquiv_generator (j : Fin 2) (v : Space) :
    adaptedEquiv (fieldRepresentation .natural (ambientGenerator j) v) =
      (adaptedMatrix j).mulVec (adaptedEquiv v) := by
  change inverseMatrix.mulVec (flatten (fieldRepresentation .natural (ambientGenerator j) v)) =
    (adaptedMatrix j).mulVec (inverseMatrix.mulVec (flatten v))
  rw [flatten_generator, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h : inverseMatrix * generatorMatrix j = adaptedMatrix j * inverseMatrix := by
    calc
      inverseMatrix * generatorMatrix j =
          inverseMatrix * (generatorMatrix j * basisMatrix) * inverseMatrix := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, basis_mul_inverse, mul_one]
      _ = adaptedMatrix j * inverseMatrix := by
        rw [generator_mul_basis, ← Matrix.mul_assoc, inverse_mul_basis, one_mul]
  rw [h]

lemma basis_expansion (v : Space) :
    v = ∑ k : Fin 66, adaptedEquiv v k • basisVector k := by
  apply adaptedEquiv.injective
  simp only [map_sum, map_smul, adaptedEquiv_basis]
  funext i
  simp [Pi.single_apply]

open Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- The ordinary span of an initial segment, expressed in the certified basis. -/
def coordinateSpace (n : ℕ) : Submodule Field Space where
  carrier := {v | ∀ k : Fin 66, n ≤ k.val → adaptedEquiv v k = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw k hk; simp [hv k hk, hw k hk]
  smul_mem' := by intro a v hv k hk; simp [hv k hk]

lemma basisVector_mem_coordinateSpace (n : ℕ) (k : Fin 66) (hk : k.val < n) :
    basisVector k ∈ coordinateSpace n := by
  intro i hi
  rw [adaptedEquiv_basis]
  have h : i ≠ k := by intro h; subst i; omega
  simp [h]

lemma coordinateSpace_eq_span (n : ℕ) (hn : n ≤ 66) :
    coordinateSpace n = Submodule.span Field
      (Set.range fun i : Fin n => basisVector (Fin.castLE hn i)) := by
  apply le_antisymm
  · intro v hv
    rw [basis_expansion v]
    apply Submodule.sum_mem
    intro k _
    by_cases hk : k.val < n
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨k.val, hk⟩, rfl⟩
    · rw [hv k (by omega), zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact basisVector_mem_coordinateSpace n _ k.isLt

lemma coordinateSpace_generator_mem (m : Fin 4) (j : Fin 2)
    {v : Space} (hv : v ∈ coordinateSpace (cut m.val)) :
    fieldRepresentation .natural (ambientGenerator j) v ∈ coordinateSpace (cut m.val) := by
  intro x hx
  rw [adaptedEquiv_generator]
  change (∑ y : Fin 66, adaptedMatrix j x y * adaptedEquiv v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m.val
  · rw [adapted_upper m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

lemma coordinateSpace_inv_generator_mem (m : Fin 4) (j : Fin 2)
    {v : Space} (hv : v ∈ coordinateSpace (cut m.val)) :
    fieldRepresentation .natural (ambientGenerator j)⁻¹ v ∈ coordinateSpace (cut m.val) := by
  let f : coordinateSpace (cut m.val) → coordinateSpace (cut m.val) :=
    fun w => ⟨_, coordinateSpace_generator_mem m j w.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (Representation.apply_bijective (fieldRepresentation .natural) (ambientGenerator j)).1
      (congrArg Subtype.val h)
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
  have hw' : fieldRepresentation .natural (ambientGenerator j) w = v := congrArg Subtype.val hw
  rw [← hw', Representation.inv_self_apply]
  exact w.property

lemma coordinateSpace_invariant (m : Fin 4) (g : M22TripleCover) :
    ∀ v, v ∈ coordinateSpace (cut m.val) →
      fieldRepresentation .natural g v ∈ coordinateSpace (cut m.val) := by
  have hg : g ∈ Subgroup.closure {coreGeneratorA, coreGeneratorB} := by
    rw [coreGenerators_closure_eq_top]
    trivial
  refine Subgroup.closure_induction''
    (p := fun g _ => ∀ v, v ∈ coordinateSpace (cut m.val) →
      fieldRepresentation .natural g v ∈ coordinateSpace (cut m.val)) ?_ ?_ ?_ ?_ hg
  · intro x hx
    rcases hx with (rfl | rfl)
    · exact fun _ hv => coordinateSpace_generator_mem m 0 hv
    · exact fun _ hv => coordinateSpace_generator_mem m 1 hv
  · intro x hx
    rcases hx with (rfl | rfl)
    · exact fun _ hv => coordinateSpace_inv_generator_mem m 0 hv
    · exact fun _ hv => coordinateSpace_inv_generator_mem m 1 hv
  · intro v hv
    simpa only [map_one, Module.End.one_apply] using hv
  · intro x y _ _ hx hy v hv
    simpa only [map_mul, Module.End.mul_apply] using hx _ (hy v hv)

lemma fieldPrefix_eq_coordinateSpace (m : Fin 4) (hn : cut m.val ≤ 66) :
    (fieldPrefix (cut m.val) hn).toSubmodule = coordinateSpace (cut m.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,i⟩, rfl⟩
    exact coordinateSpace_invariant m g _
      (basisVector_mem_coordinateSpace _ _ i.isLt)
  · rw [coordinateSpace_eq_span _ hn]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨(1,i), ?_⟩
    simp only [map_one, Module.End.one_apply]

lemma fieldFlag_eq_coordinateSpace (m : ℕ) (hm : m ≤ 3) :
    (fieldFlag m).toSubmodule = coordinateSpace (cut m) := by
  interval_cases m
  · apply le_antisymm
    · exact bot_le
    · intro v hv
      change v = 0
      apply adaptedEquiv.injective
      funext k
      simpa only [map_zero, Pi.zero_apply] using hv k (Nat.zero_le _)
  · exact fieldPrefix_eq_coordinateSpace 1 (by decide)
  · exact fieldPrefix_eq_coordinateSpace 2 (by decide)
  · symm
    apply top_unique
    intro v _ k hk
    have := k.isLt
    change 66 ≤ k.val at hk
    omega

/-- The orbit span used in the literal flag is its ordinary linear span. -/
lemma fieldPrefix_fifteen_eq_span :
    (fieldPrefix 15 (by decide)).toSubmodule = Submodule.span Field
      (Set.range fun i : Fin 15 => basisVector (Fin.castLE (by decide) i)) := by
  exact (fieldPrefix_eq_coordinateSpace 1 (by decide)).trans
    (coordinateSpace_eq_span 15 (by decide))

lemma fieldPrefix_sixty_eq_span :
    (fieldPrefix 60 (by decide)).toSubmodule = Submodule.span Field
      (Set.range fun i : Fin 60 => basisVector (Fin.castLE (by decide) i)) := by
  exact (fieldPrefix_eq_coordinateSpace 2 (by decide)).trans
    (coordinateSpace_eq_span 60 (by decide))

open Uniqueness.PointRestriction.PointModel
open Representation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

lemma fieldFlag_mem_iff (m : ℕ) (hm : m ≤ 3) (v : Space) :
    v ∈ (fieldFlag m).toSubmodule ↔
      ∀ k : Fin 66, cut m ≤ k.val → adaptedEquiv v k = 0 := by
  rw [fieldFlag_eq_coordinateSpace m hm]
  rfl

/-- Projection of the next literal flag term onto one successive block. -/
def projection (s : Fin 3) :
    (fieldFlag (s.val+1)).toSubmodule →ₗ[Field] (Fin (factorDegree s) → Field) where
  toFun v i := adaptedEquiv v.val (blockIndex s i)
  map_add' _ _ := by funext i; simp
  map_smul' _ _ := by funext i; simp

lemma projection_surjective (s : Fin 3) : Function.Surjective (projection s) := by
  intro v
  let w : Fin 66 → Field := fun x =>
    if h : cut s.val ≤ x.val ∧ x.val < cut (s.val+1) then
      v ⟨x.val - cut s.val, by have := cut_step s; omega⟩ else 0
  have hw : adaptedEquiv.symm w ∈ (fieldFlag (s.val+1)).toSubmodule := by
    apply (fieldFlag_mem_iff _ (by omega) _).mpr
    intro x hx
    rw [LinearEquiv.apply_symm_apply]
    dsimp [w]
    rw [dif_neg (by omega)]
  refine ⟨⟨adaptedEquiv.symm w, hw⟩, ?_⟩
  funext x
  change adaptedEquiv (adaptedEquiv.symm w) (blockIndex s x) = v x
  rw [LinearEquiv.apply_symm_apply]
  dsimp [w]
  have hx := x.isLt
  have hc := cut_step s
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

lemma projection_kernel (s : Fin 3) :
    LinearMap.ker (projection s) = (factorKernel s).toSubmodule := by
  ext v
  constructor
  · intro hv
    change v.val ∈ (fieldFlag s.val).toSubmodule
    apply (fieldFlag_mem_iff _ (by omega) _).mpr
    intro x hx
    by_cases hx' : x.val < cut (s.val+1)
    · let y : Fin (factorDegree s) :=
        ⟨x.val - cut s.val, by have := cut_step s; omega⟩
      have hy : blockIndex s y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change adaptedEquiv v.val (blockIndex s y) = 0 at h
      rwa [hy] at h
    · exact (fieldFlag_mem_iff _ (by omega) _).mp v.property x (by omega)
  · intro hv
    change v.val ∈ (fieldFlag s.val).toSubmodule at hv
    apply LinearMap.mem_ker.mpr
    funext x
    exact (fieldFlag_mem_iff _ (by omega) _).mp hv (blockIndex s x)
      (by dsimp [blockIndex]; omega)

/-- The first isomorphism theorem for the literal nested-subspace quotient. -/
noncomputable def quotientEquiv (s : Fin 3) :
    FieldFactor s ≃ₗ[Field] (Fin (factorDegree s) → Field) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel s).symm).trans
    ((projection s).quotKerEquivOfSurjective (projection_surjective s))

lemma quotientEquiv_mk (s : Fin 3) (v : (fieldFlag (s.val+1)).toSubmodule) :
    quotientEquiv s (Submodule.Quotient.mk v) = projection s v := by
  simp [quotientEquiv]

lemma projection_generator (s : Fin 3) (j : Fin 2)
    (v : (fieldFlag (s.val+1)).toSubmodule) :
    projection s ((fieldFlag (s.val+1)).toRepresentation (ambientGenerator j) v) =
      (factorMatrix s j).mulVec (projection s v) := by
  funext x
  change adaptedEquiv (fieldRepresentation .natural (ambientGenerator j) v.val)
    (blockIndex s x) = _
  rw [adaptedEquiv_generator]
  change (∑ y : Fin 66, adaptedMatrix j (blockIndex s x) y * adaptedEquiv v.val y) =
    ∑ y : Fin (factorDegree s), factorMatrix s j x y * adaptedEquiv v.val (blockIndex s y)
  simp_rw [← adapted_block s j]
  have hinj : Function.Injective (blockIndex s) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 66 =>
    adaptedMatrix j (blockIndex s x) y * adaptedEquiv v.val y) hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  by_cases hlo : y.val < cut s.val
  · rw [adapted_upper ⟨s.val, by omega⟩ j _ y (by dsimp [blockIndex]; omega) hlo, zero_mul]
  · have hhi : cut (s.val+1) ≤ y.val := by
      by_contra h
      have hy' : y ∈ Finset.image (blockIndex s) Finset.univ := by
        apply Finset.mem_image.mpr
        refine ⟨⟨y.val - cut s.val, ?_⟩, Finset.mem_univ _, ?_⟩
        · have := cut_step s; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [(fieldFlag_mem_iff _ (by omega) _).mp v.property y hhi, mul_zero]

lemma quotientEquiv_generator (s : Fin 3) (j : Fin 2) (v : FieldFactor s) :
    quotientEquiv s (factorRepresentation s (ambientGenerator j) v) =
      (factorMatrix s j).mulVec (quotientEquiv s v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change quotientEquiv s
      ((factorKernel s).quotientRepresentation (ambientGenerator j)
        ((factorKernel s).toSubmodule.mkQ v)) = _
    rw [Subrepresentation.quotientRepresentation_mk]
    exact (quotientEquiv_mk s _).trans
      ((projection_generator s j v).trans
        (congrArg (factorMatrix s j).mulVec (quotientEquiv_mk s v).symm))

end QuotientCertificate

/-- Equivariant coordinates on each of the three literal orbit-span quotients. -/
theorem nonempty_factorCoordinates (s : Fin 3) : Nonempty (FactorCoordinates s) :=
  ⟨⟨QuotientCertificate.quotientEquiv s, QuotientCertificate.quotientEquiv_generator s⟩⟩

/-- Dimensions of the actual successive quotients, with no coordinate hypothesis. -/
theorem fieldFactor_finrank (s : Fin 3) :
    Module.finrank Field (FieldFactor s) = factorDegree s :=
  factor_finrank_of_coordinates s (nonempty_factorCoordinates s).some

/-- The three literal quotient dimensions are 15, 45, and 6, in that order. -/
theorem fieldFactor_finranks :
    Module.finrank Field (FieldFactor 0) = 15 ∧
    Module.finrank Field (FieldFactor 1) = 45 ∧
    Module.finrank Field (FieldFactor 2) = 6 :=
  ⟨fieldFactor_finrank 0, fieldFactor_finrank 1, fieldFactor_finrank 2⟩

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration
