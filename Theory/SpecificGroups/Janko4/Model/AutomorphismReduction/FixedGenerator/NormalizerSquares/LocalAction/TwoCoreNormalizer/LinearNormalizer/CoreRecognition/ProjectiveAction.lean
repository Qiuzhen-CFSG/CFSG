module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.Structure
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.PermutationComparison
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveAction.Geometry
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveAction.FiniteData

/-!
# The core action on 22 endpoint stars

The 231 distinct scalar triples are labelled by all unordered pairs of 22
points. The checked generator tables show that right multiplication by A and B
acts on these pairs through the inverses of the specified point permutations.
Compatibility is multiplicative and determines the point permutation uniquely:
two pairs meeting in just one endpoint recover that endpoint. Generation by
A and B therefore constructs the degree-22 homomorphism on the actual core.

The induced line action is inverse right row multiplication and transports the
22 endpoint stars. Its kernel is precisely the matrices fixing every specified
scalar line; no identification of those matrices as scalars is used here.

The candidate configuration and conventions are documented in
`CoreRecognition/source/README.md`; original matrix data and attribution are
retained in `../../LinearModel/source/`. The finite certificates are proved in
`ProjectiveAction/FiniteData.lean`, using Lean kernel reduction.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace CoreProjectiveAction

/-- Transport a line index by permuting its two endpoints. -/
def pairMap (p : Equiv.Perm (Fin 22)) (i : Fin 231) : Fin 231 :=
  pairIndex (p (projectiveEndpoints i).1) (p (projectiveEndpoints i).2)

theorem pairMap_spec (p : Equiv.Perm (Fin 22)) (i : Fin 231) :
    endpointPair (pairMap p i) = (endpointPair i).image p := by
  rw [pairMap, pairIndex_spec _ _ (p.injective.ne (endpoints_ne i))]
  simp only [endpointPair, Finset.image_insert, Finset.image_singleton]

theorem pairMap_one (i : Fin 231) : pairMap 1 i = i := by
  apply endpointPair_injective
  rw [pairMap_spec]
  exact Finset.image_id

theorem pairMap_mul (p q : Equiv.Perm (Fin 22)) (i : Fin 231) :
    pairMap (p * q) i = pairMap p (pairMap q i) := by
  apply endpointPair_injective
  rw [pairMap_spec, pairMap_spec, pairMap_spec, Finset.image_image]
  rfl

/-- The action of endpoint permutations on the 231 unordered pairs. -/
def pairAction : Equiv.Perm (Fin 22) →* Equiv.Perm (Fin 231) where
  toFun p :=
    { toFun := pairMap p
      invFun := pairMap p⁻¹
      left_inv := fun i => by rw [← pairMap_mul, inv_mul_cancel, pairMap_one]
      right_inv := fun i => by rw [← pairMap_mul, mul_inv_cancel, pairMap_one] }
  map_one' := by apply Equiv.ext; intro i; exact pairMap_one i
  map_mul' p q := by apply Equiv.ext; intro i; exact pairMap_mul p q i

theorem pairAction_spec (p : Equiv.Perm (Fin 22)) (i : Fin 231) :
    endpointPair (pairAction p i) = (endpointPair i).image p := pairMap_spec p i

theorem pairAction_injective : Function.Injective pairAction := by
  intro p q hpq
  have hpairs (a b : Fin 22) (hab : a ≠ b) :
      ({a, b} : Finset (Fin 22)).image p = ({a, b} : Finset (Fin 22)).image q := by
    rw [← pairIndex_spec a b hab, ← pairAction_spec, ← pairAction_spec, hpq]
  have partners : ∀ a : Fin 22, ∃ b c : Fin 22, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    decide +kernel
  apply Equiv.ext
  intro a
  obtain ⟨b, c, hab, hac, hbc⟩ := partners a
  have h₁ : p a = q a ∨ p a = q b := by
    have h : p a ∈ ({a, b} : Finset (Fin 22)).image q := by
      rw [← hpairs a b hab]
      exact Finset.mem_image.mpr ⟨a, by simp only [Finset.mem_insert, true_or], rfl⟩
    simpa only [Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton] using h
  have h₂ : p a = q a ∨ p a = q c := by
    have h : p a ∈ ({a, c} : Finset (Fin 22)).image q := by
      rw [← hpairs a c hac]
      exact Finset.mem_image.mpr ⟨a, by simp only [Finset.mem_insert, true_or], rfl⟩
    simpa only [Finset.image_insert, Finset.image_singleton,
      Finset.mem_insert, Finset.mem_singleton] using h
  rcases h₁ with h | h
  · exact h
  rcases h₂ with h' | h'
  · exact h'
  exact False.elim (hbc (q.injective (h.symm.trans h')))

def rightRow (u : Matrix12ˣ) (v : Row) : Row := Matrix.vecMul v (u : Matrix12)

theorem rightRow_one : rightRow 1 = id := by
  funext w
  exact Matrix.vecMul_one w

theorem rightRow_mul (u v : Matrix12ˣ) : rightRow (u * v) = rightRow v ∘ rightRow u := by
  funext w
  exact (Matrix.vecMul_vecMul w (u : Matrix12) (v : Matrix12)).symm

/-- Right row action agrees with the inverse permutation on endpoint pairs. -/
def Compatible (u : Matrix12ˣ) (p : Equiv.Perm (Fin 22)) : Prop :=
  ∀ i : Fin 231, rightRow u '' scalarLine (projectiveVector i) =
    scalarLine (projectiveVector (pairAction p⁻¹ i))

theorem compatible_one : Compatible 1 1 := by
  intro i
  rw [rightRow_one, Set.image_id, inv_one, map_one, Equiv.Perm.one_apply]

theorem compatible_mul {u v : Matrix12ˣ} {p q : Equiv.Perm (Fin 22)}
    (hu : Compatible u p) (hv : Compatible v q) : Compatible (u * v) (p * q) := by
  intro i
  calc
    rightRow (u * v) '' scalarLine (projectiveVector i) =
        rightRow v '' (rightRow u '' scalarLine (projectiveVector i)) := by
      rw [rightRow_mul]
      exact (Set.image_image (rightRow v) (rightRow u) (scalarLine (projectiveVector i))).symm
    _ = scalarLine (projectiveVector (pairAction q⁻¹ (pairAction p⁻¹ i))) := by
      rw [hu i, hv]
    _ = scalarLine (projectiveVector (pairAction (p * q)⁻¹ i)) := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply]

theorem compatible_unique {u : Matrix12ˣ} {p q : Equiv.Perm (Fin 22)}
    (hp : Compatible u p) (hq : Compatible u q) : p = q := by
  apply inv_injective
  apply pairAction_injective
  apply Equiv.ext
  intro i
  exact line_inj ((hp i).symm.trans (hq i))

theorem compatible_A : Compatible coreA corePermA := by
  intro i
  obtain ⟨j, hv, hj⟩ := generatorA_data i
  have he : j = pairAction corePermA⁻¹ i :=
    endpointPair_injective (hj.trans (pairAction_spec corePermA⁻¹ i).symm)
  change (fun w => Matrix.vecMul w (coreA : Matrix12)) '' _ = _
  rw [coe_coreA, scalarLine_image _ _ matrixJ_commute_A.symm,
    scalarLine_of_mem hv, he]

theorem compatible_B : Compatible coreB corePermB := by
  intro i
  obtain ⟨j, hv, hj⟩ := generatorB_data i
  have he : j = pairAction corePermB⁻¹ i :=
    endpointPair_injective (hj.trans (pairAction_spec corePermB⁻¹ i).symm)
  change (fun w => Matrix.vecMul w (coreB : Matrix12)) '' _ = _
  rw [coe_coreB, scalarLine_image _ _ matrixJ_commute_B.symm,
    scalarLine_of_mem hv, he]

theorem compatible_exists (x : derivedGroup) : ∃ p, Compatible (x : Matrix12ˣ) p := by
  let S : Submonoid Matrix12ˣ :=
    { carrier := {u | ∃ p, Compatible u p}
      one_mem' := ⟨1, compatible_one⟩
      mul_mem' := by
        rintro u v ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p * q, compatible_mul hp hq⟩ }
  have hfinite : ∀ u ∈ ({coreA, coreB} : Set Matrix12ˣ), IsOfFinOrder u := by
    rintro u (rfl | rfl)
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨11, by decide, coreA_pow_eleven⟩
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, coreB_pow_two⟩
  have h : derivedGroup.toSubmonoid ≤ S := by
    rw [derivedGroup_eq_closure, Subgroup.closure_toSubmonoid_of_isOfFinOrder hfinite]
    apply Submonoid.closure_le.mpr
    rintro u (rfl | rfl)
    · exact ⟨corePermA, compatible_A⟩
    · exact ⟨corePermB, compatible_B⟩
  exact h x.property

end CoreProjectiveAction
open CoreProjectiveAction

/-- The degree-22 action of the literal matrix core on endpoint stars. -/
noncomputable def corePermutationAction : derivedGroup →* Equiv.Perm (Fin 22) where
  toFun x := Classical.choose (compatible_exists x)
  map_one' := compatible_unique (Classical.choose_spec (compatible_exists 1)) compatible_one
  map_mul' x y := compatible_unique (Classical.choose_spec (compatible_exists (x * y)))
    (compatible_mul (Classical.choose_spec (compatible_exists x))
      (Classical.choose_spec (compatible_exists y)))

/-- Compatibility with the concrete right row action. -/
theorem corePermutationAction_spec (x : derivedGroup) :
    Compatible (x : Matrix12ˣ) (corePermutationAction x) :=
  Classical.choose_spec (compatible_exists x)

/-- The first matrix generator induces the specified inverse row permutation. -/
theorem corePermutationAction_coreGeneratorA :
    corePermutationAction coreGeneratorA = corePermA :=
  compatible_unique (corePermutationAction_spec coreGeneratorA) compatible_A

/-- The involutory matrix generator induces the specified point permutation. -/
theorem corePermutationAction_coreGeneratorB :
    corePermutationAction coreGeneratorB = corePermB :=
  compatible_unique (corePermutationAction_spec coreGeneratorB) compatible_B

/-- The action kernel is exactly pointwise fixation of the scalar lines. -/
theorem corePermutationAction_eq_one_iff (x : derivedGroup) :
    corePermutationAction x = 1 ↔ FixesCoreLines (x : Matrix12ˣ) := by
  constructor
  · intro hx i
    have h := corePermutationAction_spec x i
    rw [hx, inv_one, map_one, Equiv.Perm.one_apply] at h
    rw [← h]
    exact Set.mem_image_of_mem (rightRow (x : Matrix12ˣ)) (Or.inl rfl)
  · intro hx
    apply compatible_unique (corePermutationAction_spec x)
    intro i
    rw [inv_one, map_one, Equiv.Perm.one_apply]
    exact (scalarLine_image (projectiveVector i) ((x : Matrix12ˣ) : Matrix12)
      (derivedGroup_commute_matrixJ x)).trans (scalarLine_of_mem (hx i))

/-- The action on the 231 labelled scalar lines. -/
noncomputable def coreLineAction : derivedGroup →* Equiv.Perm (Fin 231) :=
  pairAction.comp corePermutationAction

theorem coreLineAction_endpoints (x : derivedGroup) (i : Fin 231) :
    endpointPair (coreLineAction x i) = (endpointPair i).image (corePermutationAction x) :=
  pairAction_spec (corePermutationAction x) i

/-- The line action uses inverse matrices, as required for a homomorphism. -/
theorem coreLineAction_scalarLines (x : derivedGroup) (i : Fin 231) :
    (fun v => Matrix.vecMul v (((x⁻¹ : derivedGroup) : Matrix12ˣ).val)) ''
      scalarLine (projectiveVector i) = scalarLine (projectiveVector (coreLineAction x i)) := by
  have h := corePermutationAction_spec x⁻¹ i
  simp only [map_inv, inv_inv] at h
  exact h

/-- The 21 lines incident with an endpoint. -/
def coreEndpointStar (a : Fin 22) : Set (Fin 231) := {i | a ∈ endpointPair i}

theorem coreEndpointStar_injective : Function.Injective coreEndpointStar := by
  have third : ∀ a b : Fin 22, a ≠ b → ∃ c : Fin 22, a ≠ c ∧ b ≠ c := by decide +kernel
  intro a b h
  by_contra hab
  obtain ⟨c, hac, hbc⟩ := third a b hab
  have ha : pairIndex a c ∈ coreEndpointStar a := by
    change a ∈ endpointPair (pairIndex a c)
    rw [pairIndex_spec a c hac]
    exact Finset.mem_insert_self _ _
  have hb : pairIndex a c ∈ coreEndpointStar b := h ▸ ha
  change b ∈ endpointPair (pairIndex a c) at hb
  rw [pairIndex_spec a c hac, Finset.mem_insert, Finset.mem_singleton] at hb
  exact hb.elim (fun hba => hab hba.symm) hbc

theorem coreLineAction_mem_star (x : derivedGroup) (a : Fin 22) (i : Fin 231) :
    coreLineAction x i ∈ coreEndpointStar (corePermutationAction x a) ↔
      i ∈ coreEndpointStar a := by
  change corePermutationAction x a ∈ endpointPair (coreLineAction x i) ↔ a ∈ endpointPair i
  rw [coreLineAction_endpoints, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (corePermutationAction x).injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The constructed matrix action permutes the 22 endpoint stars. -/
theorem coreLineAction_image_star (x : derivedGroup) (a : Fin 22) :
    coreLineAction x '' coreEndpointStar a = coreEndpointStar (corePermutationAction x a) := by
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (coreLineAction_mem_star x a j).mpr hj
  · intro hi
    refine ⟨(coreLineAction x).symm i, ?_, (coreLineAction x).apply_symm_apply i⟩
    apply (coreLineAction_mem_star x a _).mp
    rwa [(coreLineAction x).apply_symm_apply]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
