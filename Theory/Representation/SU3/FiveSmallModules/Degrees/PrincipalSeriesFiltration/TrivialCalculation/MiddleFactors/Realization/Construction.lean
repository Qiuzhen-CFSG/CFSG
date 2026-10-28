module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Interface
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Geometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Realization.Quotients

/-!
# The actual middle quotients from the geometric table

The adapted basis defines the intermediate 105-dimensional subspace of
functions on canonical cosets. The checked actor blocks, together with
actual generation, make it invariant under the entire group. Constants are
precisely its first coordinate and augmentation is precisely its first 125
coordinates. Projection to the two intervening blocks gives the requested
coordinates on the literal quotients, over the original coefficient field.

The coset table and the group-generation theorem remain explicit geometric
inputs. This is the linear-algebra assembly supporting Guralnick–Malle
Proposition 4.3 and Aschbacher–Smith K.2, p.453.
-/

@[expose] public section
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open scoped BigOperators Matrix

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
universe v
attribute [local irreducible] basisMatrix coordinateMatrix actorMatrix factor104 factor20
  basisRows coordinateRows actorRows basisCoordinates actor
variable (K : Type v) [Field K] [CharP K 2]

/-- Reindex functions by a literal coset equivalence. -/
noncomputable def reindex (e : Fin 126 ≃ CanonicalPoints) :
    (CanonicalPoints → K) ≃ₗ[K] (Fin 126 → K) where
  toFun f i := f (e i)
  invFun f x := f (e.symm x)
  left_inv f := by funext x; simp
  right_inv f := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (c : CosetEnumeration) (hcard : Nat.card CanonicalPoints = 126)

noncomputable def adaptedCoordinates : (CanonicalPoints → K) ≃ₗ[K] (Fin 126 → K) :=
  (reindex K (c.equiv hcard)).trans (basisCoordinates K)

theorem adaptedCoordinates_action (j : Fin 2) (v : CanonicalPoints → K) :
    adaptedCoordinates K c hcard (functionAction (actor j) v) =
      (CycleCertificate.castMatrix K (actorMatrix j)).mulVec (adaptedCoordinates K c hcard v) := by
  change basisCoordinates K (fun i => v ((actor j)⁻¹ • c.point i)) =
    (CycleCertificate.castMatrix K (actorMatrix j)).mulVec
      (basisCoordinates K (fun i => v (c.point i)))
  simp_rw [← c.action]
  exact basisCoordinates_action K j (fun i => v (c.point i))

theorem adaptedCoordinates_constant :
    adaptedCoordinates K c hcard (fun _ => 1) = Pi.single 0 1 :=
  basisCoordinates_constant K

theorem adaptedCoordinates_last (v : CanonicalPoints → K) :
    adaptedCoordinates K c hcard v 125 = ∑ x, v x := by
  change basisCoordinates K (fun i => v (c.equiv hcard i)) 125 = _
  rw [basisCoordinates_last]
  exact Equiv.sum_comp (c.equiv hcard) v

/-- The inverse image of an initial segment of adapted coordinates. -/
noncomputable def initialSpace (d : ℕ) : Submodule K (CanonicalPoints → K) where
  carrier := {v | ∀ x : Fin 126, d ≤ x.val → adaptedCoordinates K c hcard v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

theorem initialSpace_generator (m : Fin 3) (j : Fin 2) {v : CanonicalPoints → K}
    (hv : v ∈ initialSpace K c hcard (cut m)) :
    functionAction (actor j) v ∈ initialSpace K c hcard (cut m) := by
  intro x hx
  rw [adaptedCoordinates_action]
  change (∑ y : Fin 126, CycleCertificate.castMatrix K (actorMatrix j) x y *
    adaptedCoordinates K c hcard v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [cast_actor_upper K j m x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem constants_iff (v : CanonicalPoints → K) :
    v ∈ (constants (K := K) (G := CanonicalGroup)) ↔
      ∀ x : Fin 126, 1 ≤ x.val → adaptedCoordinates K c hcard v x = 0 := by
  constructor
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    intro x hx
    rw [map_smul, adaptedCoordinates_constant]
    have hx0 : x ≠ 0 := by intro h; subst x; simp at hx
    simp [hx0]
  · intro hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨adaptedCoordinates K c hcard v 0, ?_⟩
    apply (adaptedCoordinates K c hcard).injective
    rw [map_smul, adaptedCoordinates_constant]
    ext x
    by_cases hx : x = 0
    · subst x; simp
    · have hval : 1 ≤ x.val := by
        have : x.val ≠ 0 := by intro he; apply hx; exact Fin.ext he
        omega
      simp [hx, hv x hval]

theorem augmentation_iff (v : CanonicalPoints → K) :
    v ∈ (augmentationKernel (K := K) (G := CanonicalGroup)) ↔
      ∀ x : Fin 126, 125 ≤ x.val → adaptedCoordinates K c hcard v x = 0 := by
  change (∑ x, v x) = 0 ↔ _
  rw [← adaptedCoordinates_last K c hcard]
  constructor
  · intro hv x hx
    have he : x = 125 := by apply Fin.ext; change x.val = 125; omega
    simpa only [he] using hv
  · intro hv
    exact hv 125 (by decide)

variable [Finite K] (hgen : Subgroup.closure (Set.range actor) = ⊤)

/-- The genuine invariant middle subspace of the canonical coset module. -/
noncomputable def middleSpace : Subrepresentation
    (functionAction (K := K) (G := CanonicalGroup) (Ω := CanonicalPoints)) where
  toSubmodule := initialSpace K c hcard 105
  apply_mem_toSubmodule g _ hv :=
    invariant_of_generators functionAction (initialSpace K c hcard 105) actor hgen
      (fun j _v hv => initialSpace_generator K c hcard 1 j hv) g _ hv

theorem middleSpace_iff (v : CanonicalPoints → K) :
    v ∈ middleSpace K c hcard hgen ↔
      ∀ x : Fin 126, 105 ≤ x.val → adaptedCoordinates K c hcard v x = 0 := Iff.rfl

theorem constants_le_middleSpace : constants ≤ middleSpace K c hcard hgen := by
  intro v hv x hx
  exact (constants_iff K c hcard v).mp hv x (by omega)

theorem middleSpace_le_augmentation : middleSpace K c hcard hgen ≤ augmentationKernel := by
  intro v hv
  apply (augmentation_iff K c hcard v).mpr
  intro x hx
  exact hv x (by omega)

noncomputable def lowerCoordinates :
    ((middleSpace K c hcard hgen).toSubmodule ⧸
      (within constants (middleSpace K c hcard hgen)).toSubmodule) ≃ₗ[K] (Fin 104 → K) :=
  blockCoordinates (adaptedCoordinates K c hcard) constants
    (middleSpace K c hcard hgen) 1 104 (by decide)
    (constants_iff K c hcard) (middleSpace_iff K c hcard hgen)

noncomputable def upperCoordinates :
    (augmentationKernel.toSubmodule ⧸
      (within (middleSpace K c hcard hgen) augmentationKernel).toSubmodule) ≃ₗ[K] (Fin 20 → K) :=
  blockCoordinates (adaptedCoordinates K c hcard) (middleSpace K c hcard hgen)
    augmentationKernel 105 20 (by decide)
    (middleSpace_iff K c hcard hgen) (augmentation_iff K c hcard)

theorem lowerCoordinates_action (j : Fin 2) v :
    lowerCoordinates K c hcard hgen
      ((within constants (middleSpace K c hcard hgen)).quotientRepresentation (actor j) v) =
    (CycleCertificate.castMatrix K (factor104 j)).mulVec (lowerCoordinates K c hcard hgen v) := by
  have ht := blockCoordinates_action (adaptedCoordinates K c hcard) constants
    (middleSpace K c hcard hgen) 1 104 (by decide)
    (constants_iff K c hcard) (middleSpace_iff K c hcard hgen)
    (actor j) (CycleCertificate.castMatrix K (actorMatrix j))
    (adaptedCoordinates_action K c hcard j) (cast_actor_upper K j 0) v
  have hb : (fun x y => CycleCertificate.castMatrix K (actorMatrix j)
      (blockIndex 1 104 (by decide) x) (blockIndex 1 104 (by decide) y)) =
      CycleCertificate.castMatrix K (factor104 j) := by
    ext x y
    exact (cast_factor104_eq_block K j x y).symm
  exact ht.trans (congrArg (fun M : Matrix (Fin 104) (Fin 104) K =>
    M.mulVec (lowerCoordinates K c hcard hgen v)) hb)

theorem upperCoordinates_action (j : Fin 2) v :
    upperCoordinates K c hcard hgen
      ((within (middleSpace K c hcard hgen) augmentationKernel).quotientRepresentation (actor j) v) =
    (CycleCertificate.castMatrix K (factor20 j)).mulVec (upperCoordinates K c hcard hgen v) := by
  have ht := blockCoordinates_action (adaptedCoordinates K c hcard)
    (middleSpace K c hcard hgen) augmentationKernel 105 20 (by decide)
    (middleSpace_iff K c hcard hgen) (augmentation_iff K c hcard)
    (actor j) (CycleCertificate.castMatrix K (actorMatrix j))
    (adaptedCoordinates_action K c hcard j) (cast_actor_upper K j 1) v
  have hb : (fun x y => CycleCertificate.castMatrix K (actorMatrix j)
      (blockIndex 105 20 (by decide) x) (blockIndex 105 20 (by decide) y)) =
      CycleCertificate.castMatrix K (factor20 j) := by
    ext x y
    exact (cast_factor20_eq_block K j x y).symm
  exact ht.trans (congrArg (fun M : Matrix (Fin 20) (Fin 20) K =>
    M.mulVec (upperCoordinates K c hcard hgen v)) hb)

/-- The construction uses the literal subspaces and their literal quotients. -/
noncomputable def coordinates : Coordinates K where
  space := middleSpace K c hcard hgen
  constants_le := constants_le_middleSpace K c hcard hgen
  le_augmentation := middleSpace_le_augmentation K c hcard hgen
  actors := actor
  lower := lowerCoordinates K c hcard hgen
  upper := upperCoordinates K c hcard hgen
  lower_action := lowerCoordinates_action K c hcard hgen
  upper_action := upperCoordinates_action K c hcard hgen

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
