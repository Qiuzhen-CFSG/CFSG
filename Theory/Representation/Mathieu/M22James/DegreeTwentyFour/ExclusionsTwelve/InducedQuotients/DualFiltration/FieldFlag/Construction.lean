module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.FieldFlag.MatrixChecks
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Invariant prefixes and their literal quotient actions

Initial adapted coordinate segments define actual subspaces. The two native
core generators preserve them by upper triangularity. Invertibility on each
finite subspace handles inverses, and core generation gives whole-group
invariance. The prefix equivalence also identifies their ordinary column
spans and dimensions.

Projection onto a successive block is surjective, with kernel the previous
stage inside the next. Its first-isomorphism equivalence therefore gives
coordinates on the literal quotient, with the published generator matrices.
This adapts the general flag argument in `CoordinateFiltrations.AdaptedFlag`.
Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16 and Theorem 6.6;
this particular induced flag is proved independently from the saved matrices.
-/

@[expose] public noncomputable section
open Representation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
open Uniqueness.PointRestriction.PointModel
variable (e : Space ≃ₗ[F] (Fin 66 → F))
def space (m : ℕ) : Submodule F Space where
  carrier := {v | ∀ x : Fin 66, cut m ≤ x.val → e v x = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw x hx; simp [hv x hx, hw x hx]
  smul_mem' := by intro a v hv x hx; simp [hv x hx]

/-- Coordinates on the entire prefix, before passing to a successive quotient. -/
def prefixEquiv (m : ℕ) : space e m ≃ₗ[F] (Fin (cut m) → F) where
  toFun v x := e v.val (Fin.castLE (cut_le m) x)
  invFun w := ⟨e.symm (fun x => if h : x.val < cut m then w ⟨x.val,h⟩ else 0), by
    intro x hx
    simp only [e.apply_symm_apply]
    rw [dif_neg (by omega)]⟩
  left_inv v := by
    apply Subtype.ext
    apply e.injective
    funext x
    simp only [e.apply_symm_apply]
    split
    · rfl
    · exact (v.property x (by omega)).symm
  right_inv w := by
    funext x
    simp only [e.apply_symm_apply]
    exact dif_pos x.isLt
  map_add' v w := by funext x; simp
  map_smul' a v := by funext x; simp

lemma prefixEquiv_symm_basis (m : ℕ) (x : Fin (cut m)) :
    ((prefixEquiv e m).symm (Pi.single x 1)).val =
      e.symm (Pi.single (Fin.castLE (cut_le m) x) 1) := by
  change e.symm (fun q => if h : q.val < cut m then (Pi.single x (1 : F) : Fin (cut m) → F) ⟨q.val,h⟩ else 0) = _
  congr 1
  funext q
  by_cases hq : q.val < cut m
  · simp [hq, Pi.single_apply, Fin.ext_iff, eq_comm]
  · have hne : q ≠ Fin.castLE (cut_le m) x := by
      intro h
      have := congrArg Fin.val h
      have := x.isLt
      simp only [Fin.val_castLE] at *
      omega
    simp [hq, hne]

lemma space_eq_span (m : ℕ) :
    space e m = Submodule.span F (Set.range fun x : Fin (cut m) =>
      e.symm (Pi.single (Fin.castLE (cut_le m) x) 1)) := by
  let b := (Pi.basisFun F (Fin (cut m))).map (prefixEquiv e m).symm
  have h := (Submodule.span_val_image_eq_iff (space e m) (Set.range b)).mpr b.span_eq
  rw [← Set.range_comp] at h
  have hb : (Subtype.val ∘ b) = fun x : Fin (cut m) =>
      e.symm (Pi.single (Fin.castLE (cut_le m) x) 1) := by
    funext x
    simpa only [b, Function.comp_apply, Module.Basis.map_apply, Pi.basisFun_apply] using
      prefixEquiv_symm_basis e m x
  rw [hb] at h
  exact h.symm

variable (he : ∀ j v, e (fieldRepresentation .dual (ambientGenerator j) v) =
  (adaptedMatrix j).mulVec (e v))
  (ht : ∀ m j (x y : Fin 66), cut m ≤ x.val → y.val < cut m →
    adaptedMatrix j x y = 0)

include he ht

theorem generator_mem (m : ℕ) (j : Fin 2) {v : Space} (hv : v ∈ space e m) :
    fieldRepresentation .dual (ambientGenerator j) v ∈ space e m := by
  intro x hx
  rw [he]
  change (∑ y : Fin 66, adaptedMatrix j x y * e v y) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : y.val < cut m
  · rw [ht m j x y hx hy, zero_mul]
  · rw [hv y (by omega), mul_zero]

theorem word_mem (m : ℕ) (g : M22TripleCover) :
    ∀ v, v ∈ space e m → fieldRepresentation .dual g v ∈ space e m := by
  let : Finite Space := Finite.of_injective e e.injective
  have hg : g ∈ Subgroup.closure
      ({coreGeneratorA, coreGeneratorB} : Set M22TripleCover) := by
    rw [coreGenerators_closure_eq_top]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact fun v hv => generator_mem e he ht m 0 hv
    · exact fun v hv => generator_mem e he ht m 1 hv
  | one => intro v hv; simpa using hv
  | inv g _ ih =>
    let f : space e m → space e m := fun v => ⟨_, ih v v.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact (Representation.apply_bijective (fieldRepresentation .dual) g).1
        (congrArg Subtype.val h)
    intro v hv
    obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hw' : fieldRepresentation .dual g w = v := congrArg Subtype.val hw
    rw [← hw', Representation.inv_self_apply]
    exact w.property
  | mul g h _ _ hg hh =>
    intro v hv
    exact (by simpa only [map_mul, Module.End.mul_apply] using hg _ (hh v hv))

def stage (m : ℕ) : Subrepresentation (fieldRepresentation .dual) where
  toSubmodule := space e m
  apply_mem_toSubmodule g _ hv := word_mem e he ht m g _ hv

theorem stage_zero : stage e he ht 0 = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · intro v hv
    change v = 0
    apply e.injective
    funext x
    simpa using hv x (by rw [cut_zero]; omega)
  · exact bot_le

theorem stage_last : stage e he ht 3 = ⊤ := by
  apply top_unique
  intro v _ x hx
  rw [cut_last] at hx
  omega

theorem stage_mono (m : ℕ) (hm : m < 3) :
    stage e he ht m ≤ stage e he ht (m + 1) := by
  intro v hv x hx
  exact hv x (le_trans (cut_step ⟨m, hm⟩).1.le hx)

lemma stage_finrank (m : ℕ) : Module.finrank F (stage e he ht m).toSubmodule = cut m := by
  change Module.finrank F (space e m) = cut m
  rw [(prefixEquiv e m).finrank_eq, Module.finrank_fin_fun]

def projection (t : Fin 3) :
    (stage e he ht (t.val + 1)).toSubmodule →ₗ[F]
      (Fin (factorDimension t) → F) where
  toFun v x := e v.val (blockIndex t x)
  map_add' v w := by funext x; simp
  map_smul' a v := by funext x; simp

theorem projection_surjective (t : Fin 3) :
    Function.Surjective (projection e he ht t) := by
  intro v
  let w : Fin 66 → F := fun x =>
    if h : cut t.val ≤ x.val ∧ x.val < cut (t.val + 1) then
      v ⟨x.val - cut t.val, by have := cut_dimension t; omega⟩ else 0
  have hw : e.symm w ∈ space e (t.val + 1) := by
    intro x hx
    simp only [e.apply_symm_apply]
    dsimp [w]
    rw [dif_neg (by omega)]
  refine ⟨⟨e.symm w, hw⟩, ?_⟩
  funext x
  change e (e.symm w) (blockIndex t x) = v x
  rw [e.apply_symm_apply]
  dsimp [w]
  have hx := x.isLt
  have hd := cut_dimension t
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

theorem projection_kernel (t : Fin 3) :
    LinearMap.ker (projection e he ht t) =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule := by
  ext v
  constructor
  · intro hv
    change ∀ x : Fin 66, cut t.val ≤ x.val → e v.val x = 0
    intro x hx
    by_cases hx' : x.val < cut (t.val + 1)
    · let y : Fin (factorDimension t) := ⟨x.val - cut t.val, by have := cut_dimension t; omega⟩
      have hy : blockIndex t y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change e v.val (blockIndex t y) = 0 at h
      rwa [hy] at h
    · exact v.property x (by omega)
  · intro hv
    apply LinearMap.mem_ker.mpr
    funext x
    exact hv (blockIndex t x) (by dsimp [blockIndex]; omega)

noncomputable def coordinates (t : Fin 3) :
    ((stage e he ht (t.val + 1)).toSubmodule ⧸
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule)
      ≃ₗ[F] (Fin (factorDimension t) → F) :=
  (Submodule.quotEquivOfEq _ _ (projection_kernel e he ht t).symm).trans
    ((projection e he ht t).quotKerEquivOfSurjective (projection_surjective e he ht t))

theorem coordinates_mk (t : Fin 3) (v : (stage e he ht (t.val + 1)).toSubmodule) :
    coordinates e he ht t (Submodule.Quotient.mk v) = projection e he ht t v := by
  simp [coordinates]

theorem projection_generator (t : Fin 3) (j : Fin 2)
    (v : (stage e he ht (t.val + 1)).toSubmodule) :
    projection e he ht t ((stage e he ht (t.val + 1)).toRepresentation
      (ambientGenerator j) v) =
    (factorMatrix t j).mulVec (projection e he ht t v) := by
  funext x
  change e (fieldRepresentation .dual (ambientGenerator j) v.val) (blockIndex t x) = _
  rw [he]
  simp only [Matrix.mulVec, dotProduct, ← factor_block]
  change (∑ y : Fin 66, adaptedMatrix j (blockIndex t x) y * e v.val y) =
    ∑ y : Fin (factorDimension t), adaptedMatrix j (blockIndex t x) (blockIndex t y) *
      e v.val (blockIndex t y)
  have hinj : Function.Injective (blockIndex t) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin 66 =>
    adaptedMatrix j (blockIndex t x) y * e v.val y) hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  by_cases hlo : y.val < cut t.val
  · rw [ht t.val j _ y (by dsimp [blockIndex]; omega) hlo, zero_mul]
  · have hhi : cut (t.val + 1) ≤ y.val := by
      by_contra h
      have hy' : y ∈ Finset.image (blockIndex t) Finset.univ := by
        apply Finset.mem_image.mpr
        refine ⟨⟨y.val - cut t.val, ?_⟩, Finset.mem_univ _, ?_⟩
        · have := cut_dimension t; omega
        · apply Fin.ext; dsimp [blockIndex]; omega
      exact hy hy'
    rw [v.property y hhi, mul_zero]

theorem coordinates_generator (t : Fin 3) (j : Fin 2) v :
    coordinates e he ht t
      ((within (stage e he ht t.val) (stage e he ht (t.val + 1))).quotientRepresentation
        (ambientGenerator j) v) =
      (factorMatrix t j).mulVec (coordinates e he ht t v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v =
      (within (stage e he ht t.val) (stage e he ht (t.val + 1))).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (coordinates_mk e he ht t _).trans
      ((projection_generator e he ht t j v).trans
        (congrArg (factorMatrix t j).mulVec (coordinates_mk e he ht t v).symm))


end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
