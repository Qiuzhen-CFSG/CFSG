module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Coordinates on literal successive quotients of an adapted flag

Restriction to an interval of coordinates is onto, and its kernel is the
preceding initial segment. The first isomorphism theorem gives coordinates on
the literal quotient. An upper triangular action induces precisely its diagonal
block. The application is the 104- and 20-dimensional factors in the SU₃(5)
coset module, supporting Guralnick–Malle Proposition 4.3.
-/

@[expose] public section

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
open scoped BigOperators Matrix
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization

section Quotients
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V} {n : ℕ}
  (e : V ≃ₗ[K] (Fin n → K)) (S T : Subrepresentation ρ)
  (a d : ℕ) (had : a + d ≤ n)

/-- The coordinates in the interval [a,a+d). -/
def blockIndex (x : Fin d) : Fin n := ⟨x.val + a, by omega⟩

def blockProjection : T.toSubmodule →ₗ[K] (Fin d → K) where
  toFun v x := e v.val (blockIndex a d had x)
  map_add' v w := by ext x; simp
  map_smul' c v := by ext x; simp

variable (hS : ∀ v, v ∈ S ↔ ∀ x : Fin n, a ≤ x.val → e v x = 0)
  (hT : ∀ v, v ∈ T ↔ ∀ x : Fin n, a + d ≤ x.val → e v x = 0)

include hT in
theorem blockProjection_surjective :
    Function.Surjective (blockProjection e T a d had) := by
  intro v
  let w : Fin n → K := fun x =>
    if h : a ≤ x.val ∧ x.val < a + d then
      v ⟨x.val - a, by omega⟩ else 0
  have hw : e.symm w ∈ T := by
    apply (hT _).mpr
    intro x hx
    rw [e.apply_symm_apply]
    exact dif_neg (by omega)
  refine ⟨⟨e.symm w, hw⟩, ?_⟩
  ext x
  change e (e.symm w) (blockIndex a d had x) = v x
  rw [e.apply_symm_apply]
  dsimp [w]
  rw [dif_pos (by dsimp [blockIndex]; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp [blockIndex]

include hS hT in
theorem blockProjection_kernel :
    LinearMap.ker (blockProjection e T a d had) = (within S T).toSubmodule := by
  ext v
  constructor
  · intro hv
    change v.val ∈ S
    apply (hS _).mpr
    intro x hx
    by_cases hx' : x.val < a + d
    · let y : Fin d := ⟨x.val - a, by omega⟩
      have hy : blockIndex a d had y = x := by apply Fin.ext; dsimp [blockIndex, y]; omega
      have h := congrFun (LinearMap.mem_ker.mp hv) y
      change e v.val (blockIndex a d had y) = 0 at h
      rwa [hy] at h
    · exact (hT v.val).mp v.property x (by omega)
  · intro hv
    apply LinearMap.mem_ker.mpr
    ext x
    exact (hS v.val).mp hv (blockIndex a d had x) (by dsimp [blockIndex]; omega)

noncomputable def blockCoordinates :
    (T.toSubmodule ⧸ (within S T).toSubmodule) ≃ₗ[K] (Fin d → K) :=
  (Submodule.quotEquivOfEq _ _ (blockProjection_kernel e S T a d had hS hT).symm).trans
    ((blockProjection e T a d had).quotKerEquivOfSurjective
      (blockProjection_surjective e T a d had hT))

theorem blockCoordinates_mk (v : T.toSubmodule) :
    blockCoordinates e S T a d had hS hT (Submodule.Quotient.mk v) =
      blockProjection e T a d had v := by
  simp [blockCoordinates]

variable (g : G) (A : Matrix (Fin n) (Fin n) K)
  (he : ∀ v, e (ρ g v) = A.mulVec (e v))
  (ht : ∀ x y : Fin n, a ≤ x.val → y.val < a → A x y = 0)

include hT he ht in
theorem blockProjection_action (v : T.toSubmodule) :
    blockProjection e T a d had (T.toRepresentation g v) =
      Matrix.mulVec (fun x y => A (blockIndex a d had x) (blockIndex a d had y))
        (blockProjection e T a d had v) := by
  ext x
  change e (ρ g v.val) (blockIndex a d had x) = _
  rw [he]
  change (∑ y : Fin n, A (blockIndex a d had x) y * e v.val y) =
    ∑ y : Fin d, A (blockIndex a d had x) (blockIndex a d had y) *
      e v.val (blockIndex a d had y)
  have hinj : Function.Injective (blockIndex a d had) := by
    intro b c hbc
    apply Fin.ext
    have h := congrArg Fin.val hbc
    dsimp [blockIndex] at h
    omega
  rw [← Finset.sum_image (f := fun y : Fin n =>
    A (blockIndex a d had x) y * e v.val y) hinj.injOn]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  by_cases hlo : y.val < a
  · rw [ht _ y (by dsimp [blockIndex]; omega) hlo, zero_mul]
  · have hhi : a + d ≤ y.val := by
      by_contra h
      have hy' : y ∈ Finset.image (blockIndex a d had) Finset.univ := by
        apply Finset.mem_image.mpr
        refine ⟨⟨y.val - a, by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        dsimp [blockIndex]
        omega
      exact hy hy'
    rw [(hT v.val).mp v.property y hhi, mul_zero]

include he ht in
theorem blockCoordinates_action (v : T.toSubmodule ⧸ (within S T).toSubmodule) :
    blockCoordinates e S T a d had hS hT ((within S T).quotientRepresentation g v) =
      Matrix.mulVec (fun x y => A (blockIndex a d had x) (blockIndex a d had y))
        (blockCoordinates e S T a d had hS hT v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [show Submodule.Quotient.mk v = (within S T).toSubmodule.mkQ v from rfl,
      Subrepresentation.quotientRepresentation_mk]
    exact (blockCoordinates_mk e S T a d had hS hT _).trans
      ((blockProjection_action e T a d had hT g A he ht v).trans
        (congrArg _ (blockCoordinates_mk e S T a d had hS hT v).symm))
end Quotients

section Invariance
variable {K G V J : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [Finite V] (ρ : Representation K G V) (S : Submodule K V) (actors : J → G)
  (hgen : Subgroup.closure (Set.range actors) = ⊤)
  (h : ∀ j v, v ∈ S → ρ (actors j) v ∈ S)

include hgen h

/-- Finite subspaces stable under generators are stable under the full group. -/
theorem invariant_of_generators (g : G) : ∀ v, v ∈ S → ρ g v ∈ S := by
  have hg : g ∈ Subgroup.closure (Set.range actors) := hgen ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨j, rfl⟩ := hg; exact h j
  | one => intro v hv; simpa only [map_one, Module.End.one_apply] using hv
  | mul g h _ _ ihg ihh =>
    intro v hv
    simpa only [map_mul, Module.End.mul_apply] using ihg _ (ihh v hv)
  | inv g _ ih =>
    let f : S → S := fun v => ⟨ρ g v.val, ih v.val v.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      exact (Representation.apply_bijective ρ g).1 (congrArg Subtype.val hxy)
    intro v hv
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hf ⟨v, hv⟩
    have hu' : ρ g u.val = v := congrArg Subtype.val hu
    rw [← hu', Representation.inv_self_apply]
    exact u.property
end Invariance

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
