module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceExtensions
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Source pure commutators and paired-vector stabilizers

The two coordinate embeddings preserve the original marked summands and
polar pairing. Transporting literal displacements proves [V₁,L_u]=V₁
and [V₂,L_u]=V₂∩uᗮ, with the latter of dimension n−1. The same marked
comparison identifies the simultaneous paired-vector stabilizer with its
two-residual, and every outer fixer exchanges the original components.

Source: Aschbacher–Smith H.9.1(3–4), printed pp.389–390.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits BinaryNaturalDual.VectorStabilizers
open BinaryLinear.OuterCyclic Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup n M V)

noncomputable def naturalEmbedding : BinaryLinear.OuterCyclic.Space n →ₗ[ZMod 2] V :=
  S.natural.subtype.comp S.naturalCoordinates.symm.toLinearMap
noncomputable def dualEmbedding : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n) →ₗ[ZMod 2] V :=
  S.dual.subtype.comp S.model.dualCoordinates.symm.toLinearMap

@[simp] theorem naturalEmbedding_coordinates (x : BinaryLinear.OuterCyclic.Space n) :
    S.model.coordinates (S.naturalEmbedding x) = (x,0) := by
  exact (S.model.natural_marking _).trans (congrArg (fun z => (z,0)) (S.naturalCoordinates.apply_symm_apply x))
@[simp] theorem dualEmbedding_coordinates (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    S.model.coordinates (S.dualEmbedding f) = (0,f) := by
  exact (S.model.dual_marking _).trans (congrArg (fun z => (0,z)) (S.model.dualCoordinates.apply_symm_apply f))

@[simp] theorem naturalEmbedding_range : LinearMap.range S.naturalEmbedding = S.natural := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩; exact (S.naturalCoordinates.symm x).property
  · intro hv; exact ⟨S.naturalCoordinates ⟨v,hv⟩, congrArg Subtype.val (S.naturalCoordinates.symm_apply_apply _)⟩
@[simp] theorem dualEmbedding_range : LinearMap.range S.dualEmbedding = S.dual := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩; exact (S.model.dualCoordinates.symm x).property
  · intro hv; exact ⟨S.model.dualCoordinates ⟨v,hv⟩, congrArg Subtype.val (S.model.dualCoordinates.symm_apply_apply _)⟩

/-- The source polar form is the actual evaluation pairing in the constructed coordinates. -/
theorem polar_coordinates (v w : V) :
    S.quadratic.polarBilin v w = (S.model.coordinates v).2 (S.model.coordinates w).1 +
      (S.model.coordinates w).2 (S.model.coordinates v).1 := by
  calc
    _ = BinaryNaturalDual.quadratic.polarBilin (S.model.coordinates v) (S.model.coordinates w) := by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, S.quadratic_apply, map_add]
    _ = _ := BinaryNaturalDual.polar_apply _ _

/-- The literal polar hyperplane of a pure source vector in the dual summand. -/
noncomputable def dualHyperplane (u : S.natural) : Submodule (ZMod 2) V :=
  S.dual ⊓ LinearMap.BilinForm.orthogonal S.quadratic.polarBilin
    (Submodule.span (ZMod 2) {(u : V)})

theorem dualHyperplane_eq_map (u : S.natural) : S.dualHyperplane u =
    (annihilator (S.naturalCoordinates u)).map S.dualEmbedding := by
  ext v
  rw [dualHyperplane, Submodule.mem_inf,
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  change (v ∈ S.dual ∧ S.quadratic.polarBilin u v = 0) ↔ _
  rw [S.polar_coordinates, S.model.natural_marking]
  simp only [LinearMap.zero_apply, zero_add]
  constructor
  · rintro ⟨hv,hf⟩
    refine ⟨S.model.dualCoordinates ⟨v,hv⟩, ?_, ?_⟩
    · have he := congrArg Prod.snd (S.model.dual_marking ⟨v,hv⟩)
      change S.model.dualCoordinates ⟨v,hv⟩ (S.naturalCoordinates u) = 0
      change (S.model.coordinates v).2 = S.model.dualCoordinates ⟨v,hv⟩ at he
      rw [← he]; exact hf
    · exact congrArg Subtype.val (S.model.dualCoordinates.symm_apply_apply _)
  · rintro ⟨f,hf,rfl⟩
    exact ⟨(S.model.dualCoordinates.symm f).property, by rw [S.dualEmbedding_coordinates]; exact hf⟩

theorem dualHyperplane_finrank (u : S.natural) (hu : (u : V) ≠ 0) :
    Module.finrank (ZMod 2) (S.dualHyperplane u) = n - 1 := by
  rw [S.dualHyperplane_eq_map]
  have hi : Function.Injective S.dualEmbedding := S.dual.injective_subtype.comp S.model.dualCoordinates.symm.injective
  rw [← (Submodule.equivMapOfInjective S.dualEmbedding hi (annihilator (S.naturalCoordinates u))).finrank_eq]
  exact Pure.annihilator_finrank (S.naturalCoordinates_ne_zero u hu)

private theorem commutator_embedding {G H X W : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G X) (A : Subgroup G)
    (σ : Representation (ZMod 2) H W) (e : A ≃* H) (j : W →ₗ[ZMod 2] X)
    (he : ∀ a w, ρ a.val (j w) = j (σ (e a) w)) :
    subspaceCommutator ρ (LinearMap.range j) A = (Representation.Coinvariants.ker σ).map j := by
  rw [subspaceCommutator, Representation.Coinvariants.ker, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨a,ha,_,⟨w,rfl⟩,rfl⟩
    exact ⟨σ (e ⟨a,ha⟩) w - w, ⟨(e ⟨a,ha⟩,w),rfl⟩, by rw [map_sub, ← he]⟩
  · rintro ⟨_,⟨⟨a,w⟩,rfl⟩,rfl⟩
    refine ⟨(e.symm a).val,(e.symm a).property,j w,⟨w,rfl⟩,?_⟩
    rw [he, e.apply_symm_apply, map_sub]

/-- The pure source stabilizer acts through its actual natural and dual actions. -/
theorem pure_natural_action (u : S.natural) (hu : (u : V) ≠ 0)
    (a : S.stabilizer u) (x : BinaryLinear.OuterCyclic.Space n) :
    S.representation a.val (S.naturalEmbedding x) =
      S.naturalEmbedding ((S.purePointEquiv u hu a).val x) := by
  apply S.model.coordinates.injective
  rw [S.model.equivariant, S.naturalEmbedding_coordinates, S.naturalEmbedding_coordinates,
    ← S.pureInnerEquiv_apply u hu a, Pure.inner_action, naturalDualRepresentation_apply, map_zero]
  rfl

theorem pure_dual_action (u : S.natural) (hu : (u : V) ≠ 0)
    (a : S.stabilizer u) (f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)) :
    S.representation a.val (S.dualEmbedding f) =
      S.dualEmbedding ((S.purePointEquiv u hu a).val.symm.dualMap f) := by
  apply S.model.coordinates.injective
  rw [S.model.equivariant, S.dualEmbedding_coordinates, S.dualEmbedding_coordinates,
    ← S.pureInnerEquiv_apply u hu a, Pure.inner_action, naturalDualRepresentation_apply, map_zero]
  rfl

/-- H.9.1(3), with both commutators taken in the original source module. -/
theorem pure_commutators (u : S.natural) (hu : (u : V) ≠ 0) :
    subspaceCommutator S.representation S.natural (S.residual u) = S.natural ∧
    subspaceCommutator S.representation S.dual (S.residual u) = S.dualHyperplane u := by
  rw [← (S.pure_stabilizer_eq_residual u hu).1]
  constructor
  · have h := commutator_embedding S.representation (S.stabilizer u)
      (Pure.pointNaturalRepresentation _) (S.purePointEquiv u hu)
      S.naturalEmbedding (S.pure_natural_action u hu)
    rw [S.naturalEmbedding_range,
      Pure.point_natural_commutator (by simpa [BinaryLinear.OuterCyclic.Space] using (show 3 ≤ n by have := S.degree; omega))
        (S.naturalCoordinates_ne_zero u hu), Submodule.map_top, S.naturalEmbedding_range] at h
    exact h
  · have h := commutator_embedding S.representation (S.stabilizer u)
      (Pure.pointDualRepresentation _) (S.purePointEquiv u hu)
      S.dualEmbedding (S.pure_dual_action u hu)
    rw [S.dualEmbedding_range, Pure.point_dual_commutator (S.naturalCoordinates_ne_zero u hu),
      ← S.dualHyperplane_eq_map] at h
    exact h

/-- The actual simultaneous stabilizer of paired pure components is the residual. -/
theorem paired_stabilizer (u : S.natural) (w : S.dual)
    (h : S.quadratic ((u : V) + w) = 1) :
    S.stabilizer u ⊓ S.stabilizer w = S.residual ((u : V) + w) := by
  have he : S.model.coordinates ((u : V) + w) = (S.naturalCoordinates u,S.model.dualCoordinates w) := by
    simp [S.model.natural_marking, S.model.dual_marking]
  have hp : S.model.dualCoordinates w (S.naturalCoordinates u) = 1 := by
    simpa only [S.quadratic_apply, he, BinaryNaturalDual.quadratic_apply] using h
  apply Subgroup.map_injective (f := S.model.group.toMonoidHom) S.model.group.injective
  rw [Subgroup.map_inf _ _ _ S.model.group.injective, S.stabilizer_map, S.stabilizer_map,
    S.residual_map, S.model.natural_marking, S.model.dual_marking, he]
  exact componentStabilizer_eq_innerResidual S.degree _ hp

/-- An outer element fixing a nonsingular sum exchanges its literal components. -/
theorem paired_outer_swaps (u : S.natural) (w : S.dual)
    (s : S.stabilizer ((u : V) + w)) (hout : s.val ∉ componentLayer M) :
    S.representation s.val u = w ∧ S.representation s.val w = u := by
  have he : S.model.coordinates ((u : V) + w) = (S.naturalCoordinates u,S.model.dualCoordinates w) := by
    simp [S.model.natural_marking, S.model.dual_marking]
  let a : fullStabilizer (AutomorphismModel.coordinateAction S.degree)
      (S.naturalCoordinates u,S.model.dualCoordinates w) :=
    ⟨S.model.group s, by
      have hh := (S.stabilizerEquiv _ s).property
      simpa only [he, S.stabilizerEquiv_apply] using hh⟩
  have ho : a.val ∉ MulAut.innerSubgroup (LinearGroup n) := fun h => hout ((S.model.inner_iff s).mp h)
  obtain ⟨h₁,h₂⟩ := outer_swaps_components S.degree _ a ho
  constructor <;> apply S.model.coordinates.injective
  · simpa only [S.model.equivariant, S.model.natural_marking, S.model.dual_marking] using h₁
  · simpa only [S.model.equivariant, S.model.natural_marking, S.model.dual_marking] using h₂

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
