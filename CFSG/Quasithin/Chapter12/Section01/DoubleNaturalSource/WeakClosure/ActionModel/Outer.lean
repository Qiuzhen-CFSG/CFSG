module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel.Layer
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ModelInput

/-!
# Outer interchange in the literal doubled quotient action

A nonzero intertwiner from the natural action to its graph twist would
be an isomorphism, since the natural action is transitive on nonzero
vectors. That would make inverse transpose inner, a contradiction.
Consequently the diagonal block of the graph actor on the doubled
module vanishes. Invertibility and equal dimensions identify its image
of the natural summand with the dual summand.

A group comparison preserving the component layer applies this argument
to the original quotient representation, rather than an unrelated model.
Source: Aschbacher--Smith, H.9 setup and 12.1, printed pp.389,788.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryNaturalDual BinaryLinear.OuterCyclic
open BinaryNaturalDual.ModelOrbits
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel

theorem graph_intertwiner_eq_zero {n : ℕ} (hn : n = 4 ∨ n = 5)
    (f : BinaryLinear.OuterCyclic.Space n →ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space n)
    (hf : ∀ (g : LinearGroup n) x, f (g x) = graphLinear n g (f x)) : f = 0 := by
  by_contra hne
  have hi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    change x = 0
    by_contra hx0
    have hall : ∀ y, f y = 0 := by
      intro y
      by_cases hy : y = 0
      · simp [hy]
      obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq hx0 hy
      rw [← hg, hf, show f x = 0 from hx, map_zero]
    exact hne (LinearMap.ext hall)
  let e : LinearGroup n := LinearEquiv.ofBijective f
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  apply AutomorphismModel.graph_not_inner hn
  refine ⟨e, ?_⟩
  apply MulEquiv.ext
  intro g
  apply LinearEquiv.ext
  intro x
  change e (g (e.symm x)) = (graphLinear n g) x
  exact (hf g (e.symm x)).trans (by rw [show f (e.symm x) = x from e.apply_symm_apply x])


theorem graph_maps_natural {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : Representation (ZMod 2) (MulAut (LinearGroup n)) (CoordinateSpace n))
    (hi : ∀ g v, ρ (MulAut.conj g) v = naturalDualRepresentation g v) :
    (LinearMap.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
      (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker.map
        (ρ (graphLinear n)) =
    (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
      (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker := by
  let f := (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _).comp
    ((ρ (graphLinear n)).comp (LinearMap.inl (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _))
  have hf : f = 0 := graph_intertwiner_eq_zero hn f (by
    intro g x
    have he : graphLinear n * MulAut.conj g =
        MulAut.conj (graphLinear n g) * graphLinear n := by
      ext a
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have ha := congrArg (fun a => ρ a (x, 0)) he
    simp only [map_mul, Module.End.mul_apply, hi, naturalDualRepresentation_apply,
      map_zero] at ha
    exact congrArg Prod.fst ha)
  have hle : (LinearMap.snd (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
      (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker.map
        (ρ (graphLinear n)) ≤
    (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n)
      (Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n))).ker := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v.2 = 0 := hv
    have he := LinearMap.congr_fun hf v.1
    change (ρ (graphLinear n) v).1 = 0
    simpa only [f, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inl_apply,
      LinearMap.zero_apply, ← hv'] using he
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [← (Submodule.equivMapOfInjective _ (ρ.apply_bijective _).injective _).finrank_eq]
  rw [LinearMap.ker_snd, LinearMap.ker_fst,
    LinearMap.finrank_range_of_inj LinearMap.inl_injective,
    LinearMap.finrank_range_of_inj LinearMap.inr_injective,
    Subspace.dual_finrank_eq]

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionModel


namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

theorem quotientLayerEquiv_coordinates (l : componentLayer B.ActionQuotient)
    (w : Additive (componentOrbit V (T : Subgroup G))) :
    B.linearCoordinates (B.quotientRepresentation l w) =
      naturalDualRepresentation (B.quotientLayerEquiv l) (B.linearCoordinates w) := by
  have hl : (l : B.ActionQuotient) ∈ B.componentEmbedding.range := by
    rw [B.componentEmbedding_range_eq_layer]
    exact l.property
  obtain ⟨q, hq⟩ := hl
  have he : l = ⟨B.componentEmbedding q,
      B.componentEmbedding_range_eq_layer ▸ ⟨q, rfl⟩⟩ := Subtype.ext hq.symm
  rw [he, B.quotientLayerEquiv_embedding]
  exact B.componentEmbedding_coordinates q w

theorem exists_quotient_outer :
    ∃ t : B.ActionQuotient, t ∉ componentLayer B.ActionQuotient ∧
      B.naturalSpace.map (B.quotientRepresentation t) = B.dualSpace := by
  obtain ⟨e, hel, hem⟩ := SourceComparison.exists_layerCompatible B.degree
    (B.full.trans (AutomorphismModel.projectiveAutEquiv (by have := B.degree; omega)).symm)
    B.quotientLayerEquiv
  let ρ := B.linearCoordinates.conjRingEquiv.toMonoidHom.comp
    (B.quotientRepresentation.comp e.symm.toMonoidHom)
  have hi (g : LinearGroup n) (v : CoordinateSpace n) :
      ρ (MulAut.conj g) v = naturalDualRepresentation g v := by
    have he : e.symm (MulAut.conj g) =
        (B.quotientLayerEquiv.symm g : B.ActionQuotient) := by
      apply e.injective
      rw [e.apply_symm_apply, hel, B.quotientLayerEquiv.apply_symm_apply]
    change B.linearCoordinates
      (B.quotientRepresentation (e.symm (MulAut.conj g)) (B.linearCoordinates.symm v)) = _
    rw [he, B.quotientLayerEquiv_coordinates, B.quotientLayerEquiv.apply_symm_apply,
      B.linearCoordinates.apply_symm_apply]
  have hswap := WeakClosure.ActionModel.graph_maps_natural B.degree ρ hi
  refine ⟨e.symm (graphLinear n), ?_, ?_⟩
  · intro ht
    have hh := (hem (e.symm (graphLinear n))).mpr ht
    rw [e.apply_symm_apply] at hh
    exact AutomorphismModel.graph_not_inner B.degree hh
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hh : ρ (graphLinear n) (B.linearCoordinates v) ∈
          (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _).ker := by
        rw [← hswap]
        exact ⟨B.linearCoordinates v, hv, rfl⟩
      change (B.linearCoordinates (B.quotientRepresentation _ v)).1 = 0
      change (B.linearCoordinates (B.quotientRepresentation _
        (B.linearCoordinates.symm (B.linearCoordinates v)))).1 = 0 at hh
      rwa [B.linearCoordinates.symm_apply_apply] at hh
    · intro hw
      have hh : B.linearCoordinates w ∈
          (LinearMap.fst (ZMod 2) (BinaryLinear.OuterCyclic.Space n) _).ker := hw
      rw [← hswap] at hh
      obtain ⟨v, hv, he⟩ := hh
      refine ⟨B.linearCoordinates.symm v, ?_, ?_⟩
      · change (B.linearCoordinates (B.linearCoordinates.symm v)).2 = 0
        rw [B.linearCoordinates.apply_symm_apply]
        exact hv
      · exact B.linearCoordinates.injective he

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

