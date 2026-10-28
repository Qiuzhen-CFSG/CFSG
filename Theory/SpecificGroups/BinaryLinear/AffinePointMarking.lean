module

public import Theory.SpecificGroups.BinaryLinear.Affine
public import Theory.GroupTheory.SemidirectProductTranslationCentralizer

/-!
# Marking all translations in an affine point centralizer

An affine point marking identifies an actual element centralizer with the
centralizer of a translation, retaining the entire original elementary
subgroup pointwise. This is stronger than marking just the involution: the
whole subgroup is needed to distinguish the two elementary root groups in
Aschbacher, *Sporadic Groups* (1994), 39.1(2).

The structure is local coordinate data, not an ambient recognition theorem.
The source application constructs it from the split configuration in
Aschbacher--Smith 12.2.26--27, printed pp.806--807.
-/

@[expose] public section
open Subgroup
namespace BinaryLinear.Affine
variable {G : Type*} [Group G]

/-- A centralizer model retaining every element of the original translations. -/
structure PointMarking (d : ℕ) (z : G) (V : Subgroup G) where
  point_mem : z ∈ V
  seed_le : V ≤ centralizer ({z} : Set G)
  vectorEquiv : V ≃* Multiplicative (Fin d → ZMod 2)
  centralizerEquiv : centralizer ({z} : Set G) ≃*
    Theory.GroupTheory.TranslationCentralizer.centralizer (action d)
      (vectorEquiv ⟨z, point_mem⟩)
  on_seed : ∀ u : V,
    (centralizerEquiv ⟨u, seed_le u.property⟩ : Model d) =
      SemidirectProduct.inl (vectorEquiv u)

namespace PointMarking
variable {d : ℕ} {z : G} {V : Subgroup G} (M : PointMarking d z V)

/-- In particular the original distinguished element keeps its translation. -/
theorem on_point :
    (M.centralizerEquiv ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : Model d) =
      SemidirectProduct.inl (M.vectorEquiv ⟨z, M.point_mem⟩) :=
  M.on_seed ⟨z, M.point_mem⟩

/-- A nonidentity source point is a nonzero translation in these coordinates. -/
theorem vector_ne_one (hz : z ≠ 1) : M.vectorEquiv ⟨z, M.point_mem⟩ ≠ 1 := by
  intro he
  exact hz (congrArg Subtype.val (M.vectorEquiv.map_eq_one_iff.mp he))

/-- The image of the literal seed is the full translation kernel, not an
unspecified elementary subgroup of the same order. -/
theorem map_seed :
    (V.subgroupOf (centralizer ({z} : Set G))).map M.centralizerEquiv.toMonoidHom =
      (Theory.GroupTheory.TranslationCentralizer.inclusion (action d)
        (M.vectorEquiv ⟨z, M.point_mem⟩)).range := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨M.vectorEquiv ⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    exact (M.on_seed ⟨u, hu⟩).symm
  · rintro ⟨v, rfl⟩
    refine ⟨⟨M.vectorEquiv.symm v, M.seed_le (M.vectorEquiv.symm v).property⟩,
      (M.vectorEquiv.symm v).property, ?_⟩
    apply Subtype.ext
    exact (M.on_seed (M.vectorEquiv.symm v)).trans
      (congrArg SemidirectProduct.inl (M.vectorEquiv.apply_symm_apply v))

end PointMarking
end BinaryLinear.Affine
