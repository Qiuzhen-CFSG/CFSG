module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Canonical subgroups of an involution centralizer

The two-residual of the centralizer is embedded back in the ambient group.
Inside that residual the relevant characteristic subgroups are its two-core
and the commutator of the center of its two-core with the whole residual.
All these constructions respect actual group isomorphisms. Two-centrality is
witnessed by centrality in an actual Sylow two-subgroup and also transports
through isomorphisms.

These elementary constructions support the exceptional cases on printed
pp.1202–1203 of Aschbacher–Smith, *The Classification of Quasithin Groups*
(combined manuscript, 1 March 2004). They do not assert any model-specific
centralizer identification or existence of a nonidentity conjugate product.
-/

@[expose] public section

open Subgroup

namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- An involution central in a Sylow two-subgroup of its ambient group. -/
def IsSylowCentralInvolution (v : G) : Prop :=
  orderOf v = 2 ∧ ∃ S : Sylow 2 G, v ∈ S ∧
    (S : Subgroup G) ≤ centralizer ({v} : Set G)

theorem IsSylowCentralInvolution.map [Finite G] (e : G ≃* H) {v : G}
    (hv : IsSylowCentralInvolution v) : IsSylowCentralInvolution (e v) := by
  obtain ⟨ho, S, hvS, hS⟩ := hv
  refine ⟨?_, S.mapSurjective (f := e.toMonoidHom) e.surjective, ?_, ?_⟩
  · rwa [e.orderOf_eq]
  · exact mem_map.mpr ⟨v, hvS, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_singleton_iff.mp (hS hs))

/-- The actual subgroup `O²(C_G(v))`, with its inclusion in `G`. -/
def centralizerTwoResidual (v : G) : Subgroup G :=
  (pResidual 2 (centralizer ({v} : Set G))).map
    (centralizer ({v} : Set G)).subtype

/-- The center of the two-core, embedded in the original group. -/
def centerTwoCore (G : Type*) [Group G] : Subgroup G :=
  (center (pCore 2 G)).map (pCore 2 G).subtype

/-- The intrinsic subgroup `[Z(O₂(G)),G]`. -/
def centerCoreCommutator (G : Type*) [Group G] : Subgroup G :=
  ⁅centerTwoCore G, ⊤⁆

instance centerTwoCore_characteristic : (centerTwoCore G).Characteristic := by
  unfold centerTwoCore
  infer_instance

instance centerCoreCommutator_characteristic : (centerCoreCommutator G).Characteristic := by
  unfold centerCoreCommutator
  infer_instance

theorem centralizerTwoResidual_le (v : G) :
    centralizerTwoResidual v ≤ centralizer ({v} : Set G) := map_subtype_le _

theorem centerCoreCommutator_le : centerCoreCommutator G ≤ centerTwoCore G :=
  commutator_le_left _ _

theorem map_centralizer_singleton (e : G ≃* H) (v : G) :
    (centralizer ({v} : Set G)).map e.toMonoidHom =
      centralizer ({e v} : Set H) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro hy
    refine ⟨e.symm y, mem_centralizer_singleton_iff.mpr ?_, e.apply_symm_apply y⟩
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

theorem map_centralizerTwoResidual [Finite G] (e : G ≃* H) (v : G) :
    (centralizerTwoResidual v).map e.toMonoidHom = centralizerTwoResidual (e v) := by
  unfold centralizerTwoResidual
  rw [map_embedded_pResidual, map_centralizer_singleton]

theorem map_center_equiv (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (mem_center_iff.mp hx w)
  · intro hy
    refine ⟨e.symm y, mem_center_iff.mpr ?_, e.apply_symm_apply y⟩
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hy (e x)

theorem map_centerTwoCore (e : G ≃* H) :
    (centerTwoCore G).map e.toMonoidHom = centerTwoCore H := by
  let f := (e.subgroupMap (pCore 2 G)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  calc
    _ = ((center (pCore 2 G)).map f.toMonoidHom).map (pCore 2 H).subtype := by
      rw [centerTwoCore, map_map, map_map]
      rfl
    _ = _ := by rw [map_center_equiv]; rfl

theorem map_centerCoreCommutator (e : G ≃* H) :
    (centerCoreCommutator G).map e.toMonoidHom = centerCoreCommutator H := by
  unfold centerCoreCommutator
  rw [map_commutator, map_centerTwoCore, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr e.surjective]

/-- The two-core choice of product subgroup inside the centralizer residual. -/
def centralizerResidualCore (v : G) : Subgroup G :=
  (centralizerTwoResidual v).pCoreIn 2

/-- The center-commutator choice of product subgroup inside the residual. -/
def centralizerResidualCommutator (v : G) : Subgroup G :=
  (centerCoreCommutator (centralizerTwoResidual v)).map
    (centralizerTwoResidual v).subtype

theorem centralizerResidualCore_le (v : G) :
    centralizerResidualCore v ≤ centralizerTwoResidual v := pCoreIn_le _ _

theorem centralizerResidualCommutator_le (v : G) :
    centralizerResidualCommutator v ≤ centralizerTwoResidual v := map_subtype_le _

/-- Characteristicity is inside the residual, not in the ambient group. -/
theorem centralizerResidualCore_characteristic (v : G) :
    ((centralizerResidualCore v).subgroupOf (centralizerTwoResidual v)).Characteristic := by
  rw [centralizerResidualCore, pCoreIn, ← comap_subtype,
    comap_map_eq_self_of_injective (centralizerTwoResidual v).subtype_injective]
  infer_instance

/-- The center-commutator construction is characteristic in the residual. -/
theorem centralizerResidualCommutator_characteristic (v : G) :
    ((centralizerResidualCommutator v).subgroupOf (centralizerTwoResidual v)).Characteristic := by
  rw [centralizerResidualCommutator, ← comap_subtype,
    comap_map_eq_self_of_injective (centralizerTwoResidual v).subtype_injective]
  infer_instance

theorem map_centralizerResidualCore [Finite G] (e : G ≃* H) (v : G) :
    (centralizerResidualCore v).map e.toMonoidHom = centralizerResidualCore (e v) := by
  unfold centralizerResidualCore
  rw [map_pCoreIn_of_injective _ _ _ e.injective, map_centralizerTwoResidual]

theorem map_embedded_centerCoreCommutator (X : Subgroup G) (f : G →* H)
    (hf : Function.Injective f) :
    ((centerCoreCommutator X).map X.subtype).map f =
      (centerCoreCommutator (X.map f)).map (X.map f).subtype := by
  let e := X.equivMapOfInjective f hf
  calc
    _ = ((centerCoreCommutator X).map e.toMonoidHom).map (X.map f).subtype := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [map_centerCoreCommutator]

theorem map_centralizerResidualCommutator [Finite G] (e : G ≃* H) (v : G) :
    (centralizerResidualCommutator v).map e.toMonoidHom =
      centralizerResidualCommutator (e v) := by
  unfold centralizerResidualCommutator
  rw [map_embedded_centerCoreCommutator _ _ e.injective, map_centralizerTwoResidual]

end Theory.GroupTheory
