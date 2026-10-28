module

public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.GroupTheory.PGroup.NormalElementaryOrderJoin
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.PGroupCore

/-!
# Canonical candidates for an automorphism-invariant Held local pair

For a subgroup S of the actual degree-2058 Held group, take the centralizer
of its center and the normalizer of the join of its normal elementary
subgroups of order 64. Both constructions commute with automorphisms of
Held. In particular, an automorphism may exchange the two order-64
subgroups without affecting the second local.

The definitions here do not assert the finite local structure or generation.
Those calculations belong to the representative and assembly modules.
Source: Aschbacher--Smith, printed p.526; GLS3 Table 5.3p and its
interpretation of the two classes fused by Aut(He).
-/

@[expose] public section

namespace Held.AutomorphismLocalPair
open Subgroup

/-- The intrinsic center, embedded by the literal subgroup inclusion. -/
def centerSeed (S : Subgroup He) : Subgroup He := (center S).map S.subtype

/-- Join all normal elementary subgroups of order 64 inside S, then embed in Held. -/
def largeSeed (S : Subgroup He) : Subgroup He :=
  (normalElementaryOrderJoin 2 64 S).map S.subtype

/-- The first local candidate, with no choice of central involution. -/
def centerLocal (S : Subgroup He) : Subgroup He := centralizer (centerSeed S : Set He)

/-- The second local candidate, retaining both possible order-64 members. -/
def largeLocal (S : Subgroup He) : Subgroup He := normalizer (largeSeed S : Set He)

theorem mem_centerSeed (S : Subgroup He) (x : He) :
    x ∈ centerSeed S ↔ x ∈ S ∧ ∀ y ∈ S, y * x = x * y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, fun y hy => congrArg Subtype.val
      ((mem_center_iff.mp hx) ⟨y, hy⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)), rfl⟩

theorem mem_centerLocal (S : Subgroup He) (x : He) :
    x ∈ centerLocal S ↔ ∀ z ∈ centerSeed S, z * x = x * z :=
  mem_centralizer_iff

theorem mem_largeLocal (S : Subgroup He) (x : He) :
    x ∈ largeLocal S ↔ ∀ y : He,
      y ∈ largeSeed S ↔ x * y * x⁻¹ ∈ largeSeed S :=
  mem_normalizer_iff

theorem centerSeed_le (S : Subgroup He) : centerSeed S ≤ S := map_subtype_le _

theorem largeSeed_le (S : Subgroup He) : largeSeed S ≤ S := map_subtype_le _

theorem le_centerLocal (S : Subgroup He) : S ≤ centerLocal S := by
  intro x hx z hz
  exact ((mem_centerSeed S z).mp hz).2 x hx |>.symm

theorem le_largeLocal (S : Subgroup He) : S ≤ largeLocal S :=
  S.le_normalizer.trans (normalizer_le_normalizer_characteristic_image S _)

theorem centerSeed_map (S : Subgroup He) (e : MulAut He) :
    centerSeed (S.map e.toMonoidHom) = (centerSeed S).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hc⟩ := (mem_centerSeed _ _).mp hx
    obtain ⟨y, hy, rfl⟩ := hxS
    refine ⟨y, (mem_centerSeed _ _).mpr ⟨hy, ?_⟩, rfl⟩
    intro z hz
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc (e z) (mem_map_of_mem _ hz)
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyS, hc⟩ := (mem_centerSeed _ _).mp hy
    refine (mem_centerSeed _ _).mpr ⟨mem_map_of_mem _ hyS, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hc z hz)

theorem largeSeed_map (S : Subgroup He) (e : MulAut He) :
    largeSeed (S.map e.toMonoidHom) = (largeSeed S).map e.toMonoidHom := by
  unfold largeSeed
  let eS := S.equivMapOfInjective e.toMonoidHom e.injective
  rw [← map_normalElementaryOrderJoin 2 64 eS, map_map, map_map]
  congr 1

private theorem centralizer_map (K : Subgroup He) (e : MulAut He) :
    centralizer (K.map e.toMonoidHom : Set He) =
      (centralizer (K : Set He)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  · exact map_centralizer_le_centralizer_image _ e.toMonoidHom

theorem centerLocal_map (S : Subgroup He) (e : MulAut He) :
    centerLocal (S.map e.toMonoidHom) = (centerLocal S).map e.toMonoidHom := by
  rw [centerLocal, centerSeed_map, centralizer_map]
  rfl

theorem largeLocal_map (S : Subgroup He) (e : MulAut He) :
    largeLocal (S.map e.toMonoidHom) = (largeLocal S).map e.toMonoidHom := by
  rw [largeLocal, largeSeed_map, ← map_equiv_normalizer_eq]
  rfl

/-- Invariance uses setwise preservation of S, including for outer actors. -/
theorem locals_invariant (S : Subgroup He) (e : MulAut He)
    (h : S.map e.toMonoidHom = S) :
    (centerLocal S).map e.toMonoidHom = centerLocal S ∧
      (largeLocal S).map e.toMonoidHom = largeLocal S := by
  rw [← centerLocal_map, ← largeLocal_map, h]
  exact ⟨rfl, rfl⟩

/-- The concrete defining two-subgroup inside its own normalizer. -/
def largeKernel (S : Subgroup He) : Subgroup (largeLocal S) :=
  (largeSeed S).subgroupOf (largeLocal S)

theorem largeSeed_le_largeLocal (S : Subgroup He) : largeSeed S ≤ largeLocal S :=
  (largeSeed S).le_normalizer

instance largeKernel_normal (S : Subgroup He) : (largeKernel S).Normal :=
  (normal_subgroupOf_iff_le_normalizer (largeSeed_le_largeLocal S)).mpr le_rfl

theorem largeKernel_map (S : Subgroup He) :
    (largeKernel S).map (largeLocal S).subtype = largeSeed S :=
  map_subgroupOf_eq_of_le (largeSeed_le_largeLocal S)

theorem largeKernel_isPGroup (T : Sylow 2 He) : IsPGroup 2 (largeKernel T) :=
  (T.isPGroup'.to_le (largeSeed_le T)).comap_subtype

theorem largeKernel_le_pCore (T : Sylow 2 He) :
    largeKernel T ≤ pCore 2 (largeLocal T) :=
  le_sSup ⟨inferInstance, largeKernel_isPGroup T⟩

/-- The literal quotient by the defining normal subgroup, before identifying the full core. -/
abbrev LargeQuotient (S : Subgroup He) := largeLocal S ⧸ largeKernel S

def largeProjection (S : Subgroup He) : largeLocal S →* LargeQuotient S :=
  QuotientGroup.mk' (largeKernel S)

theorem largeProjection_ker (S : Subgroup He) :
    (largeProjection S).ker = largeKernel S := QuotientGroup.ker_mk' _

/-- Projection by the first local's actual intrinsic two-core. -/
def centerCoreProjection (S : Subgroup He) :
    centerLocal S →* centerLocal S ⧸ pCore 2 (centerLocal S) :=
  QuotientGroup.mk' (pCore 2 (centerLocal S))

/-- Projection by the second local's actual intrinsic two-core. -/
def largeCoreProjection (S : Subgroup He) :
    largeLocal S →* largeLocal S ⧸ pCore 2 (largeLocal S) :=
  QuotientGroup.mk' (pCore 2 (largeLocal S))

theorem centerCoreProjection_ker (S : Subgroup He) :
    (centerCoreProjection S).ker = pCore 2 (centerLocal S) := QuotientGroup.ker_mk' _

theorem largeCoreProjection_ker (S : Subgroup He) :
    (largeCoreProjection S).ker = pCore 2 (largeLocal S) := QuotientGroup.ker_mk' _

/-- The seed quotient surjects onto the actual core quotient; equality of the kernels
is not presumed. -/
def largeQuotientToCoreQuotient (T : Sylow 2 He) :
    LargeQuotient T →* largeLocal T ⧸ pCore 2 (largeLocal T) :=
  QuotientGroup.map (largeKernel T) (pCore 2 (largeLocal T))
    (MonoidHom.id _) (largeKernel_le_pCore T)

theorem largeQuotientToCoreQuotient_surjective (T : Sylow 2 He) :
    Function.Surjective (largeQuotientToCoreQuotient T) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (largeLocal T)) y
  exact ⟨largeProjection T x, rfl⟩

@[simp] theorem largeQuotientToCoreQuotient_projection (T : Sylow 2 He)
    (x : largeLocal T) :
    largeQuotientToCoreQuotient T (largeProjection T x) = largeCoreProjection T x :=
  QuotientGroup.map_mk' _ _ _ _ x

/-- Ambient self-centralization of the defining subgroup suffices for local characteristic two. -/
theorem largeLocal_selfCentralizingCore (T : Sylow 2 He)
    (hc : centralizer (largeSeed T : Set He) ≤ largeSeed T) :
    centralizer (pCore 2 (largeLocal T) : Set (largeLocal T)) ≤
      pCore 2 (largeLocal T) := by
  intro x hx
  apply largeKernel_le_pCore T
  apply hc
  intro y hy
  have hyK : (⟨y, largeSeed_le_largeLocal T hy⟩ : largeLocal T) ∈ largeKernel T := hy
  exact congrArg Subtype.val (hx _ (largeKernel_le_pCore T hyK))

end Held.AutomorphismLocalPair
