module

public import Theory.GroupTheory.ReducedNormal.Representation
public import Theory.Representation.BinaryOffender.Homogeneous.Embedding

/-!
# The actual inclusion between reduced-normal modules

Given H ≤ M and the ambient inclusion R₂(H) ≤ R₂(M), construct the
literal homomorphism between these subgroups and its canonical binary
linear map. Both actions are original conjugation, so the map is
injective and equivariant. It preserves Irr⁺, the original seed
stabilizers, and the underlying subgroup of the original ambient group.

The reduced-subgroup inclusion is supplied by A.1.11, through
`reducedPSubgroup_ambient_le` or its FSU consumer. These results implement
the module inclusion in Aschbacher–Smith, Lemma 3.2.2, combined manuscript
of 1 March 2004, printed p.579.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] {H M : Subgroup G}
  (hHM : H ≤ M)
  (hR : (ModuleGroup H).map H.subtype ≤ (ModuleGroup M).map M.subtype)

/-- The literal multiplicative inclusion R₂(H) → R₂(M). -/
def groupInclusion : ModuleGroup H →* ModuleGroup M :=
  (((inclusion hHM).comp (ModuleGroup H).subtype).codRestrict (ModuleGroup M) fun v => by
    apply (mem_map_iff_mem M.subtype_injective).mp
    exact hR (mem_map_of_mem H.subtype v.property))

/-- The same inclusion on the canonical binary modules. -/
noncomputable def moduleInclusion :
    Additive (ModuleGroup H) →ₗ[ZMod 2] Additive (ModuleGroup M) :=
  (groupInclusion hHM hR).toAdditive.toZModLinearMap 2

theorem moduleInclusion_injective : Function.Injective (moduleInclusion hHM hR) := by
  intro v w he
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Additive (ModuleGroup M) => x.toMul.val.val) he

/-- Both sides are the original conjugation in G. -/
theorem moduleInclusion_equivariant (h : H) (v : Additive (ModuleGroup H)) :
    moduleInclusion hHM hR (representation H h v) =
      representation M (inclusion hHM h) (moduleInclusion hHM hR v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem subgroupOf_map_inclusion (P : Subgroup G) (hPH : P ≤ H) :
    (P.subgroupOf H).map (inclusion hHM) = P.subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [map_map, map_subgroupOf_eq_of_le (hPH.trans hHM)]
  change (P.subgroupOf H).map H.subtype = P
  exact map_subgroupOf_eq_of_le hPH

/-- An Irr⁺ seed for the original actor remains Irr⁺ in the larger
reduced-normal module, with the actual actor inclusion. -/
theorem isIrrPlus_ambientInclusion {X : Subgroup G} (hXH : X ≤ H)
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hI : IsIrrPlus (representation H) (X.subgroupOf H) I) :
    IsIrrPlus (representation M) (X.subgroupOf M) (I.map (moduleInclusion hHM hR)) := by
  have h := hI.map_equivariant_embedding (representation H) (representation M)
    (inclusion hHM) (moduleInclusion hHM hR) (moduleInclusion_equivariant hHM hR)
    (moduleInclusion_injective hHM hR)
  rwa [subgroupOf_map_inclusion hHM X hXH] at h

/-- The original seed's stabilizing subgroup is preserved by the actual
reduced-normal inclusion; in FSU this is the two-core of X T. -/
theorem stabilizer_ambientInclusion {P : Subgroup G} (hPH : P ≤ H)
    {I : Submodule (ZMod 2) (Additive (ModuleGroup H))}
    (hP : P.subgroupOf H ≤ subspaceStabilizer (representation H) I) :
    P.subgroupOf M ≤ subspaceStabilizer (representation M) (I.map (moduleInclusion hHM hR)) := by
  have h := map_le_subspaceStabilizer_embedding (representation H) (representation M)
    (inclusion hHM) (moduleInclusion hHM hR) (moduleInclusion_equivariant hHM hR) hP
  rwa [subgroupOf_map_inclusion hHM P hPH] at h

/-- The image subspace is exactly the same subgroup of the original
ambient group before and after the module inclusion. -/
theorem subspaceImage_moduleInclusion
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H))) :
    subspaceImage M (I.map (moduleInclusion hHM hR)) = subspaceImage H I := by
  ext g
  constructor
  · rintro ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨v.toMul, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨Additive.ofMul v, hv, rfl⟩, rfl⟩, rfl⟩

end Theory.GroupTheory.ReducedNormal
