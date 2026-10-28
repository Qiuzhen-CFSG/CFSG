module
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.IrreducibleTransport
/-!
# Equivariant embeddings of irreducible sections

An injective equivariant linear map preserves Irr⁺ when the actor is
replaced by its literal image under a homomorphism. First use the existing
embedding theorem for the target action composed with that homomorphism;
then descend along the surjection from the original actor to its image.
Stabilizers and orbit spans also transport through the specified map.

This supplies the passage from the reduced module of L₀T to that of M
in Aschbacher–Smith, Lemma 3.2.2, combined manuscript of 1 March 2004,
printed p.579, with the Irr⁺ convention of Definition A.1.40.
-/

@[expose] public section
open Subgroup
namespace Representation.BinaryOffender
variable {D E V W : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) E W)
  (f : D →* E) (j : V →ₗ[ZMod 2] W)
  (hact : ∀ g v, j (ρ g v) = σ (f g) (j v))

include hact in
/-- A stabilizing subgroup acts on the actual image subspace. -/
theorem map_le_subspaceStabilizer_embedding {P : Subgroup D} {I : Submodule (ZMod 2) V}
    (hP : P ≤ subspaceStabilizer ρ I) :
    P.map f ≤ subspaceStabilizer σ (I.map j) := by
  apply le_subspaceStabilizer
  rintro _ ⟨g, hg, rfl⟩ _ ⟨v, hv, rfl⟩
  exact ⟨ρ g v, (hP hg v).2 hv, hact g v⟩

include hact in
/-- Irr⁺ is preserved by an injective equivariant inclusion with its
literal image actor, without surjectivity of the ambient group map. -/
theorem IsIrrPlus.map_equivariant_embedding (hj : Function.Injective j)
    {K : Subgroup D} {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    IsIrrPlus σ (K.map f) (I.map j) := by
  have hcomp : IsIrrPlus (σ.comp f) K (I.map j) := by
    apply IsIrrPlus.map_embedding (σ.comp f) ρ (MonoidHom.id D) j hj
      (fun g v => (hact g v).symm) K I
    simpa only [Subgroup.map_id] using hI
  exact hcomp.of_intertwining (σ.comp f) σ (f.subgroupMap K)
    (f.subgroupMap_surjective K) (LinearMap.id) Function.injective_id
    (fun _ _ => rfl) (by simp)

namespace Homogeneous
include hact in
/-- Equivariant inclusions commute with the original orbit span and
literal image of its acting subgroup. -/
theorem orbitSpan_map_equivariant (T : Subgroup D) (I : Submodule (ZMod 2) V) :
    (orbitSpan ρ T I).map j = orbitSpan σ (T.map f) (I.map j) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply iSup_le
    rintro t _ ⟨v, hv, rfl⟩
    change j (ρ t v) ∈ orbitSpan σ (T.map f) (I.map j)
    rw [hact]
    exact (le_iSup (fun t : T.map f => (I.map j).map (σ t))
      ⟨f t, mem_map_of_mem f t.property⟩) ⟨j v, ⟨v, hv, rfl⟩, rfl⟩
  · apply iSup_le
    rintro ⟨_, g, hg, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ g v, (le_iSup (fun t : T => I.map (ρ t)) ⟨g, hg⟩)
      ⟨v, hv, rfl⟩, hact g v⟩
end Homogeneous
end Representation.BinaryOffender
