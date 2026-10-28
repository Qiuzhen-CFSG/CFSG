module

public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Faithful action on an irreducible section's orbit span

Restrict the original action to the span of the orbit of a seed, then use
its actual stabilizer-action image. The literal seed inside that subspace
remains in `Irr⁺`, its orbit spans the restricted module, and every original
seed stabilizer has image stabilizing the restricted seed.

The orbit comparison is proved after mapping back through the original
subspace inclusion. The surjection, faithful representation, image
subgroups, and pointwise kernel are the existing `InvariantAction` and
`SubspaceAction` constructions, so no arbitrary isomorphism changes the
actor or module markings.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.3, printed p.193.
-/

@[expose] public section
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Passing to the actual action image on a containing invariant subspace
preserves the seed's orbit span through the original inclusion. -/
theorem orbitSpan_restrictedSubgroup_map (W I : Submodule (ZMod 2) V)
    (A : Subgroup G) (hA : A ≤ subspaceStabilizer ρ W) (hIW : I ≤ W) :
    (orbitSpan (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A)
      (I.comap W.subtype)).map W.subtype = orbitSpan ρ A I := by
  simp only [orbitSpan, Submodule.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rintro v ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨g, hg, he⟩ := a.property
    have hv : (subspaceImageRepresentation ρ W a u : V) = ρ g u := by
      rw [← he]
      rfl
    change (subspaceImageRepresentation ρ W a u : V) ∈ _
    rw [hv]
    exact le_iSup (fun a : A => I.map (ρ a)) ⟨g, hg⟩ ⟨u, hu, rfl⟩
  · refine iSup_le fun a => ?_
    rintro v ⟨u, hu, rfl⟩
    let g : restrictedSubgroup ρ W A :=
      ⟨subgroupActionHom ρ W A hA a, ⟨⟨a, hA a.property⟩, a.property, rfl⟩⟩
    apply (le_iSup (fun a : restrictedSubgroup ρ W A =>
      ((I.comap W.subtype).map (subspaceImageRepresentation ρ W a)).map W.subtype) g)
    exact ⟨subspaceImageRepresentation ρ W g ⟨u, hIW hu⟩,
      ⟨⟨u, hIW hu⟩, hu, rfl⟩, rfl⟩

/-- The literal image of a seed stabilizer stabilizes its preimage inside
any subspace on which that image acts. -/
theorem restrictedSubgroup_le_subspaceStabilizer_comap
    (W I : Submodule (ZMod 2) V) {P : Subgroup G}
    (hP : P ≤ subspaceStabilizer ρ I) :
    restrictedSubgroup ρ W P ≤
      subspaceStabilizer (subspaceImageRepresentation ρ W) (I.comap W.subtype) := by
  apply le_subspaceStabilizer
  rintro a ⟨g, hg, rfl⟩ v hv
  exact (hP hg v).2 hv

/-- The image of the full ambient group is the entire stabilizer-action
image; the construction itself restricts to elements acting on the subspace. -/
theorem restrictedSubgroup_top (W : Submodule (ZMod 2) V) :
    restrictedSubgroup ρ W ⊤ = ⊤ := by
  apply top_unique
  intro a ha
  obtain ⟨g, rfl⟩ := (stabilizerRepresentation ρ W).asGroupHom.rangeRestrict_surjective a
  exact ⟨g, Subgroup.mem_top g, rfl⟩

/-- In the faithful action on the full orbit module, the original seed
still generates the whole module under its literal action image. -/
theorem orbitSpan_faithfulOrbit_eq_top (I : Submodule (ZMod 2) V) :
    orbitSpan (subspaceImageRepresentation ρ (orbitSpan ρ ⊤ I)) ⊤
      (I.comap (orbitSpan ρ ⊤ I).subtype) = ⊤ := by
  let W := orbitSpan ρ ⊤ I
  apply Submodule.map_injective_of_injective W.subtype_injective
  rw [Submodule.map_top, Submodule.range_subtype]
  have he := orbitSpan_restrictedSubgroup_map ρ W I ⊤
    (orbitSpan_invariant ρ ⊤ I) (le_orbitSpan ρ ⊤ I)
  rwa [restrictedSubgroup_top] at he

/-- Restriction to the orbit module and its faithful action image preserves
the original irreducible central section. -/
theorem isIrrPlus_faithfulOrbit {X : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ X I) :
    IsIrrPlus (subspaceImageRepresentation ρ (orbitSpan ρ ⊤ I))
      (restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X)
      (I.comap (orbitSpan ρ ⊤ I).subtype) :=
  hI.restricted ρ (le_top.trans (orbitSpan_invariant ρ ⊤ I)) (le_orbitSpan ρ ⊤ I)

/-- A specified seed stabilizer survives passage to the actual faithful
image on the orbit module, as used for the two-core in D.3.3. -/
theorem faithfulOrbit_seed_stabilized (I : Submodule (ZMod 2) V) {P : Subgroup G}
    (hP : P ≤ subspaceStabilizer ρ I) :
    restrictedSubgroup ρ (orbitSpan ρ ⊤ I) P ≤
      subspaceStabilizer (subspaceImageRepresentation ρ (orbitSpan ρ ⊤ I))
        (I.comap (orbitSpan ρ ⊤ I).subtype) :=
  restrictedSubgroup_le_subspaceStabilizer_comap ρ _ _ hP

end Representation.BinaryOffender.Homogeneous
