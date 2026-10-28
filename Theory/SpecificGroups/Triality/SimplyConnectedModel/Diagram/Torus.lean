module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Diagram.Pinned
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Orientation

/-!
# The diagram permutation on the genuine Spin coroot torus

Permuting the four integral coroot coordinates constructs a regular torus
isomorphism with a regular inverse. Any Spin point endomorphism transporting
the pinned simple roots restricts to this map: transport the source coroot
words and reorder their commuting product. In particular it preserves the
constructed closed maximal torus.

The actual simple cocharacters are sent by `ρ`, whereas pullback sends a
fundamental character at `i` to the character at `ρ⁻¹(i)`. Thus integral weight
coordinates pull back as `a ∘ ρ`. The final binary-weight lemmas compare both
forward and inverse pullback with the conventions in `SteinbergTensors.Orientation`.
No existence or regularity of an ambient diagram action is claimed here.

Source: GLS3, Theorems 1.12.1 and 1.15.2(a,b), and §1.14
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Diagram
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Pinning Pinning.CorootTorus
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Coroot parameters are pushed forward by the numbered arm cycle. -/
def permutedParameters (t : Fin 4 → kˣ) : Fin 4 → kˣ :=
  t ∘ typeD4DiagramPermutation.symm

/-- The regular Laurent coordinate permutation on the actual Spin torus. -/
def torusMap : AlgebraicGroup.Morphism (closedSubgroup k).carrierVariety
    (closedSubgroup k).carrierVariety :=
  (coordinateIso k).hom.comp
    ((dCharacterTupleMorphism 4 4 (fun j i =>
      if i = typeD4DiagramPermutation.symm j then 1 else 0)).comp (coordinateIso k).inv)

/-- Its point formula in the constructed integral coroot coordinates. -/
theorem torusMap_parameter (t : Fin 4 → kˣ) :
    (torusMap k).onPoints (parameterPoint k t) = parameterPoint k (permutedParameters k t) := by
  change (coordinateIso k).hom.onPoints
    ((dCharacterTupleMorphism 4 4 _).onPoints
      ((coordinateIso k).inv.onPoints (parameterPoint k t))) = _
  rw [coordinateIso_inv_parameter, coordinateIso_hom_apply]
  congr 1
  funext j
  rw [dCharacterTupleMorphism_apply, Equiv.apply_symm_apply]
  simp [permutedParameters]

private theorem parameterPoint_surjective : Function.Surjective (parameterPoint k) := by
  intro t
  obtain ⟨x, hx⟩ := (coordinateIso k).toMulEquiv.surjective t
  exact ⟨dPointEquiv 4 x, (coordinateIso_hom_apply k x).symm.trans hx⟩

/-- The coordinate cycle has cube equal to the identity. -/
theorem torusMap_cube (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (torusMap k).onPoints ((torusMap k).onPoints ((torusMap k).onPoints t)) = t := by
  obtain ⟨t, rfl⟩ := parameterPoint_surjective k t
  simp only [torusMap_parameter]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [IsAlgClosed k] [CharP k 2] in
private theorem cube_left {G : Variety k} [AlgebraicGroup G]
    (f : AlgebraicGroup.Morphism G G)
    (hf : ∀ x, f.onPoints (f.onPoints (f.onPoints x)) = x) :
    ∀ x, (f.comp f).onPoints (f.onPoints x) = x := hf

omit [IsAlgClosed k] [CharP k 2] in
private theorem cube_right {G : Variety k} [AlgebraicGroup G]
    (f : AlgebraicGroup.Morphism G G)
    (hf : ∀ x, f.onPoints (f.onPoints (f.onPoints x)) = x) :
    ∀ x, f.onPoints ((f.comp f).onPoints x) = x := hf

/-- The torus isomorphism has its square as regular inverse. -/
def torusIso : AlgebraicGroup.Iso (closedSubgroup k).carrierVariety
    (closedSubgroup k).carrierVariety where
  hom := torusMap k
  inv := (torusMap k).comp (torusMap k)
  hom_inv_id := by exact cube_left k (torusMap k) (torusMap_cube k)
  inv_hom_id := by exact cube_right k (torusMap k) (torusMap_cube k)

/-- Transport of the ordered product uses commutativity of the actual coroots. -/
theorem IsPinned.parameter {f : Points k →* Points k} (hf : IsPinned k f)
    (t : Fin 4 → kˣ) :
    f (parameter k t) = parameter k (permutedParameters k t) := by
  have hp := typeD4DiagramPermutation.ofFn_comp_perm
    (fun i => Pinning.simpleCoroot k i (permutedParameters k t i))
  have hc : (List.ofFn (fun i => Pinning.simpleCoroot k (typeD4DiagramPermutation i) (t i))).Pairwise Commute := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact corootWord_commute k _ _ _ _
  simp only [Function.comp_def, permutedParameters, Equiv.symm_apply_apply] at hp
  change f ((List.ofFn fun i => Pinning.simpleCoroot k i (t i)).prod) = _
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, hf.simpleCoroot k]
  exact hp.prod_eq' hc

/-- Every pinned point map restricts to the explicitly constructed regular torus map. -/
theorem IsPinned.torus_inclusion {f : Points k →* Points k} (hf : IsPinned k f)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    f ((closedSubgroup k).includePoint t) =
      (closedSubgroup k).includePoint ((torusMap k).onPoints t) := by
  obtain ⟨x, rfl⟩ := (coordinateIso k).toMulEquiv.surjective t
  change f ((closedSubgroup k).inclusion.onPoints ((coordinateIso k).hom.onPoints x)) =
    (closedSubgroup k).inclusion.onPoints ((torusMap k).onPoints ((coordinateIso k).hom.onPoints x))
  rw [coordinateIso_hom_apply, torusMap_parameter, inclusion_parameterPoint,
    inclusion_parameterPoint, hf.parameter k]

/-- The constructed closed maximal torus is preserved in both directions. -/
theorem IsPinned.torus_mem_iff {f : Points k →* Points k} (hf : IsPinned k f) (g : Points k) :
    f g ∈ (closedSubgroup k).toSubgroup ↔ g ∈ (closedSubgroup k).toSubgroup := by
  have hmem (x : Points k) (hx : x ∈ (closedSubgroup k).toSubgroup) :
      f x ∈ (closedSubgroup k).toSubgroup := by
    obtain ⟨t, rfl⟩ := (mem_iff_parameter k x).mp hx
    rw [hf.parameter k]
    exact parameter_mem k _
  refine ⟨fun h => ?_, hmem g⟩
  simpa only [hf.cube k] using hmem (f (f g)) (hmem (f g) h)

/-- Pullback of an integral weight is precomposition with the forward diagram cycle. -/
theorem weightEmbedding_pullback (a : Fin 4 → ℤ)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (weightEmbedding k (a ∘ typeD4DiagramPermutation)).pointCharacter t =
      (weightEmbedding k a).pointCharacter ((torusMap k).onPoints t) := by
  obtain ⟨x, rfl⟩ := (coordinateIso k).toMulEquiv.surjective t
  change (weightEmbedding k (a ∘ typeD4DiagramPermutation)).pointCharacter
      ((coordinateIso k).hom.onPoints x) =
    (weightEmbedding k a).pointCharacter ((torusMap k).onPoints ((coordinateIso k).hom.onPoints x))
  rw [coordinateIso_hom_apply, torusMap_parameter, weightEmbedding_parameter,
    weightEmbedding_parameter]
  simpa [permutedParameters] using
    Equiv.prod_comp typeD4DiagramPermutation
      (fun i => ((dPointEquiv 4 x) (typeD4DiagramPermutation.symm i) : k) ^ a i)

/-- The fundamental character index transforms by the inverse permutation. -/
theorem fundamentalCharacter_pullback (i : Fin 4)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (fundamentalCharacter k i).pointCharacter ((torusMap k).onPoints t) =
      (fundamentalCharacter k (typeD4DiagramPermutation.symm i)).pointCharacter t := by
  obtain ⟨x, rfl⟩ := (coordinateIso k).toMulEquiv.surjective t
  change (fundamentalCharacter k i).pointCharacter
      ((torusMap k).onPoints ((coordinateIso k).hom.onPoints x)) =
    (fundamentalCharacter k (typeD4DiagramPermutation.symm i)).pointCharacter
      ((coordinateIso k).hom.onPoints x)
  rw [coordinateIso_hom_apply, torusMap_parameter, fundamentalCharacter_parameter,
    fundamentalCharacter_parameter]
  rfl

open D4RestrictedWeight

/-- Equality of the actual algebraic characters, not just their formal labels. -/
theorem weightEmbedding_comp (a : Fin 4 → ℤ) :
    (weightEmbedding k a).comp (torusMap k) =
      weightEmbedding k (a ∘ typeD4DiagramPermutation) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  exact (weightEmbedding_pullback k a t).symm

/-- Inverse graph pullback uses the literal inverse diagram permutation. -/
theorem weightEmbedding_inverse_pullback (a : Fin 4 → ℤ)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (weightEmbedding k (a ∘ typeD4DiagramPermutation.symm)).pointCharacter t =
      (weightEmbedding k a).pointCharacter ((torusIso k).inv.onPoints t) := by
  have h := weightEmbedding_pullback k (a ∘ typeD4DiagramPermutation.symm)
    ((torusIso k).inv.onPoints t)
  have hc : (a ∘ typeD4DiagramPermutation.symm) ∘ typeD4DiagramPermutation = a := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hc] at h
  change (weightEmbedding k a).pointCharacter ((torusIso k).inv.onPoints t) =
    (weightEmbedding k (a ∘ typeD4DiagramPermutation.symm)).pointCharacter
      ((torusIso k).hom.onPoints ((torusIso k).inv.onPoints t)) at h
  rw [(torusIso k).inv_hom_id] at h
  exact h.symm

/-- Agreement with the forward binary-weight convention. -/
theorem basicWeight_pullback (a : BasicWeight)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (weightEmbedding k (coefficient (diagramAction a))).pointCharacter t =
      (weightEmbedding k (coefficient a)).pointCharacter ((torusMap k).onPoints t) :=
  weightEmbedding_pullback k (coefficient a) t

/-- Agreement with the inverse graph convention at a graph-field exponent boundary. -/
theorem basicWeight_inverse_pullback (a : BasicWeight)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (weightEmbedding k (coefficient
      (Triality.RestrictedWeights.SteinbergTensors.inverseDiagramAction a))).pointCharacter t =
      (weightEmbedding k (coefficient a)).pointCharacter ((torusIso k).inv.onPoints t) := by
  rw [Triality.RestrictedWeights.SteinbergTensors.inverseDiagramAction_eq_pullback]
  exact weightEmbedding_inverse_pullback k (coefficient a) t

/-- The realized simple cocharacter is the corresponding single coroot parameter. -/
theorem simpleCoroot_parameter (i : Fin 4) (t : Variety.Point (KMult k)) :
    ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t =
      parameterPoint k (Function.update (fun _ => 1) i (dPointEquiv 1 t 0)) := by
  apply (closedSubgroup k).inclusion_injective
  exact (pinnedRootData_rootCocharacter k _ t).trans
    (inclusion_single_parameter k i (dPointEquiv 1 t 0)).symm

/-- The regular torus map permutes the actual simple cocharacter morphisms by `ρ`. -/
theorem torusMap_simpleCoroot (i : Fin 4) :
    (torusMap k).comp ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))) =
      (pinnedRootData k).rootCocharacter
        (pinnedRootIndex k (simpleRoot (typeD4DiagramPermutation i))) := by
  apply AlgebraicGroup.Morphism.ext
  funext t
  change (torusMap k).onPoints
    (((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t) = _
  rw [simpleCoroot_parameter, torusMap_parameter]
  change parameterPoint k _ =
    ((pinnedRootData k).rootCocharacter
      (pinnedRootIndex k (simpleRoot (typeD4DiagramPermutation i)))).onPoints t
  rw [simpleCoroot_parameter]
  congr 1
  funext j
  by_cases h : typeD4DiagramPermutation.symm j = i
  · have hj : j = typeD4DiagramPermutation i := by
      rw [← h, Equiv.apply_symm_apply]
    simp [permutedParameters, hj]
  · have hj : j ≠ typeD4DiagramPermutation i := by
      intro hj
      apply h
      simp [hj]
    simp [permutedParameters, h, hj]

end Triality.SimplyConnected.Diagram
