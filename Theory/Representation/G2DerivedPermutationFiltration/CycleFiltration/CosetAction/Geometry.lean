module

public import Theory.Representation.G2DerivedPermutationFiltration.CycleFiltration.CosetAction.GeometryData

/-!
# The literal enumeration is the actual G₂ unipotent-coset action

The standard unipotent subgroup fixes the base line–point pair. The checked
images therefore distinguish actual left cosets; the known index 189 proves
coverage. Both endpoint tables agree with the actual parabolic projections.
The finite geometric action certificates then identify all eight ambient and
two derived permutations. The Schreier equations state explicitly how GAP
right cosets and inverse actors become Lean left cosets and left actions.
No normality of the unipotent subgroup is assumed.

Witness provenance and ATLAS attribution are in Data and source/README.md.
Source application: Aschbacher–Smith G.7.2(3), printed p.348 / PDF p.359.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
open scoped Pointwise
namespace G2DerivedPermutationFiltration.CycleFlagCoordinates
open VertexCoordinates VertexCoordinates.ActionGeometry
set_option maxRecDepth 16000

private theorem unipotent_fixes_base (i : Fin 2) :
    Atlas.G2.unipotent ≤ MulAction.stabilizer FullGroup (base i) := by
  let S := MulAction.stabilizer FullGroup (base i)
  have h (j : Fin 6) : rootGenerator ⟨j.val, by omega⟩ ∈ S :=
    root_fixes_base i _ (Or.inl j.isLt)
  have hr (r : ZMod 2 → FullGroup) (h0 : r 0 = 1) (h1 : r 1 ∈ S) :
      ∀ a, r a ∈ S := by
    intro a
    have ha : a = 0 ∨ a = 1 := (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
    rcases ha with rfl | rfl
    · rw [h0]; exact S.one_mem
    · exact h1
  rw [Atlas.G2.unipotent, Subgroup.closure_le]
  simp only [Set.union_subset_iff, Set.range_subset_iff]
  exact ⟨⟨⟨⟨⟨hr rootA rootA_zero (h 0), hr rootB rootB_zero (h 1)⟩,
    hr rootC rootC_zero (h 2)⟩, hr rootD rootD_zero (h 3)⟩,
    hr rootE rootE_zero (h 4)⟩, hr rootF rootF_zero (h 5)⟩

private theorem parabolic_fixes_base (i : Fin 2) :
    parabolic i ≤ MulAction.stabilizer FullGroup (base i) := by
  let S := MulAction.stabilizer FullGroup (base i)
  have hu : Atlas.G2.unipotent ≤ S := unipotent_fixes_base i
  have ht : splitTorus ≤ S := by
    rintro _ ⟨⟨a,b⟩,rfl⟩
    have ha : a = 1 := Subsingleton.elim _ _
    have hb : b = 1 := Subsingleton.elim _ _
    subst a; subst b
    change torus 1 1 ∈ S
    rw [show torus (1 : (ZMod 2)ˣ) 1 = 1 from map_one torusHom]
    exact S.one_mem
  fin_cases i
  · apply sup_le hu ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl : x = weylS)
    exact root_fixes_base 0 7 (Or.inr rfl)
  · apply sup_le (sup_le hu ht) ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl : x = weylR)
    exact root_fixes_base 1 6 (Or.inr rfl)

private def geometricVertex (i : Fin 2) : Vertex i → Finset (Carrier (ZMod 2)) :=
  Quotient.lift (fun g : FullGroup => g • base i) (by
    intro a b hab
    have hm := parabolic_fixes_base i ((QuotientGroup.leftRel_apply).mp hab)
    change (a⁻¹ * b) • base i = base i at hm
    have he := congrArg (fun s => a • s) hm
    simpa only [← SemigroupAction.mul_smul, mul_inv_cancel_left] using he.symm)

private theorem geometricVertex_vertex (i : Fin 2) (x : Fin 63) :
    geometricVertex i (vertex i x) = image i x := ActionGeometry.representative_images i x

private theorem geometricVertex_injective (i : Fin 2) : Function.Injective (geometricVertex i) := by
  intro a b hab
  obtain ⟨x,rfl⟩ := (vertex_bijective i).surjective a
  obtain ⟨y,rfl⟩ := (vertex_bijective i).surjective b
  rw [geometricVertex_vertex, geometricVertex_vertex] at hab
  exact congrArg (vertex i) (image_injective i hab)

/-- The literal endpoint tables agree with the two actual parabolic quotients. -/
theorem projection_flag (i : Fin 2) (x : Fin 189) :
    projection i (flag x) = vertex i (endpoint i x) := by
  apply geometricVertex_injective i
  rw [geometricVertex_vertex]
  exact representative_images x i

/-- The published 189 representatives are distinct actual unipotent cosets. -/
theorem flag_injective : Function.Injective flag := by
  intro x y h
  apply endpoints_injective
  apply Prod.ext
  · apply vertex_injective 0
    simpa only [projection_flag] using congrArg (projection 0) h
  · apply vertex_injective 1
    simpa only [projection_flag] using congrArg (projection 1) h

/-- The known unipotent index turns separation into exhaustive enumeration. -/
theorem flag_bijective : Function.Bijective flag := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨flag_injective, by rw [Fintype.card_fin, card_flags]⟩

noncomputable def flagEquiv : Fin 189 ≃ Flag := Equiv.ofBijective flag flag_bijective

@[simp] theorem flagEquiv_apply (x : Fin 189) : flagEquiv x = flag x := rfl

private theorem projections_injective : Function.Injective (fun f : Flag =>
    (projection 0 f, projection 1 f)) := by
  intro a b h
  obtain ⟨x,rfl⟩ := flag_bijective.surjective a
  obtain ⟨y,rfl⟩ := flag_bijective.surjective b
  apply congrArg flag
  apply endpoints_injective
  apply Prod.ext
  · apply vertex_injective 0
    simpa only [projection_flag] using congrArg Prod.fst h
  · apply vertex_injective 1
    simpa only [projection_flag] using congrArg Prod.snd h

private theorem flag_action_of_images (g : FullGroup) (x y : Fin 189)
    (h : ∀ i, g • flagImage x i = flagImage y i) : g • flag x = flag y := by
  apply projections_injective
  have hp (i : Fin 2) : projection i (g • flag x) = projection i (flag y) := by
    apply geometricVertex_injective i
    change (g * (evalWord (representativeWord x))⁻¹) • base i =
      (evalWord (representativeWord y))⁻¹ • base i
    rw [SemigroupAction.mul_smul, representative_images, representative_images]
    exact h i
  exact Prod.ext (hp 0) (hp 1)

/-- All eight ambient root/Weyl permutations on the actual flag space. -/
theorem ambient_flag_action (j : Fin 8) (x : Fin 189) :
    rootGenerator j • flag x = flag (ambientTable j x) :=
  flag_action_of_images _ _ _ (ambient_images j x)

/-- The two inverse GAP words act by the original saved flag permutations. -/
theorem derived_flag_action (j : Fin 2) (x : Fin 189) :
    flagPerm (groupGenerator j) (flag x) = flag (derivedTable j x) :=
  flag_action_of_images _ _ _ (derived_images j x)

/-- Exact right-coset/left-action conversion, including multiplication order. -/
theorem derived_flag_action_iff (j : Fin 2) (x y : Fin 189) :
    flagPerm (groupGenerator j) (flag x) = flag y ↔
      evalWord (representativeWord x) * evalWord (generatorWord j) *
        (evalWord (representativeWord y))⁻¹ ∈ unipotent := by
  change QuotientGroup.mk
      ((evalWord (generatorWord j))⁻¹ * (evalWord (representativeWord x))⁻¹) =
    (QuotientGroup.mk (evalWord (representativeWord y))⁻¹ : Flag) ↔ _
  rw [QuotientGroup.eq]
  simp only [mul_inv_rev, inv_inv]

/-- Right-coset transport for an arbitrary ambient root/Weyl letter. -/
theorem ambient_flag_action_iff (j : Fin 8) (x y : Fin 189) :
    rootGenerator j • flag x = flag y ↔
      evalWord (representativeWord x) * (rootGenerator j)⁻¹ *
        (evalWord (representativeWord y))⁻¹ ∈ unipotent := by
  change QuotientGroup.mk (rootGenerator j * (evalWord (representativeWord x))⁻¹) =
    (QuotientGroup.mk (evalWord (representativeWord y))⁻¹ : Flag) ↔ _
  rw [QuotientGroup.eq]
  simp only [mul_inv_rev, inv_inv]

/-- The ambient GAP Schreier products use involutory root/Weyl letters. -/
theorem ambient_schreier_mem (j : Fin 8) (x : Fin 189) :
    evalWord (representativeWord x) * rootGenerator j *
      (evalWord (representativeWord (ambientTable j x)))⁻¹ ∈ unipotent := by
  have h := (ambient_flag_action_iff j x _).mp (ambient_flag_action j x)
  rwa [rootGenerator_inv] at h

/-- Each saved GAP right-coset Schreier product lies in the actual U. -/
theorem derived_schreier_mem (j : Fin 2) (x : Fin 189) :
    evalWord (representativeWord x) * evalWord (generatorWord j) *
      (evalWord (representativeWord (derivedTable j x)))⁻¹ ∈ unipotent :=
  (derived_flag_action_iff j x _).mp (derived_flag_action j x)

end G2DerivedPermutationFiltration.CycleFlagCoordinates
