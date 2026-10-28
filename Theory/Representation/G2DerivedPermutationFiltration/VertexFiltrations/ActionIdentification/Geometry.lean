module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.ActionIdentification.GeometryData
/-!
# Geometric certificates for the two binary G₂ parabolic actions

The images of a fixed three-point line and a fixed point separate the 63
published coset representatives. Their known coset counts give coverage;
finite action checks then identify both literal generator tables.
This supports Aschbacher–Smith G.7.2(3), printed p.348.
The byte tables below are evaluated from the root words in Coordinates;
their use is certified by kernel reduction, not by the generating script.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
open scoped Pointwise
namespace G2DerivedPermutationFiltration.VertexCoordinates
set_option maxRecDepth 10000
open ActionGeometry

private theorem unipotent_le_of_roots (S : Subgroup FullGroup)
    (h : ∀ j : Fin 6, rootGenerator ⟨j.val, by omega⟩ ∈ S) :
    Atlas.G2.unipotent ≤ S := by
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

private theorem torus_le (S : Subgroup FullGroup) : splitTorus ≤ S := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  have ha : a = 1 := Subsingleton.elim _ _
  have hb : b = 1 := Subsingleton.elim _ _
  subst a; subst b
  change torus 1 1 ∈ S
  have he : torus (1 : (ZMod 2)ˣ) 1 = 1 := by
    exact map_one torusHom
  rw [he]
  exact S.one_mem

private theorem parabolic_fixes_base (i : Fin 2) :
    parabolic i ≤ MulAction.stabilizer FullGroup (base i) := by
  let S := MulAction.stabilizer FullGroup (base i)
  have hu : Atlas.G2.unipotent ≤ S := unipotent_le_of_roots S (fun j =>
    root_fixes_base i ⟨j.val, by omega⟩ (Or.inl j.isLt))
  fin_cases i
  · apply sup_le hu ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl : x = weylS)
    change rootGenerator 7 • base 0 = base 0
    exact root_fixes_base 0 7 (Or.inr rfl)
  · apply sup_le (sup_le hu (torus_le S)) ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl : x = weylR)
    change rootGenerator 6 • base 1 = base 1
    exact root_fixes_base 1 6 (Or.inr rfl)

private def geometricVertex (i : Fin 2) : Vertex i → Finset (Carrier (ZMod 2)) :=
  Quotient.lift (fun g : FullGroup => g • base i) (by
    intro a b hab
    have hm := parabolic_fixes_base i ((QuotientGroup.leftRel_apply).mp hab)
    change (a⁻¹ * b) • base i = base i at hm
    have he := congrArg (fun s => a • s) hm
    simpa only [← SemigroupAction.mul_smul, mul_inv_cancel_left] using he.symm)

private theorem geometricVertex_vertex (i : Fin 2) (x : Fin 63) :
    geometricVertex i (vertex i x) = image i x := representative_images i x

 theorem vertex_injective (i : Fin 2) : Function.Injective (vertex i) := by
  intro a b hab
  apply image_injective i
  simpa only [geometricVertex_vertex] using congrArg (geometricVertex i) hab

 theorem vertex_bijective (i : Fin 2) : Function.Bijective (vertex i) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨vertex_injective i, by rw [Fintype.card_fin, card_vertices]⟩

private theorem geometricVertex_injective (i : Fin 2) : Function.Injective (geometricVertex i) := by
  intro a b hab
  obtain ⟨x,rfl⟩ := (vertex_bijective i).surjective a
  obtain ⟨y,rfl⟩ := (vertex_bijective i).surjective b
  rw [geometricVertex_vertex, geometricVertex_vertex] at hab
  exact congrArg (vertex i) (image_injective i hab)

 theorem vertex_generator_action (i j : Fin 2) (x : Fin 63) :
    vertex i (generator i j x) = vertexPerm i (groupGenerator j) (vertex i x) := by
  apply geometricVertex_injective i
  rw [geometricVertex_vertex]
  change image i (generator i j x) =
    (ambientGenerator j * (evalWord (representativeWord i x))⁻¹) • base i
  rw [SemigroupAction.mul_smul, representative_images, generator_images]

end G2DerivedPermutationFiltration.VertexCoordinates
