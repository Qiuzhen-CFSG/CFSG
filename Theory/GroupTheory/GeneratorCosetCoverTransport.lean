module
public import Theory.GroupTheory.GeneratorCosetCoverIndex
/-!
# Transport of coset covers through surjective homomorphisms

A cover of `H` in a generated group descends through a surjective homomorphism
to a cover of any subgroup containing the image of `H`. The target generating
family may be different: lift a target element, use the original cover, and
map its subgroup-witness equality. This proves both positive and inverse
transitions in the target group without assuming a relation between generator
labels. The argument is the usual image-of-cosets argument for index bounds.
-/

namespace Subgroup.GeneratorCosetCover
/-- Descend a cover and enlarge its subgroup, with arbitrary target generators. -/
public def mapSurjective {G G' α β ι : Type*} [Group G] [Group G']
    {H : Subgroup G} {g : α → G} (C : Subgroup.GeneratorCosetCover H g ι)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (f : G →* G') (hf : Function.Surjective f)
    (K : Subgroup G') (hK : H.map f ≤ K) (g' : β → G') :
    Subgroup.GeneratorCosetCover K g' ι := by
  have step (i : ι) (y : G') :
      ∃ h : K, ∃ j, f (C.repr i) * y = h.val * f (C.repr j) := by
    obtain ⟨x, hx⟩ := hf (f (C.repr i) * y)
    obtain ⟨h, j, hj⟩ := C.covers hgen x
    refine ⟨⟨f h, hK (Subgroup.mem_map.mpr ⟨h, h.property, rfl⟩)⟩, j, ?_⟩
    change f (C.repr i) * y = f h * f (C.repr j)
    rw [← hx, hj, map_mul]
  exact {
    repr := fun i => f (C.repr i)
    initial := C.initial
    initial_eq := by rw [C.initial_eq, map_one]
    step := fun i a => step i (g' a)
    inv_step := fun i a => step i ((g' a)⁻¹) }
end Subgroup.GeneratorCosetCover
