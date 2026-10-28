module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Data

/-!
# Three generators of the actual outer M₁₂ overlap

The original quaternion generator `leftI`, the compatible split movement
involution, and the extra involution give 128 distinct words in the literal
overlap. The proved overlap order therefore makes these words exhaustive.
The checked three-point permutation signatures prove distinctness
without comparing the large permutation words pairwise. Homomorphisms out of
the overlap are consequently determined by these three marked generators.

Only the whole overlap is coordinatized here. The order-64 split movement
subgroup is not identified with the nonsplit first core. Source context:
Aschbacher--Smith F.1.12(I)(13), p.263, and 14.2.21, p.988; degree-24 ATLAS
coordinates and attribution are retained from the imported concrete modules.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
set_option maxRecDepth 100000
namespace FiniteWords
variable {G H : Type*} [Group G] [Group H] {n m : ℕ}

def evaluate (g : Fin n → G) : List (Fin n) → G
  | [] => 1
  | j :: w => g j * evaluate g w

theorem map_evaluate (f : G →* H) (g : Fin n → G) (w : List (Fin n)) :
    f (evaluate g w) = evaluate (fun j => f (g j)) w := by
  induction w with
  | nil => exact map_one f
  | cons j w ih => simp only [evaluate, map_mul, ih]

theorem hom_ext (g : Fin n → G) (words : Fin m → List (Fin n))
    (hs : Function.Surjective (fun i => evaluate g (words i)))
    (f h : G →* H) (he : ∀ j, f (g j) = h (g j)) : f = h := by
  apply MonoidHom.ext
  intro x
  obtain ⟨i, rfl⟩ := hs x
  rw [map_evaluate, map_evaluate]
  exact congrArg (fun k => evaluate k (words i)) (funext he)

end FiniteWords
namespace Overlap
open SecondCoordinates

def generator (i : Fin 3) : overlap :=
  ⟨![leftI, swap, extra] i, by
    fin_cases i
    · have h := movement_mem_overlap (QuaternionSwapModel.leftEmbedding (.a 1))
      convert h using 1
      decide +kernel
    · exact movement_swap ▸ movement_mem_overlap QuaternionSwapModel.swap
    · exact extra_mem_overlap⟩

def element (i : Fin 128) : overlap := FiniteWords.evaluate generator (Data.overlapWords i)

def signature (x : overlap) : Nat × Nat × Nat :=
  ((x.val.val 0).val, (x.val.val 1).val, (x.val.val 2).val)
def indexSignature (i : Fin 128) : Nat × Nat × Nat := Data.overlapSignatures[i.val]!
def generatorPerm : Fin 3 → Equiv.Perm (Fin 24) :=
  ![FirstParabolic.leftIPerm, SecondCoordinates.swapPerm, SecondCoordinates.extraPerm]

theorem generator_val (j : Fin 3) : (generator j).val.val = generatorPerm j := by
  fin_cases j
  · exact FirstParabolic.leftI_val
  · rfl
  · rfl

theorem element_val (i : Fin 128) : (element i).val.val =
    FiniteWords.evaluate generatorPerm (Data.overlapWords i) := by
  have h := FiniteWords.map_evaluate (group.subtype.comp overlap.subtype)
    generator (Data.overlapWords i)
  change (element i).val.val = _ at h
  rw [show (fun j => (group.subtype.comp overlap.subtype) (generator j)) =
    generatorPerm from funext generator_val] at h
  exact h

private theorem signature_check : ∀ i : Fin 128,
    let p := FiniteWords.evaluate generatorPerm (Data.overlapWords i)
    ((p 0).val, (p 1).val, (p 2).val) = indexSignature i := by
  decide +kernel

theorem signature_element (i : Fin 128) : signature (element i) = indexSignature i := by
  unfold signature
  rw [element_val]
  exact signature_check i

theorem indexSignature_injective : Function.Injective indexSignature := by decide +kernel

theorem element_injective : Function.Injective element := by
  intro i j h
  apply indexSignature_injective
  rw [← signature_element, ← signature_element, h]

theorem element_surjective : Function.Surjective element :=
  ((Nat.bijective_iff_injective_and_card element).mpr
    ⟨element_injective, by rw [Nat.card_fin, card_overlap innerModel]⟩).2

theorem signature_injective : Function.Injective signature := by
  intro x y h
  obtain ⟨i, rfl⟩ := element_surjective x
  obtain ⟨j, rfl⟩ := element_surjective y
  apply congrArg element
  apply indexSignature_injective
  simpa only [signature_element] using h

noncomputable def coordinates : Fin 128 ≃ overlap :=
  Equiv.ofBijective element ⟨element_injective, element_surjective⟩

theorem element_zero : element 0 = 1 := by decide +kernel

theorem element_generator : ∀ j : Fin 3,
    element ⟨j.val + 1, by omega⟩ = generator j := by decide +kernel

theorem hom_ext {G : Type*} [Group G] (f g : overlap →* G)
    (h : ∀ j, f (generator j) = g (generator j)) : f = g :=
  FiniteWords.hom_ext generator Data.overlapWords element_surjective f g h
end Overlap

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
