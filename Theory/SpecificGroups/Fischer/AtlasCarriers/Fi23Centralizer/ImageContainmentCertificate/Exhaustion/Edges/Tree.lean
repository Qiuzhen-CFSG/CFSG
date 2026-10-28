module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Exhaustion.Edges.SourceRelations

/-!
# Tree cancellation and short cycles for the Fi23 exhaustion

A literal prefix equality makes its Schreier edge trivial. The checked
A² and B³ relations also express an omitted edge as the inverse product of
its other cycle edges. Thus at most one A edge or two B edges per nontrivial
cycle require independent membership certificates. Fixed-point loops remain.
The original representatives and all eight witness generators are unchanged.

Source: ATLAS F23G1-p31671B0, GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
open Fi24Prime.Fi23Lift.Certificate

def representativeLetters (x : Fin 31671) : List Bool := (wordCode x).bits.dropLast

theorem representative_eq_letters (x : Fin 31671) :
    representative x = ((representativeLetters x).map letter).prod := rfl

/-- The next representative is obtained by prepending this actual generator. -/
def TreeEdge (b : Bool) (x : Fin 31671) : Prop :=
  representativeLetters (packedLetter b x) = b :: representativeLetters x

instance (b : Bool) (x : Fin 31671) : Decidable (TreeEdge b x) :=
  inferInstanceAs (Decidable (_ = _))

theorem representative_prefix (b : Bool) (x y : Fin 31671)
    (h : representativeLetters y = b :: representativeLetters x) :
    representative y = letter b * representative x := by
  rw [representative_eq_letters y]
  rw [h, List.map_cons, List.prod_cons]
  rfl

private theorem telescope_two {G : Type*} [Group G] (s r₀ r₁ : G)
    (hs : s * s = 1) :
    (r₀⁻¹ * s * r₁) * (r₁⁻¹ * s * r₀) = 1 := by
  calc
    _ = r₀⁻¹ * (s * s) * r₀ := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = 1 := by rw [hs]; simp

private theorem telescope_three {G : Type*} [Group G] (s r₀ r₁ r₂ : G)
    (hs : s * s * s = 1) :
    (r₀⁻¹ * s * r₂) * (r₂⁻¹ * s * r₁) * (r₁⁻¹ * s * r₀) = 1 := by
  calc
    _ = r₀⁻¹ * (s * s * s) * r₀ := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = 1 := by rw [hs]; simp

variable (hA : ∀ x, generatorA x = sourceA x) (hB : ∀ x, generatorB x = sourceB x)

include hA in
theorem letter_false_square : letter false * letter false = 1 := by
  apply inclusion_injective
  simp only [map_mul, map_one, inclusion_letter_false]
  apply Equiv.ext
  intro x
  change generatorA (generatorA x) = x
  rw [hA, hA, sourceA_square]

include hB in
theorem letter_true_cube : letter true * letter true * letter true = 1 := by
  apply inclusion_injective
  simp only [map_mul, map_one, inclusion_letter_true]
  apply Equiv.ext
  intro x
  change generatorB (generatorB (generatorB x)) = x
  rw [hB, hB, hB, sourceB_cube]

include hA hB in
theorem edge_eq_one_of_tree (b : Bool) (x : Fin 31671) (h : TreeEdge b x) :
    edge b x = 1 := by
  have hp := representative_prefix b x (packedLetter b x) h
  rw [edge, ← packedLetter_eq hA hB, hp]
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, one_mul]

include hA hB in
theorem edge_mem_of_tree (b : Bool) (x : Fin 31671) (h : TreeEdge b x) :
    inclusion (edge b x) ∈ witnessGroup := by
  rw [edge_eq_one_of_tree hA hB b x h, map_one]
  exact witnessGroup.one_mem

-- The two A edges multiply to the identity in the actual carrier.
include hA in
theorem edge_false_pair (x : Fin 31671) :
    edge false (sourceA x) * edge false x = 1 := by
  simp only [edge, inclusion_letter_false, hA, sourceA_square]
  exact telescope_two (letter false) (representative x) (representative (sourceA x))
    (letter_false_square hA)

-- The three B edges multiply to the identity, in reverse path order.
include hB in
theorem edge_true_triple (x : Fin 31671) :
    edge true (sourceB (sourceB x)) * edge true (sourceB x) * edge true x = 1 := by
  simp only [edge, inclusion_letter_true, hB, sourceB_cube]
  exact telescope_three (letter true) (representative x) (representative (sourceB x))
    (representative (sourceB (sourceB x))) (letter_true_cube hB)

include hA in
theorem edge_false_mem_of_next (x : Fin 31671)
    (h : inclusion (edge false (sourceA x)) ∈ witnessGroup) :
    inclusion (edge false x) ∈ witnessGroup := by
  have he := congrArg inclusion (edge_false_pair hA x)
  simp only [map_mul, map_one] at he
  rw [mul_eq_one_iff_eq_inv'.mp he]
  exact witnessGroup.inv_mem h

include hB in
theorem edge_true_mem_of_next (x : Fin 31671)
    (h₁ : inclusion (edge true (sourceB x)) ∈ witnessGroup)
    (h₂ : inclusion (edge true (sourceB (sourceB x))) ∈ witnessGroup) :
    inclusion (edge true x) ∈ witnessGroup := by
  have he := congrArg inclusion (edge_true_triple hB x)
  simp only [map_mul, map_one] at he
  rw [mul_eq_one_iff_eq_inv'.mp he]
  exact witnessGroup.inv_mem (witnessGroup.mul_mem h₂ h₁)

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate.Exhaustion.Edges
