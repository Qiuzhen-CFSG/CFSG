module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer.Native
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FirstStabilizer

/-!
# The two complete source involution stabilizer structures

The actual core action has two singular orbits. The first stabilizer is the
recognized full-design pair stabilizer. A checked five-involution action in
the second native stabilizer gives its elementary order-sixteen two-core and
symmetric-five quotient. Transport along the original full cubic action
identifies both literal images of C_H(r) under H → H/Q.

This proves all the orbit and group-shape assertions of Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), (4.2), p.597,
DOI 10.1007/BF01232280. No splitting of these extensions is asserted.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Both distinct source classes, with elementary two-cores and actual S₅
quotients for their literal centralizer images. -/
theorem source_involution_stabilizer_structures (h : IsTypeJ4 z) :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
      ¬ IsConj (r₁ : centralizer z) (r₂ : centralizer z) ∧
      (let C := (Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))
       Nat.card C = 3840 ∧ IsElementaryAbelian 2 (pCore 2 C) ∧
         Nat.card (pCore 2 C) = 32 ∧
         Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5))) ∧
      (let C := (Subgroup.centralizer ({(r₂ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))
       Nat.card C = 1920 ∧ IsElementaryAbelian 2 (pCore 2 C) ∧
         Nat.card (pCore 2 C) = 16 ∧
         Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5))) ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  have hl₁ : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₁))) = 4 := by
    rw [e₁,VectorOrbits.label_decode]
    rfl
  have hl₂ : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₂))) = 7 := by
    rw [e₂,VectorOrbits.label_decode]
    rfl
  refine ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,?_,?_,?_,hcov⟩
  · intro hc
    have he := core_label_of_isConj h e X r₁ r₂ hc
    rw [hl₁,hl₂] at he
    exact (by decide : (4 : VectorOrbits.Word) ≠ 7) he
  · dsimp only
    rw [← coreVectorStabilizer_eq_centralizer_image h r₁ h₁c]
    exact ⟨coreVectorStabilizer_card_four h e X r₁ hl₁,
      coreVectorStabilizer_structure_four h e X r₁ h₁c hl₁⟩
  · dsimp only
    rw [← coreVectorStabilizer_eq_centralizer_image h r₂ h₂c]
    exact ⟨coreVectorStabilizer_card_seven h e X r₂ hl₂,
      coreVectorStabilizer_structure_seven h e X r₂ hl₂⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
