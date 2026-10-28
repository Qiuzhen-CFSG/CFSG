module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Restriction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Subtori
/-!
# Pulling intrinsic torus characters back to the original torus

The inclusion of a torus in a closed overgroup lifts surjectively onto its
literal inverse image in that overgroup. Character pullback is therefore
injective, and its pairing with a cocharacter agrees with composition of the
cocharacter. A nontrivial intrinsic character trivial on the original
codimension-one subtorus recovers that same ambient connected kernel.

This supplies the original-torus character and sign comparisons for the two
centralizer models in Borel, *Linear Algebraic Groups*, IV, 13.11(3)--13.12.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k]
variable {G : Variety k} [AlgebraicGroup G]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

@[expose] noncomputable def inclusionPreimageMorphism (T H : ClosedSubgroup G) (hTH : T ≤ H) :
    let Ti := H.inclusion.closedSubgroupPreimage T
    letI : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    AlgebraicGroup.Morphism T.carrierVariety Ti.carrierVariety := by
  dsimp only
  let _ : AlgebraicGroup (H.inclusion.closedSubgroupPreimage T).carrierVariety :=
    (H.inclusion.closedSubgroupPreimage T).carrierAlgebraicGroup
  let j := T.inclusion.codRestrictClosedSubgroup H
    (fun x => hTH (T.pointEquiv x).property)
  apply j.codRestrictClosedSubgroup (H.inclusion.closedSubgroupPreimage T)
  intro x
  change H.inclusion.onPoints (j.onPoints x) ∈ T
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply]
  exact (T.pointEquiv x).property

theorem inclusionPreimageMorphism_apply (T H : ClosedSubgroup G) (hTH : T ≤ H)
    (x : Variety.Point T.carrierVariety) :
    let Ti := H.inclusion.closedSubgroupPreimage T
    letI : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    H.inclusion.onPoints (Ti.includePoint ((inclusionPreimageMorphism T H hTH).onPoints x)) =
      T.includePoint x := by
  dsimp only
  let _ : AlgebraicGroup (H.inclusion.closedSubgroupPreimage T).carrierVariety :=
    (H.inclusion.closedSubgroupPreimage T).carrierAlgebraicGroup
  change H.inclusion.onPoints ((H.inclusion.closedSubgroupPreimage T).inclusion.onPoints
    ((inclusionPreimageMorphism T H hTH).onPoints x)) = T.includePoint x
  dsimp only [inclusionPreimageMorphism, id]
  rw [Morphism.codRestrictClosedSubgroup_inclusion_apply,
    Morphism.codRestrictClosedSubgroup_inclusion_apply]
  rfl

theorem inclusionPreimageMorphism_surjective (T H : ClosedSubgroup G) (hTH : T ≤ H) :
    let Ti := H.inclusion.closedSubgroupPreimage T
    letI : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
    Function.Surjective (inclusionPreimageMorphism T H hTH).onPoints := by
  dsimp only
  let Ti := H.inclusion.closedSubgroupPreimage T
  let _ : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
  intro y
  let x := T.pointEquiv.symm ⟨H.includePoint (Ti.includePoint y), (Ti.pointEquiv y).property⟩
  refine ⟨x, Ti.inclusion_injective (H.inclusion_injective ?_)⟩
  exact inclusionPreimageMorphism_apply T H hTH x

theorem character_pullback_injective_of_surjective
    {A B : Variety k} [AlgebraicGroup A] [AlgebraicGroup B]
    (f : AlgebraicGroup.Morphism A B) (hf : Function.Surjective f.onPoints) :
    Function.Injective (TorusCharacter.pullback f) := by
  intro χ ψ he
  apply AlgebraicGroup.Morphism.ext
  funext y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun γ : TorusCharacter A => γ.onPoints x) he

variable [IsAlgClosed k]

theorem characterCocharacterPairing_pullback
    {A : Variety k} [AlgebraicGroup A]
    (T : ClosedSubgroup G) (U : ClosedSubgroup A)
    (f : AlgebraicGroup.Morphism T.carrierVariety U.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T) (χ : TorusWeight U) :
    characterCocharacterPairing T c (Additive.ofMul (TorusCharacter.pullback f χ)) =
      characterCocharacterPairing U (f.comp c) (Additive.ofMul χ) := by
  apply (weightCocharacterEquation_existsUnique T (TorusCharacter.pullback f χ) c).unique
    (characterCocharacterPairing_spec T _ c)
  exact characterCocharacterPairing_spec U χ (f.comp c)

/-- Pulling the intrinsic character back along the original torus inclusion
retains its literal codimension-one ambient kernel. -/
theorem pulled_character_ambientConnectedKernel
    (T S H : ClosedSubgroup G) (hTH : T ≤ H) (hT : IsSubtorus T)
    (hS : IsSubtorus S) (hST : S ≤ T)
    (hcodim : Variety.dimension S.carrierVariety + 1 = Variety.dimension T.carrierVariety)
    : let Ti := H.inclusion.closedSubgroupPreimage T
      letI : AlgebraicGroup Ti.carrierVariety := Ti.carrierAlgebraicGroup
      ∀ (χ : TorusWeight Ti), χ ≠ 1 →
        (∀ x : Variety.Point Ti.carrierVariety,
          H.inclusion.onPoints (Ti.includePoint x) ∈ S → χ.onPoints x = 1) →
        (TorusCharacter.pullback (inclusionPreimageMorphism T H hTH) χ).ambientConnectedKernel T = S := by
  dsimp only
  let _ : AlgebraicGroup (H.inclusion.closedSubgroupPreimage T).carrierVariety :=
    (H.inclusion.closedSubgroupPreimage T).carrierAlgebraicGroup
  intro χ hχ hkill
  apply ambientConnectedKernel_eq_of_codimension_one T S hT hS hST hcodim
  · intro he
    apply hχ
    apply character_pullback_injective_of_surjective _ (inclusionPreimageMorphism_surjective T H hTH)
    simpa only [map_one] using he
  · intro x hx
    apply hkill
    change H.inclusion.onPoints ((H.inclusion.closedSubgroupPreimage T).includePoint
      ((inclusionPreimageMorphism T H hTH).onPoints x)) ∈ S
    rw [inclusionPreimageMorphism_apply]
    exact hx
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
