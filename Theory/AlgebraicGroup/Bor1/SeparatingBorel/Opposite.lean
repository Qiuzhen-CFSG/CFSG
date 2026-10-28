module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.RegularChoice

/-!
# Reversing a cocharacter

Composing with inversion on the multiplicative group reverses every integral
character pairing and preserves the literal one-parameter image. Thus the same
semiregular parameter supplies both maximal and minimal weight comparisons.

Source: Borel, *Linear Algebraic Groups*, IV, 13.3 and 13.11(3).
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
@[expose] noncomputable def oppositeCocharacter (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) : ClosedSubgroupTorusCocharacter T :=
  c.comp ((AlgebraicGroup.Morphism.id (KMult k) : TorusCharacter (KMult k))⁻¹)

omit [IsAlgClosed k] in
theorem oppositeCocharacter_apply (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (t : Variety.Point (KMult k)) :
    (oppositeCocharacter T c).onPoints t = c.onPoints t⁻¹ := rfl

theorem oppositeCocharacter_image (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) :
    (T.inclusion.comp (oppositeCocharacter T c)).imageClosedSubgroup =
      (T.inclusion.comp c).imageClosedSubgroup := by
  apply SetLike.coe_injective
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t⁻¹, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t⁻¹, ?_⟩
    change T.includePoint (c.onPoints (t⁻¹)⁻¹) = T.includePoint (c.onPoints t)
    rw [inv_inv]

theorem characterCocharacterPairing_opposite (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (χ : TorusWeight T) :
    characterCocharacterPairing T (oppositeCocharacter T c) (Additive.ofMul χ) =
      -characterCocharacterPairing T c (Additive.ofMul χ) := by
  have he : TorusCharacter.pullback (oppositeCocharacter T c) χ =
      (TorusCharacter.pullback c χ)⁻¹ := by
    apply AlgebraicGroup.Morphism.ext
    funext t
    change χ.onPoints (c.onPoints t⁻¹) = (χ.onPoints (c.onPoints t))⁻¹
    rw [map_inv, map_inv]
  apply (weightCocharacterEquation_existsUnique T χ (oppositeCocharacter T c)).unique
    (characterCocharacterPairing_spec T χ (oppositeCocharacter T c))
  intro t
  have he' : TorusCharacter.pullback (oppositeCocharacter T c) χ =
      TorusCharacter.pullback c χ⁻¹ := he.trans (map_inv (TorusCharacter.pullback c) χ).symm
  have hv := congrArg (fun ψ : TorusCharacter (KMult k) => ψ.pointCharacter t) he'
  have hs := characterCocharacterPairing_spec T χ⁻¹ c t
  change χ.pointCharacter ((oppositeCocharacter T c).onPoints t) =
    (χ⁻¹).pointCharacter (c.onPoints t) at hv
  rw [hv]
  change (χ⁻¹).pointCharacter (c.onPoints t) =
    (dPointEquiv 1 t 0 : k) ^ (-characterCocharacterPairing T c (Additive.ofMul χ))
  rw [← map_neg]
  exact hs
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
