module

public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The intrinsic two-subgroup bound for characteristic-two PSL₂

Transport an embedded two-group through the canonical SL₂–PSL₂ equivalence,
place its image in a Sylow two-subgroup, and use the actual equivalence of
that Sylow subgroup with the additive field. This includes GF(2), needed
for the outer-involution fixed group when the original field has order four.

The consumer in `ElementaryAutomorphisms.Bounds` applies this first to inner
automorphisms and then to their intersection with an outer involution's fixed
group. Source: GLS, Volume 2, Theorem 26.24, Step 5.
-/

namespace Theory.PSL2

/-- A two-group embedded in characteristic-two PSL₂ has order at most the
field cardinality. The bound uses the actual additive-field Sylow model. -/
public theorem twoGroup_card_le_field_of_injective {K E : Type*}
    [Field K] [CharP K 2] [Finite K] [_root_.Group E]
    (hE : IsPGroup 2 E) (f : E →* Group K) (hf : Function.Injective f) :
    Nat.card E ≤ Nat.card K := by
  let φ := (sl2QuotientEquiv K).symm.toMonoidHom.comp f
  have hφ : Function.Injective φ := (sl2QuotientEquiv K).symm.injective.comp hf
  obtain ⟨P, hP⟩ := (hE.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).exists_le_sylow
  calc
    Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    _ ≤ Nat.card P := Subgroup.card_le_of_le hP
    _ = Nat.card K := by
      exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 P).toEquiv).symm

end Theory.PSL2
