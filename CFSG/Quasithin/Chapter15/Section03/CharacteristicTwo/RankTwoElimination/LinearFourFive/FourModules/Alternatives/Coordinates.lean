module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization.ModelCases

/-!
# Transporting the surviving module coordinates

The universal FF table uses additive representations of the subgroup
chosen as component. Here that subgroup is the whole literal `L/O₂(L)`.
Transporting along the top-subgroup equivalence and the additive type tag
gives the original multiplicative `U_L`, with its ambient conjugation
formula. The natural-plus-dual calculation retains the inverse in the
contragredient action. Each output keeps its own classification marking;
there is no comparison with an independently selected parabolic marking.

These constructions consume classification outputs. They do not prove
that the FF hypotheses or either alternative holds in the local setting.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1)
and 15.3.24, printed pp.99 and 1129.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives

open RankOneConfiguration.EightGeometry.NaturalModule.Recognition
open Chapter2.ComponentRefinement.LieType.Binary

/-- The two existing binary projective models use the same matrix action. -/
theorem projective_action_eq (g : Projective 4) :
    pslEquivLinear 4 g = projectiveEquivLinear (by decide : 0 < 4) g := by
  rfl

variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
  [IsElementaryAbelian 2 (spanCommutator d L)]
  (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))

/-- Recover repeated-natural coordinates on the actual multiplicative commutator. -/
noncomputable def repeatedCoordinates {r : ℕ}
    (h : FFSpecialization.RepeatedNatural (coreRepresentation d L hcore hR) ⊤ r) :
    RepeatedNatural d L r where
  model := (Subgroup.topEquiv : (⊤ : Subgroup (L ⧸ pCore 2 L)) ≃* _).symm.trans h.model
  coordinates := h.coordinates.toAddEquiv.toMultiplicativeRight
  equivariant l u i := by
    have he := h.equivariant ⟨QuotientGroup.mk' _ l, mem_top _⟩ (Additive.ofMul u) i
    rw [coreRepresentation_mk] at he
    change h.coordinates (Additive.ofMul (commutatorAction d L l u)) i =
      pslEquivLinear 4 (h.model ⟨QuotientGroup.mk' _ l, mem_top _⟩)
        (h.coordinates (Additive.ofMul u) i) at he
    exact he

/-- Recover natural-plus-dual coordinates with the classifier’s own model marking. -/
noncomputable def naturalDualCoordinates
    {model : (⊤ : Subgroup (L ⧸ pCore 2 L)) ≃* Projective 4}
    (h : Models.NaturalDual (coreRepresentation d L hcore hR) ⊤ model) :
    NaturalDual d L where
  model := (Subgroup.topEquiv : (⊤ : Subgroup (L ⧸ pCore 2 L)) ≃* _).symm.trans model
  coordinates := h.coordinates.toAddEquiv.toMultiplicativeRight
  equivariant l u := by
    have he := h.equivariant ⟨QuotientGroup.mk' _ l, mem_top _⟩ (Additive.ofMul u)
    rw [coreRepresentation_mk] at he
    refine he.trans ?_
    apply Prod.ext
    · rw [BinaryLinear.NaturalDualFlag.action_fst]
      rfl
    · apply LinearMap.ext
      intro v
      change (h.coordinates (Additive.ofMul u)).2
          (pslEquivLinear 4 ((model ⟨QuotientGroup.mk' _ l, mem_top _⟩)⁻¹) v) = _
      rw [map_inv, BinaryLinear.NaturalDualFlag.action_snd]
      rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives
end
