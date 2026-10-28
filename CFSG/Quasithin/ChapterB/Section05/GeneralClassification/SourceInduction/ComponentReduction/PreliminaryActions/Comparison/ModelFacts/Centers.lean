module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison

/-!
# The component is disjoint from its ambient centralizer

Each surviving B.5.1 row identifies the component with a centerless group:
SL₂ in characteristic two, SL₃ of odd binary degree, or A₅. For SL₃ the
scalar-center formula and the parity of the field degree give the result.
Faithful restriction then transports centerlessness from L⁺ back to L.
Thus the disjointness used in the later centralizer projection argument is
a proved consequence of the complete source cases, rather than an extra
assumption on the ambient group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
B.5.9, printed pp.107–108, the projections on L and C_G(L).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : center Y = ⊥) : center X = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have hy : e x ∈ center Y := ((centerCongr e) ⟨x, hx⟩).property
  rw [hY, mem_bot] at hy
  exact mem_bot.mpr (e.injective (by simpa using hy))

private theorem linearThree_center_eq_bot (F : BinaryField) (ho : Odd F.degree) :
    center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ := by
  apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
  rw [F.card_eq, Nat.BinaryTorusParity.two_pow_mod_three, Nat.odd_iff.mp ho]
  decide

/-- Every surviving irreducible source row has a centerless component. -/
theorem rankOneIrreducible_center_eq_bot {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {σ : Representation (ZMod 2) D V} {L H : Subgroup D}
    (c : RankOneIrreducibleCase σ L H) : center L = ⊥ := by
  cases c with
  | linearTwo F _ e _ _ =>
      exact center_eq_bot_of_equiv e.groupEquiv Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot
  | linearThree F ho _ e _ =>
      exact center_eq_bot_of_equiv e.groupEquiv (linearThree_center_eq_bot F ho)
  | symmetricFive e _ _ =>
      exact center_eq_bot_of_equiv e.subgroupEquiv (alternatingGroup.center_eq_bot (by simp))

/-- The same conclusion includes the doubled natural branch. -/
theorem rankOneAction_center_eq_bot {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {σ : Representation (ZMod 2) D V} {L : Subgroup D} {s : MovedSection σ L}
    (c : RankOneActionCase σ L s) : center L = ⊥ := by
  cases c with
  | irreducible _ _ _ c _ => exact rankOneIrreducible_center_eq_bot c
  | doubleThree F ho _ e _ _ =>
      exact center_eq_bot_of_equiv e.groupEquiv (linearThree_center_eq_bot F ho)

/-- Disjointness for the original component in G, applied to the literal
faithful seed quotient and the complete earlier source conclusion. -/
theorem seed_disjoint_of_source {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)) :
    Disjoint L (centralizer (L : Set G)) := by
  have hz := center_eq_bot_of_equiv (seedComponentEquiv ρ hLA p)
    (rankOneAction_center_eq_bot (seed_rankOneAction_of_source ρ hLA p hr c))
  apply disjoint_def.mpr
  intro x hx hc
  have hxc : (⟨x, hx⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp hc l l.property
  rw [hz, mem_bot] at hxc
  exact congrArg Subtype.val hxc

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
