module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Transport
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# A component with positive three-rank

A prime dividing the order of the layer divides the order of some component:
distinct components commute, and a finite join of mutually normalizing
prime-to-p subgroups is again prime to p. The actual PSL₃(2) residual has
order 168, so its inclusion in E(C_G(f)) supplies a positive-three-rank
component. This does not yet exclude rank one or prove uniqueness.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed p.1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion

private theorem exists_component_of_dvd_layer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card (componentLayer G)) :
    ∃ K : Subgroup G, IsComponent G K ∧ 0 < primeRank p K := by
  classical
  by_contra! hn
  have hfree (K : Subgroup G) (hK : IsComponent G K) : ¬ p ∣ Nat.card K :=
    PrimeRank.eq_zero_iff_not_dvd_card.mp (Nat.eq_zero_of_le_zero (hn K hK))
  let C := {K : Subgroup G // IsComponent G K}
  have hcn (i j : C) : i.val ≤ normalizer (j.val : Set G) := by
    by_cases he : i.val = j.val
    · rw [he]
      exact j.val.le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (i.property.commutator_eq_bot_of_ne j.property he)).trans (centralizer_le_normalizer _)
  have h := not_dvd_card_iSup_of_normalizes (Fact.out : p.Prime)
    (fun i : C => i.val) hcn (fun i => hfree i.val i.property)
  have hE : componentLayer G = ⨆ i : C, i.val := by
    apply le_antisymm
    · exact sSup_le fun J hJ => le_iSup (fun i : C => i.val) ⟨J, hJ⟩
    · exact iSup_le fun i => le_sSup i.property
  exact h (hE ▸ hp)

/-- The residual model has its literal order, in its actual centralizer embedding. -/
theorem fieldResidual_card {G : Type*} [Group G] (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nat.card (fieldResidual L f) = 168 :=
  (Nat.card_congr (fieldResidualEquivModel L f e).toEquiv).trans Matrix.PSL3Two.card_PSL

/-- The established layer inclusion forces a component with positive three-rank. -/
theorem exists_positive_component_of_fieldResidual {G : Type*} [Group G] [Finite G] (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hF : fieldResidual L f ≤ componentLayer (centralizer ({f} : Set G))) :
    ∃ K : Subgroup (centralizer ({f} : Set G)),
      IsComponent (centralizer ({f} : Set G)) K ∧ 0 < primeRank 3 K := by
  have hcard := fieldResidual_card L f e
  apply exists_component_of_dvd_layer
  exact (show 3 ∣ Nat.card (fieldResidual L f) by rw [hcard]; decide).trans
    (card_dvd_of_le hF)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
