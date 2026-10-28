module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.PowerLabels.Table
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Basic

/-!
# Compatible actual power labels for the ordinary J₁ classes

The supplied class census and group order suffice to orient the repeated-order
classes. Sylow conjugacy first determines the fifth- and nineteenth-order
power orbits. The mixed-order classes are distinguished by their fifth-order
powers, and disjoint swaps align them with the literal table. The power-action
multiplication law transports the result to the supplied representatives,
which need only be conjugate to the selected powers.

`ordinaryPowerLabels_of_source` has the original source hypotheses; the
stronger `ordinaryPowerLabels_of_order` shows precisely which inputs are used.
The final application discharges the compatible-label input of the actual
Brauer restriction consumer. Its nilpotent subgroup classification and cyclic
restriction calculation remain independent premises owned by that assembly.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary conjugacy-class calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482. No recognition, model
isomorphism, character existence, or seven-dimensional representation is assumed.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

open PowerLabelConstruction

/-- The actual class census and group order determine compatible power labels. -/
public theorem ordinaryPowerLabels_of_order {G : Type*} [Group G] [Finite G]
    (horder : Nat.card G = 175560) (c : OrdinaryClassData G) :
    Nonempty (OrdinaryPowerLabels c) := by
  obtain ⟨a, b, d, h⟩ := exists_aligned c horder
  refine ⟨{
    labels := labelPerm a b d
    labels_zero := labelPerm_zero a b d
    labels_orders := labelPerm_order a b d
    labels_centralizers := labelPerm_centralizer a b d
    powers := ?_ }⟩
  intro j n
  have he := congrArg (labelPerm a b d) (aligned_power (relabel c a b d) h j n)
  rw [power_relabel, Equiv.apply_symm_apply] at he
  apply c.classes.symm.injective
  simpa only [power, idx, Equiv.symm_apply_apply] using he

/-- Compatible power labels under the original arbitrary-source-group hypotheses. -/
public theorem ordinaryPowerLabels_of_source {G : Type*}
    [Group G] [Finite G] [IsSimpleGroup G]
    (_h : CFSG.Quasithin.Janko1CentralizerData G)
    (horder : Nat.card G = 175560)
    (_hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = _h.z)
    (c : OrdinaryClassData G) : Nonempty (OrdinaryPowerLabels c) :=
  ordinaryPowerLabels_of_order horder c

/-- Application to the literal generalized-row consumer, discharging its
power-label premise. The independent subgroup and restriction calculations
remain explicit, with their final discharge in `GeneralizedRows`. -/
public theorem ordinaryGeneralizedRows_of_order_and_restrictions
    {G : Type*} [Group G] [Finite G]
    (horder : Nat.card G = 175560) (c : OrdinaryClassData G)
    (htypes : ∀ H : Subgroup G, Group.IsNilpotent H →
      IsCyclic H ∨ ((∀ x : H, x ^ 2 = 1) ∧ Nat.card H ∣ 8))
    (hcyclic : ∀ (p : OrdinaryPowerLabels c) (ζ₅ ζ₁₉ : ℂ),
      IsPrimitiveRoot ζ₅ 5 → IsPrimitiveRoot ζ₁₉ 19 →
      ∀ (i : Fin 15) (H : Subgroup G), IsCyclic H →
        IsGeneralizedCharacter (fun x : H => p.row ζ₅ ζ₁₉ i (x : G))) :
    Nonempty (OrdinaryGeneralizedRows c) := by
  obtain ⟨p⟩ := ordinaryPowerLabels_of_order horder c
  exact ordinaryGeneralizedRows_of_local_restrictions p htypes (hcyclic p)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
