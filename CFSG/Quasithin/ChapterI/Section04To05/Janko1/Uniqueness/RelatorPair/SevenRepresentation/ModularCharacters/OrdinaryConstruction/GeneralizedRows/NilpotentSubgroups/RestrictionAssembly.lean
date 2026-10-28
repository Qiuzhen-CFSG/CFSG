module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.NilpotentSubgroups
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows

/-!+# Ordinary-row assembly with the nilpotent alternatives discharged

Apply the subgroup classification to the literal restriction criterion. This
removes its `htypes` premise using the source centralizer data, ambient order
and supplied class enumeration. Compatible power labels and cyclic restriction
realizations remain explicit inputs, to be discharged by the parent ordinary-row
construction. The elementary two-subgroup restrictions are already proved in
`TwoRestriction` and are consumed by `GeneralizedRows`.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

/-- Generalized ordinary rows from their remaining power-map and cyclic
restriction inputs. The nilpotent-subgroup classification is proved here. -/
public theorem ordinaryGeneralizedRows_of_cyclic_restrictions
    {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) (horder : Nat.card G = 175560)
    {c : OrdinaryClassData G} (p : OrdinaryPowerLabels c)
    (hcyclic : ∀ (ζ₅ ζ₁₉ : ℂ), IsPrimitiveRoot ζ₅ 5 → IsPrimitiveRoot ζ₁₉ 19 →
      ∀ (i : Fin 15) (H : Subgroup G), IsCyclic H →
        IsGeneralizedCharacter (fun x : H => p.row ζ₅ ζ₁₉ i (x : G))) :
    Nonempty (OrdinaryGeneralizedRows c) :=
  ordinaryGeneralizedRows_of_local_restrictions p
    (ordinary_nilpotent_subgroup_types h horder c) hcyclic

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
