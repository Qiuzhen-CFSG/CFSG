module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Selection

/-!
# Residual selection for the two product branches of 13.6.13

The actual minimal solvable X is normal, nontrivial and two-perfect in the
offender actor on U_v. The native B.5.6(3) factor list therefore identifies
X with the residual of the first S₃ factor, the second S₃ factor, or their
whole product. In B.5.6(5), only the second factor can occur.

These theorems discharge the group-selection step on the original star
quotient and Sylow marking. Ambient normality of the selected overgroup,
its literal Thompson equality, and the actual moved-support decomposition
remain to be constructed before either product branch yields
`NormalS3Decomposition`. Neither irreducibility nor the solvable exclusion
is used in the selection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

/-- The chosen X from 13.6.13 is one of the three literal residuals of
B.5.6(3), in the actual offender actor on U_v. This is a factor-selection
result, not yet the normal S₃ decomposition. -/
theorem minimalSolvable_twoFactor_choice (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    ResidualChoice (D := FFFactors.offenderActor (starRepresentation z v)) c.first c.second
      (X.subgroupOf (FFFactors.offenderActor (starRepresentation z v))) := by
  obtain ⟨hn, hne, hp, hs, _⟩ := minimalSolvable_in_offender L T z v hz S hS hX
  let I := FFFactors.offenderActor (starRepresentation z v)
  let : (X.subgroupOf I).Normal := hn
  exact twoFactor_solvable_choice (D := I)
    (FFFactors.offenderRepresentation (starRepresentation z v)) c (X.subgroupOf I) hs hp hne

/-- The hyperplane branch selects its second factor on the original star
quotient, without a solvable-exclusion premise. -/
theorem minimalSolvable_hyperplane_choice (L T : Subgroup G) (z v : G)
    (hz : z ∈ Gv v) [IsElementaryAbelian 2 (Uv z v)]
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v))) :
    Nonempty (c.second ≃* Equiv.Perm (Fin 3)) ∧
      X.subgroupOf (FFFactors.offenderActor (starRepresentation z v)) =
        @Subgroup.map c.second _ (FFFactors.offenderActor (starRepresentation z v)) _
          c.second.subtype (pResidual 2 c.second) := by
  obtain ⟨hn, hne, hp, hs, _⟩ := minimalSolvable_in_offender L T z v hz S hS hX
  let I := FFFactors.offenderActor (starRepresentation z v)
  let : (X.subgroupOf I).Normal := hn
  exact hyperplane_solvable_choice (D := I)
    (FFFactors.offenderRepresentation (starRepresentation z v)) c (X.subgroupOf I) hs hp hne

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
