module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.ActionFacts
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.Contracts
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.GroupQuotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.LocalMarking.SeedCoordinates

/-!
# Compatible local coordinates for the parabolic argument

The natural setup and the earlier local identities give the literal
I₂-action on V₂ with kernel O₂(I₂), a nontrivial point-core image, and
fixed-point-free L₂ actors on both V₂ and V/V₂. The latter quotient is
identified with the quotient of the given natural space by its marked
plane and has binary dimension two.

The plane action is surjective, giving I₂/O₂(I₂) ≃ S₃. Conjugating these
coordinates puts the point-core image at the specified inverter, while
the L₂ image is the characteristic cubic subgroup. The two-core acts
trivially on V/V₂, and the descended action admits natural coordinates
for this same quotient marking. Assembling the two constructions gives
`CompatibleMarking` from the natural setup and the earlier local
identities, without assuming a group or module marking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4, printed p.916, and the local action in 13.8.6, printed p.948.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking

open EarlierCore RankDoubling.SourceAction

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H L V V₁ V₂ V₃ : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- Construct compatible coordinates on the literal I₂/O₂(I₂) and V/V₂.
The quotient construction supplies both prescribed subgroup images; the seed
coordinates intertwine actual L₂ conjugation with that same quotient marking. -/
theorem nonempty_compatibleMarking
    (s : NaturalSetup T L V V₁ V₂ V₃)
    (d : LocalData H V V₁ V₂ V₃ (localI L V₁ V₂) (localResidual L V₂)) :
    Nonempty (CompatibleMarking H V V₁ V₂ V₃
      (localI L V₁ V₂) (localResidual L V₂) d) := by
  obtain ⟨q⟩ := GroupQuotient.quotientMarking_nonempty s d
  exact SeedCoordinates.nonempty_compatibleMarking s q d

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.LocalMarking
