module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.BlockSelection
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Geometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.LocalConfiguration
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.MovedAlternating

/-!
# The index-two contradiction for the literal L₃ block normalizer

The prime-to-three residual identity identifies any block in the public
contract with the block selected by E.6.7. Transfer its Thompson movement
equation, construct the local configuration in J C_T(V), and apply C.5.7.

Source: Aschbacher–Smith E.6.14, printed p.251, and 12.4.8, p.815.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
open ChapterE Section06 ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Discharge the local index contract without any block or conjugate callbacks. -/
theorem blockIndex (c : Configuration T L V U) : BlockIndex c := by
  intro hc J hJ ht hmax
  obtain ⟨J',hJ',_,hm⟩ := blockSelection_moved c hc c.stabilizer_geometry.faithful_three
  have hEq : J = J' := by
    -- The residual identity makes the selected block unique.
    have hres : J = (primeToResidual 3 (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype := hJ.residual_three
    have hres' : J' = (primeToResidual 3 (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype := hJ'.residual_three
    exact hres.trans hres'.symm
  subst J'
  have hcJ := local_configuration c hc J hJ hmax
  exact ChapterE.Section06.InvariantSubspaces.LocalIndex.index_of_moved_alternating
    hcJ hm ht

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
end
