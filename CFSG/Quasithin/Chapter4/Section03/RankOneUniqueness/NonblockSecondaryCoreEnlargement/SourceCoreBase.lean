module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCubic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrattiniKernel
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitarySource
/-!
# Characteristic two for the original source component

The genuine two-local and subnormal-component hypotheses make its full two-core
self-centralizing, independently of strict core enlargement.
Source: Aschbacher--Smith, original 4.3.11--16, pp.617--618.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
open Nonblock.RootCoordinates
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}
theorem component_core_selfCentralizing (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let H := s.component.map (rootNormalizer c).subtype
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hlocal : IsTwoLocal (rootNormalizer c) := by
    let := c.c28.module_elementary
    exact ⟨root c, root_ne_bot c D,
      (IsElementaryAbelian.isPGroup 2 (W c)).to_le inf_le_left, rfl⟩
  have hchar : HasCharacteristicTwo (rootNormalizer c) :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hlocal (root_normalized c D))
  have hc := subnormal_core_selfCentralizing hchar s.component s.isComponent.subnormal
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective)).mp hc

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
