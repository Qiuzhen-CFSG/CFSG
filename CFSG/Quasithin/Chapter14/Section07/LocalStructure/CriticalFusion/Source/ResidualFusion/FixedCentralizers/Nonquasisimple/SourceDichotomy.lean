module

public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction

/-!
# Discharging 1.2.11 in the original fixed-centralizer argument

The source involution dichotomy now supplies the universal Earlier1211
contract. The original point-commutator identity supplies its remaining
local membership hypothesis. Consequently the actual centralizer Gᵤ has
characteristic two, its C-component has F*=O₂, and the full C.2.7 consumer
retains only the genuine earlier C.2.7 classification input.

Source: Aschbacher–Smith 14.7.68(2), printed pp.1071–1072.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Nonquasisimple
/-- The universal earlier input is proved on its literal original groups. -/
theorem earlier1211_source : Earlier1211 G :=
  fun hG S H B z hH hs hB hz hzB hzTH hzc hcomm hCT =>
    Chapter1.lemma_1_2_11_involution hG S H B z hH hs hB hz hzB hzTH hzc hcomm hCT
end Nonquasisimple

namespace Data
variable (d : Data T L V F W)

/-- The actual Gᵤ has characteristic two without an earlier dichotomy premise. -/
theorem fixedCentralizer_characteristicTwo_of_source_dichotomy
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    d.fixedCentralizer u ∈ Chapter1.He G :=
  d.fixedCentralizer_characteristicTwo Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K

/-- The original component has F*=O₂, with 1.2.11 completely discharged. -/
theorem fixedComponent_fitting_of_source_dichotomy
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Theory.GroupTheory.generalizedFitting Lu = pCore 2 Lu :=
  d.fixedComponent_fitting_of_source Nonquasisimple.earlier1211_source u h

/-- Apply full C.2.7 to the original centralizer and component. Only the
independent earlier C.2.7 producer remains explicit. -/
theorem fixedComponent_C27_of_source_dichotomy
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Source
      KnownSimple.IsKnownSimple G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G) :=
  d.fixedComponent_C27_of_source Nonquasisimple.earlier1211_source c27 u h

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
