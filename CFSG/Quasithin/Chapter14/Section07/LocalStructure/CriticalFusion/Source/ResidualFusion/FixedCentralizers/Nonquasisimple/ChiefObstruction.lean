module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.AlternatingBound.A5Degree

/-!
# Original-module input to the nonquasisimple centralizer branch

The original natural action proves z ∈ [U,K]. This discharges the extra
point-commutator premise in the characteristic-two/Fitting argument and
in the application of the full C.2.7 implication, on the literal Gᵤ, Lᵤ,
Rᵤ and H ∩ Gᵤ. Universal 1.2.11 and C.2.7 remain explicit earlier inputs,
owned by qt-1-02-component-dichotomy/qt-1-02-adequate-assembly and qt-c-02.

The minimum order of each noncentral binary K-section is now proved from
the original A₅ marking and two-perfectness. The A₇ block exclusion still
requires the two actual noncentral K-chief factors from the 14.5.21 duality
and the intersection filtration supplying the injective pair maps.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed pp.1071–1072.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The Fitting conclusion now needs only the earlier universal 1.2.11,
whose producer is qt-1-02-component-dichotomy/qt-1-02-adequate-assembly. -/
theorem fixedComponent_fitting_of_source
    (earlier : Nonquasisimple.Earlier1211 G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Theory.GroupTheory.generalizedFitting Lu = pCore 2 Lu :=
  d.fixedComponent_fitting earlier u h d.point_mem_U_commutator_K

/-- Full C.2.7 on the original groups, with the original-module premise
proved. The universal 1.2.11 and C.2.7 remain the source owners' inputs. -/
theorem fixedComponent_C27_of_source
    (earlier : Nonquasisimple.Earlier1211 G)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Source
      KnownSimple.IsKnownSimple G)
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G) :=
  d.fixedComponent_C27 earlier c27 u h d.point_mem_U_commutator_K

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
