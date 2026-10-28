module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.LinearThree
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.G2Natural
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.NaturalSection

/-!
# Exceptional central two-covers in the fixed-component sieve

The PSL₃(4) branch is excluded from its actual involution centralizers.
Both exceptional two-cover alternatives are excluded: the PSL₃(4) branch
by its actual involution centralizer and the G₂(4) branch by the supplied
natural SL₂(4) section.
The source action is proved to be a nonidentity involution fixing the
literal component Sylow, with the original ambient inclusion retained.
The original U/U₀ natural section is also constructed on the image of
the fixed residual, using its unchanged map to SL₂(4).

The sporadic alternatives and Rudvalis recognition remain separate branches.
Source: Aschbacher–Smith, 14.7.68(2), printed p.1071 (PDF p.1088),
and 1.1.5(3)(b), printed pp.501–503, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace EvenCoverSieve

/-- The actual PSL₃(4) exclusion leaves only the exceptional G₂(4) quotient. -/
theorem Case.isG2_of_twoCover {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} (c : Case d u Lu α)
    (hm : ClassicalGroup.IsPSL ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
        pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 3 4 ∨
      ClassificationModels.IsG2At ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
        pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 4) :
    ClassificationModels.IsG2At ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 4 :=
  hm.resolve_left c.not_pslThreeFour

/-- The two-cover alternative of 1.1.5(3)(b) is impossible in the source
configuration.  Both conclusions use the literal component action and its
original natural section. -/
theorem Case.not_twoCover {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} (c : Case d u Lu α) :
    ¬ (ClassicalGroup.IsPSL ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 3 4 ∨
      ClassificationModels.IsG2At ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
        pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 4) := by
  rintro (hpsl | hg2)
  · exact c.not_pslThreeFour hpsl
  · exact c.not_g2Four hg2

end EvenCoverSieve
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
