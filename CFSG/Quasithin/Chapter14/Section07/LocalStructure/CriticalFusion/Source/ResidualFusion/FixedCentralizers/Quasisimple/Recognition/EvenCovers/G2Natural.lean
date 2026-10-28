module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.Setup
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.EvenCovers.NaturalSection
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections

/-!
# Excluding the G₂(4) cover in the source fixed-component sieve

The original component action is a nonidentity inner involution fixing its
actual Sylow two-subgroup. The intrinsic G₂(4) cover obstruction applies
through the original injective component inclusion to the supplied
U/U₀ natural section. The original U is elementary abelian and lies in
the two-core of the embedded fixed residual. This proves the G₂(4)
contradiction with no additional model or action premises.

The sibling linear-three exclusion and the final two-cover disjunction
remain with the EvenCovers assembly owner.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.68(2), printed p.1071 (PDF p.1088); 1.1.5(3)(b), pp.501–503.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace EvenCoverSieve

theorem Case.not_g2Four {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
    {α : MulAut (Lu.subgroupOf (d.fixedCentralizer u))} (c : Case d u Lu α)
    (hm : ClassificationModels.IsG2At ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 4) : False := by
  let := c.quasisimple
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.le_centralizer).symm
  obtain ⟨k,hk,hfin,hcard,⟨e⟩⟩ := hm
  let : Field k := hk
  let : Finite k := hfin
  obtain ⟨P, _, hP⟩ := d.fixedComponentAction_exists_sylow u α c.conjugation c.sylow c.normal
  obtain ⟨q,hq,_,hB,hs⟩ := c.fixedResidual_has_naturalSection
  let := d.U_elementary
  exact Atlas.G2.CoverFixedNaturalSections.not_naturalSection hcard e c.center_eq α
    (d.fixedComponentAction_ne_one u α c.conjugation c.le_centralizer c.escapes)
    (d.fixedComponentAction_sq u α c.conjugation) c.inner P hP
    (d.fixedComponentInclusion u Lu) (d.fixedComponentInclusion_injective u Lu)
    F.U d.U₀ hB q hq hs
end EvenCoverSieve
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
