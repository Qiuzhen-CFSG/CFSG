module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels.FullCenter
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Quotient

/-!
# Retaining the original component star quotient

The classified actions may initially be presented on L*, the actual image
of L under the source star map. The relative-normality and Sylow hypotheses
identify L/O₂(L) with that image using SmallExtension.Quotient. These
constructors transport full-center or full-core coordinates along that
specific equivalence, preserving conjugation on every lift.

Source: Aschbacher--Smith, proof of 15.3.31, printed p.1132.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration
open SmallExtension CentralCover LinearModels
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels

variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
variable (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (S : Sylow 2 I)
    (hS : (S : Subgroup I).map I.subtype = d.S)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    {ρ : Representation (ZMod 2) A V}

/-- Transport the actual star action using the proved relative quotient comparison. -/
noncomputable def fullCenterOfStar
    (q : d.starImage I c.L ≃* A)
    (e : coreCenter c.L ≃* Multiplicative V)
    (ha : ∀ (l : c.L) (z : coreCenter c.L),
      e (centerConjugate c.L l z) =
        Multiplicative.ofAdd (ρ (q (componentMap d c l)) (e z).toAdd)) :
    FullCenter c.L ρ where
  quotientIso := (coreQuotientEquivStar d c hn S hS).trans q
  equiv := e
  action l z := ha l z

/-- The same comparison for cases (1) and (2), whose full core is abelian. -/
noncomputable def abelianCoreOfStar
    (q : d.starImage I c.L ≃* A)
    (e : extensionCore c.L ≃* Multiplicative V)
    (ha : ∀ (l : c.L) (x y : extensionCore c.L),
      (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
      e y = Multiplicative.ofAdd (ρ (q (componentMap d c l)) (e x).toAdd)) :
    AbelianCore c.L ρ where
  quotientIso := (coreQuotientEquivStar d c hn S hS).trans q
  equiv := e
  action l x y h := ha l x y h

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
