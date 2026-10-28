module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.SourceSeed

/-!
# Source singleton Thompson equalities for 13.6.13

The original Sylow-central seed identifies each normal factor's moved space
with its cubic residual plane. Applying the existing maximum-elementary
construction now proves the literal Thompson equality for every selected
singleton, including mixed and hyperplane alternatives, without any support
cardinality or fixed-kernel premise.

Source: Aschbacher--Smith, combined manuscript, 13.6.13, printed p.929.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

theorem source_twoFactor_first_thompson
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.first).map c.first.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  exact minimalSolvable_twoFactor_first_thompson f S hS hfix hL hX c e hF
    (Supports.minimalSolvable_twoFactor_first_moved_card L (T : Subgroup G) _ _
      (A5Module.markedZ_mem_Gv f.module) S hS hfix hX c e hF)

theorem source_twoFactor_second_thompson
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.second).map c.second.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  exact minimalSolvable_twoFactor_second_thompson f S hS hfix hL hX c e hF
    (Supports.minimalSolvable_twoFactor_second_moved_card L (T : Subgroup G) _ _
      (A5Module.markedZ_mem_Gv f.module) S hS hfix hX c e hF)

theorem source_hyperplane_thompson
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ s) (A5Module.markedV s)))) :
    let z := A5Module.markedZ s
    let v := A5Module.markedV s
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  exact minimalSolvable_hyperplane_thompson s T S hS hfix hX c
    (Supports.minimalSolvable_hyperplane_moved_card L T _ _
      (A5Module.markedZ_mem_Gv s) S hS hfix hX c)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
