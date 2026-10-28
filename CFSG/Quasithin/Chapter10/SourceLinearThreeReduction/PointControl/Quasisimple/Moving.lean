module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.DoubledExclusion

/-!
# Quasisimple point exclusion from the moving local Thompson action

The original minimal-module classification supplies literal rank-one or
binary-three natural coordinates whenever the local Thompson subgroup moves
the chosen module. The completed containing-carrier comparisons exclude both
possibilities. The source multiple-overgroup argument also reduces every
nonzero full orbit-fixed layer to this moving branch.

These applications preserve the original setup, fixed kernel and point.
The local Thompson-centralizing branch remains with the point-control owner;
no irreducibility of an arbitrary component restriction is asserted.
Source: Aschbacher--Smith 10.1.1--2 and 10.2.9, pp.741--742,750--751.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

theorem quasisimple_impossible_of_rankOneNatural
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : Selection.RankOneNatural D) : False := by
  obtain ⟨n,hn,hm⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  obtain ⟨e,_⟩ := hm
  apply quasisimple_impossible_of_binary_quotient D c hn _ hna
  refine ⟨GaloisField 2 n,inferInstance,inferInstance,?_,
    ⟨e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := GaloisField 2 n))⟩⟩
  simpa only [Nat.card_eq_fintype_card] using GaloisField.card 2 n (NeZero.ne n)

theorem quasisimple_impossible_of_local_thompson_moves
    (hmin : D.IsMinimalFullModule)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) : False := by
  rcases Selection.ModuleChoice.moving_local_natural_of_minimal D hmin
      (fun hn => c.t_not_normalizes (hn c.t_mem)) hna hJ with hr | hb
  · exact quasisimple_impossible_of_rankOneNatural D c hna hr
  · obtain ⟨e,⟨d⟩⟩ := hb
    exact quasisimple_impossible_of_natural_binary_three D c e d

theorem quasisimple_impossible_of_full_fixed_ne_bot
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) : False :=
  quasisimple_impossible_of_local_thompson_moves D c hmin hna
    (Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot D hmany hfixed)
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
