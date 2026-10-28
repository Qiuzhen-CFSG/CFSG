module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryJanko

/-!
# Original residual uniqueness in the doubled A₆ source

Failure of uniqueness gives the literal reciprocal witness and an ordinary
component containing the entire eight-dimensional orbit. Its central quotient
must be J₄, while the same witness excludes J₄ through its large-center radical.
Thus the original odd fixed residual has N(L) as its unique maximal two-local
overgroup. The outside component in the Hall actor's normalizer is separate.
Source: Aschbacher--Smith 4.4.6, printed p.620, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Residual uniqueness follows from the original A₆ orbit and odd actor;
no non-FF, uniqueness or ordinary-model premise is added. -/
theorem sourceOrbit_six_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,W,hw,hWJ,hJC,_,K,hK,_,_,_,_⟩ :=
    D.sourceOrbit_six_reciprocal_ordinary_component h hd hmodel A hAC ho hnot
  exact D.sourceOrbit_six_witness_ordinary_not_janko h hd hmodel hw hWJ hJC K hK
    (D.sourceOrbit_six_witness_ordinary_janko h hd hmodel hw hWJ hJC K hK)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
