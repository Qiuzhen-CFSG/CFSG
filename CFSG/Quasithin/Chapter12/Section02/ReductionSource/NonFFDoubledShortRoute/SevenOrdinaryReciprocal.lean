module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJanko

/-!
# Residual uniqueness in the original non-FF doubled A7 row

Failure of uniqueness supplies an ordinary reciprocal component containing
the whole source orbit. Its central quotient is J4 by the actual catalogue
and residual exclusions, while the same original witness excludes J4 through
its large-center radical. Thus the odd fixed residual has precisely the
original normalizer N(L) as its unique maximal two-local overgroup.
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

/-- Original residual uniqueness, with every reciprocal component row excluded
on the same full orbit and quotient marking. -/
theorem sourceOrbit_seven_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) := by
  by_contra hnot
  obtain ⟨J,H,W,hw,_,_,_,_,K,hK,_,_,_,_⟩ :=
    D.sourceOrbit_seven_reciprocal_ordinary_component h hmany hnon σ hmodel A hA ho hnot
  exact D.sourceOrbit_seven_witness_ordinary_not_janko
    h hd hmany hnon σ hσ hmodel hA ho hw K hK
    (D.sourceOrbit_seven_witness_ordinary_janko h hd hmany hnon σ hmodel hA ho hw K hK)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
