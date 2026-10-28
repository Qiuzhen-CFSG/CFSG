module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixHallPlacement
public import Theory.SpecificGroups.SymplecticSix.BinaryTwoRankBound

/-!
# Excluding the actual binary symplectic Hall component for A₆

The original Hall actor gives literal whole-orbit placement and rank eight
in the full central quotient of its selected component. The actual binary
field and projective equivalences carry that quotient to Sp₆(2), whose
explicit Sylow coordinates give two-rank at most seven. The full component
center is retained throughout, and no parabolic or residual-placement
hypothesis is supplied.
Source: Aschbacher--Smith 4.4.12 and 12.1.9, printed pp.622 and 793,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Chapter4 Chapter4.Section04
open Theory.SpecificGroups.SymplecticSix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual outside Hall component cannot have binary symplectic
six-space as its full central quotient. -/
theorem sourceOrbit_six_oddNormalizer_not_symplectic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G)) :
    ¬ ClassicalGroup.IsPSp (K ⧸ center K) 3 2 := by
  intro hm
  obtain ⟨_,_,_,_,hr⟩ := D.sourceOrbit_six_oddNormalizer_symplectic_placement
    h hd hmodel A hne hAC ho hout K hK houtK hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let a := (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  have he := primeRank_congr 2 a
  have hb := binary_twoRank_le_seven
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
