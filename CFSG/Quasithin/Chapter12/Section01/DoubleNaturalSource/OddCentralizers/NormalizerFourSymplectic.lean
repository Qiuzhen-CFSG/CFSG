module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerFourPlacement
public import Theory.SpecificGroups.SymplecticSix.LocalOrder

/-!
# Excluding the inner Sp₆(2) odd-normalizer component

The literal fixed residual descends to a perfect subgroup normalizing the
nontrivial image of its moved seed in the component central quotient.
Its order retains the factors five and seven. The binary symplectic local
calculation excludes this configuration: no nonzero invariant isotropic
space of dimension at most three has both primes in its full stabilizer.

Applied to the original unique-residual branch, this eliminates the last
inner component. The result retains the actual GL₄(2) outer section as the
remaining alternative, without asserting its exclusion.
Source: Aschbacher--Smith 4.4.10--12 and 12.1.9, pp.621--623,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource

/-- The original residual requires both five and seven in a genuine two-local,
which no binary symplectic six-space model admits. -/
theorem FourComponentLocalData.not_symplectic_six
    {Q : Type*} [Group Q] [Finite Q] (h : FourComponentLocalData Q) :
    ¬ ClassicalGroup.IsPSp Q 3 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let a := (Theory.SpecificGroups.SymplecticSix.pspFieldEquivZModTwo F hF).trans
    Theory.SpecificGroups.SymplecticSix.EvenProjective.equiv.symm
  obtain ⟨B,P,_,_,hP,hne,hN,_,h105⟩ := h.of_mulEquiv (e.trans a)
  exact Theory.SpecificGroups.SymplecticSix.twoLocal_not_dvd_thirtyFive
    (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
    ((by decide : 35 ∣ 105).trans (h105.trans (card_dvd_of_le hN)))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
include D h

/-- The full original unique-residual obstruction has only an outer-section branch. -/
theorem doubledFour_oddNormalizer_outer_of_unique_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* BinaryLinear.OuterCyclic.LinearGroup 4,
      Function.Surjective f := by
  rcases D.doubledOrbit_oddNormalizer_inner_or_outer_section h B A hA ho K hK with hi | he
  · obtain ⟨_,_,hf,hs⟩ := D.doubledFour_oddNormalizer_inner_symplectic_of_many h hmany B A
      hA ho hu hout K hK houtK hi hm
    exact ((D.doubledFour_oddNormalizer_placed_local h B A hA ho K hf).not_symplectic_six hs).elim
  · exact he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
