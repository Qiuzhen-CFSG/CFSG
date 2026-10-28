module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFaithfulChiefs
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallSolvableCubic
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallPair

/-!
# The remaining original chief actions are the five-point actions

The small natural wreath row has solvable actor, and a minimal-parabolic
irreducible chief image is solvable exactly when the original group is.
Thus the original nonsolvable inside-core branch has only the single and
paired symmetric-five actions. The section markings upgrade to equivariant
coordinates on the whole original chief factors. The paired marking also
retains the exact offender base subgroup.

The original action kernel is O₂(H) by odd-normalizer control. This supplies
the literal actors for the remaining symmetric-five overlap calculation;
it does not assert that those rows are already excluded.
Source: Aschbacher--Smith, final paragraph of 3.1.9(6), p.578, applied in
8.2.2(1), p.715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterB
universe u
private theorem nonsolvable_small_chief_five
    {D W : Type u} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) [IsIrreducible ρ]
    (S : Sylow 2 D) (hp : IsMinimalParabolicOver S ⊤)
    (hff : IsFFModule (imageRepresentation ρ))
    (hs : ChiefSmallNaturalAlternatives (imageRepresentation ρ))
    (hns : ¬ Group.IsSolvable D) :
    Nonempty (ActionEquiv (imageRepresentation ρ)
      (BinaryPermutation.naturalRepresentation (Fin 5))) ∨
    ∃ e : ActionEquiv (imageRepresentation ρ) BinaryPermutation.FivePair.wreathRepresentation,
      (offenderSubgroup (imageRepresentation ρ)).map e.groupEquiv.toMonoidHom =
        BinaryPermutation.FivePair.baseSubgroup := by
  rcases hs with hs | hs | hs
  · exact (hns ((chief_image_solvable_iff S hp ρ hff).mp hs.solvable)).elim
  · exact Or.inl (minimalParabolic_chief_five_of_marked ρ S hp hff hs).1
  · exact Or.inr (minimalParabolic_chief_five_pair_of_marked ρ S hp hff hs)
end CFSG.Quasithin.Chapter8.MathieuShadowRows

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option backward.isDefEq.respectTransparency false in
/-- The unchanged original chief factors have actual single or paired
five-point markings and full action kernel O₂(H). All earlier action and
coordinate premises are constructed from the original branch inputs. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_five_actions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
        (actionHom (s.factorRepresentation i)).ker = pCore 2 H ∧
        (Nonempty (ActionEquiv (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (BinaryPermutation.naturalRepresentation (Fin 5))) ∨
        ∃ e : ActionEquiv (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
            BinaryPermutation.FivePair.wreathRepresentation,
          (offenderSubgroup (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))).map
            e.groupEquiv.toMonoidHom = BinaryPermutation.FivePair.baseSubgroup) := by
  obtain ⟨hU,a,A,_,_,_,_,ha,hs,hk⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural_faithful
      h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,?_⟩
  dsimp only
  intro s i hi
  let := s.factorRepresentation_irreducible i
  obtain ⟨e⟩ := (ha.chief s i hi).2
  exact ⟨(literal_chief_action_kernel_eq e).symm.trans hk,
    nonsolvable_small_chief_five (s.factorRepresentation i) (T.subtype hH.1.1.2)
      a.original_minimal ⟨_,(ha.chief s i hi).1⟩ ((ha.small_iff s i hi).mp hs) hns⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
