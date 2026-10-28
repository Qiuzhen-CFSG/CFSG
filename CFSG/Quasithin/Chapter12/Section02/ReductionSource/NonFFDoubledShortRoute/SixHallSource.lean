module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SixOrdinaryReciprocal

/-!
# The actual surviving Hall outside component in the doubled A₆ source

The reciprocal ordinary alternative is impossible by original residual
uniqueness. The same original Hall actor therefore has the moved outside
component, with its whole-orbit normalization and full central cover retained.
This is the input contract for subsequent native family exclusions.
Source: Aschbacher--Smith 4.4.6--11, printed pp.620--621, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Original non-FF A₆ source gives a literal Hall actor and moved outside
ordinary component, with no uniqueness or placement premise. -/
theorem sourceOrbit_six_hall_outside_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      1 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧
        ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
        pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
        (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) ∧
        D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) := by
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,hcases⟩ :=
    D.sourceOrbit_six_hall_ordinary_alternatives h hd hmany hnon hmodel
  refine ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  rcases hcases with hc | ⟨hnot,_⟩
  · exact hc
  · let : Fact p.Prime := ⟨hp⟩
    let := he
    have hodd : Odd (Nat.card A) := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
      rw [hn]
      exact ho.pow
    exact (hnot (D.sourceOrbit_six_residual_uniqueness h hd hmodel A hAC hodd)).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
