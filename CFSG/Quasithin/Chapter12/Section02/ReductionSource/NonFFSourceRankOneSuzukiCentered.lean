module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneCentered
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeCentered

/-!
# Suzuki odd-local control from residual uniqueness

The original residual lands normally in the full Suzuki-side Ree parabolic.
Its original centered commutator orbit contradicts the central-cover
calculation, closing the remaining rank-two component branch. Remark 4.4.2
and the existing Hall reduction give the arbitrary-odd and original-T Hall
applications with the actual kernel on L/O₂(L).

Residual uniqueness remains explicit for final source-theorem assembly.
Source: Aschbacher--Smith 4.4.12--14, printed pp.621--625, applied to 12.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The Ree centered-module contradiction closes the Suzuki component branch,
with the original residual and quotient maps. Residual uniqueness remains explicit. -/
theorem sourceOrbit_suzuki_abelian_odd_control_of_unique
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  by_contra hout
  have hcase := D.sourceOrbit_suzuki_ree_parabolic_of_unique h hV hs hm e A hne hA ho hu hout
  let := D.orbitComponent_quasisimple h.toHypothesis1221
  let : IsSimpleGroup (D.orbitComponent ⧸ center D.orbitComponent) := IsQuasisimple.simple
  let : Group.IsPerfect (D.orbitComponent ⧸ center D.orbitComponent) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center D.orbitComponent))
      (QuotientGroup.mk'_surjective _)
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h.toHypothesis1221 hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  have hdata := chosen_oddActorResidual_cover h.toHypothesis1221 D A hsect.1 hsect.2 ho hAV
  let eQ := Classical.choice (D.sourceOrbit_covering_central_quotient h.toHypothesis1221
    ((oddActorResidual_le L A).trans inf_le_left) hdata.1.subset)
  let F := oddActorResidual L A
  let π : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    eQ.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
      (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := eQ.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hn : ¬ Group.IsSolvable F := by
    intro hh
    let := hh
    exact Group.IsPerfect.not_isSolvable (D.orbitComponent ⧸ center D.orbitComponent)
      (Group.isSolvable_of_surjective hπ)
  exact no_ree_suzuki_centered_residual (hV ▸ hdata.2.2.1) (hV ▸ D.ne_bot)
    (hV ▸ hdata.2.1)
    (D.sourceOrbit_oddActorResidual_core_centralizes h.toHypothesis1221 hV A hA ho)
    hn hcase

/-- Remark 4.4.2 extends the proved Suzuki abelian branch to all odd actors.
The uniform residual-uniqueness input is retained for final source assembly. -/
theorem sourceOrbit_suzuki_odd_control_of_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hu : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card X)) : normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  apply odd_normalizer_control_of_abelian (W := D.sourceOrbit) ?_ X hne hX ho
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_suzuki_abelian_odd_control_of_unique h hV hs hm e A hn hA hodd
    (hu A hn hA hodd hc)

/-- The original-T Hall application uses the action kernel on L/O₂(L).
It now requires residual uniqueness instead of assuming odd-normalizer control. -/
theorem sourceOrbit_suzuki_hall_faithful_of_residual_uniqueness
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (hu : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup ChapterE.Section06.FixedPointBounds.ParabolicCartan.oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  apply D.sourceOrbit_hall_faithful_of_abelian_odd_control h hmany hV hnon ?_
    hH hlarge B hBM hHall
  intro A hn hA hodd hc
  let := hc
  exact D.sourceOrbit_suzuki_abelian_odd_control_of_unique h hV hs hm e A hn hA hodd
    (hu A hn hA hodd hc)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
