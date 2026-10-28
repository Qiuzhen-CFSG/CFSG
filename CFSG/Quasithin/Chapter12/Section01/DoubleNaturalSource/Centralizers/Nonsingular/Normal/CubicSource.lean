module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.SectionRank
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.Source
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Cubic

/-!
# The remaining degree-four cubic source branch

The original Q is Sylow in the section centralizer, and its unique cubic
block is normalized by the whole point centralizer. Restricting this Sylow
to KQ and retaining the original Thompson movement constructs the actual
binary rank-one Setup used by C.5.7, including its quotient and module maps.

The nonsingular assembly now asks for only this degree-four cubic exclusion
in its normal-residual branch: natural and A₅ blocks are excluded by
`BlockPlacement`, and degree five by `SectionRank`. Its remaining component,
cubic and nonnormal-parabolic premises belong to qt-d-double-natural-centralizers;
qt-d-1222-double-natural retains the final pure-fusion and closure discharge.
This is conditional assembly, not an unconditional proof of 12.1.1.
Source: Aschbacher--Smith, 12.1.1 and C.5.4--7, printed pp.788--789,155--160.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual cubic block and original Q satisfy the marked C.5.4 rank-one setup. -/
theorem doubleNatural_four_normal_cubic_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        IsAlternatingBlock K 3 →
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ →
        Nonempty (Section05.ConjugateSource.RankOne.Setup
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) K (ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK ha hmove
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have htype : IsChiBlock (K.subgroupOf
      (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) :=
    Or.inr ⟨3,by decide,ha.of_mulEquiv (subgroupOfEquivOfLe hKY).symm⟩
  have hHK := D.doubleNatural_four_normal_chi_block_normalized h B S w hw.nonsingular
    hc hn K hKY ⟨hK,htype⟩
  have hQK : Q ≤ normalizer (K : Set G) :=
    (D.doubleNatural_core_le_pointCentralizer h B w).trans hHK
  have hSY := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  have hQY : Q ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) := by
    obtain ⟨R,hR⟩ := hSY
    exact hR.symm.le.trans (map_subtype_le _)
  obtain ⟨P,hP⟩ := hSY.restrict (show Q ≤ K ⊔ Q from le_sup_right) (sup_le hKY hQY)
  exact Section05.BlockAnalysis.RankOneSetup.exists_normalized_cubic_setup ha Q
    (isPGroup_pCoreIn 2 _) hQK P hP hmove

/-- The actual centralizer and degree-five closure consumer, with the normal branch reduced
only to the normalized, marked degree-four cubic case. -/
theorem doubleNatural_nonsingular_controls_of_four_cubic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
    (n = 4 → ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        IsBlock (K.subgroupOf (B.pointCentralizer w)) → IsAlternatingBlock K 3 →
        B.pointCentralizer w ≤ normalizer (K : Set G) →
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ →
        (∀ N : Subgroup G, N ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          (N.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ (K ⊔ B.pointSylow w))).Normal → N = ⊥) →
        Section05.ConjugateSource.RankOne.Setup
          ((L ⊔ (T : Subgroup G)).pCoreIn 2) K (ZMod 2) →
        K ≤ normalizer (L : Set G)) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hchar hfour hparabolic
  apply D.doubleNatural_nonsingular_controls_of_normal_blocks_of_many h hmany B hchar _ hparabolic
  intro S w hw hc hn K hKY hK hKH hmove hno
  rcases B.degree with hdeg | hdeg
  · subst n
    have ht : IsChiZeroBlock K :=
      Section05.BlockAnalysis.chiZero_equiv (subgroupOfEquivOfLe hKY) hK.2
    rcases ht with ⟨k,hk⟩ | ha | ha
    · exact D.doubleNatural_normal_natural_block_le h B S w hw hc hn K hKY hK.1 hmove k hk
    · obtain ⟨C⟩ := D.doubleNatural_four_normal_cubic_setup h B S w hw hc hn K hKY hK.1 ha hmove
      exact hfour rfl S w hw hc hn K hKY hK.1 hKH.1 ha
        (D.doubleNatural_four_normal_chi_block_normalized h B S w hw.nonsingular
          hc hn K hKY hK.chi) hmove hno C
    · exact (D.doubleNatural_normal_no_alternatingFive_block h B S w hw hc hn K hKY hK.1 ha).elim
  · subst n
    exact (hKY.trans inf_le_left).trans
      (D.doubleNatural_five_adapted_normal_centralizer_le h B S w hw hc hn)

/-- Degree five retains only the characteristic-two and nonnormal-parabolic source arguments. -/
theorem doubleNatural_five_nonsingular_controls_of_characteristic_parabolic_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w)) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      B.pointResidual w ≤ centralizer (B.fixedLine : Set G)) →
    B.NonsingularCentralizers ∧
      (5 : ℕ∞) ≤ globalR (componentOrbit V (T : Subgroup G)) ∧
      0 < globalW (componentOrbit V (T : Subgroup G)) T := by
  let := D.doubledOrbit_elementary h
  intro hchar hparabolic
  obtain ⟨hc,hr,hw⟩ := D.doubleNatural_nonsingular_controls_of_four_cubic_of_many h hmany B
    hchar (fun he => (by omega : False).elim) hparabolic
  exact ⟨hc,hr,hw rfl⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
