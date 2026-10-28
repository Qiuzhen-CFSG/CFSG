module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.AlternatingStar
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarSource

/-!
# Applying the alternating star exclusions to the original point centralizer

The original point residual lies in L and hence normalizes O₂(LT).
Its simple two-core quotient retains the factor seven in both degrees
and the factor five in degree five. Applying `AlternatingStar` to these
literal groups excludes A7 and the degree-five A8 row. The degree-four
star component is therefore SL4(2) or SL5(2); in degree five, section
orders and cubic rank also remove every small and rank-one B.5 row.

The final theorem feeds both reductions to the nonsingular-centralizer
and degree-five zeroth-closure consumer. The remaining model and fixed-space
arguments, the ordinary J4 exclusion and later closure obligations remain
with qt-d-double-natural-centralizers. Independent pure fusion and corrected
MS retain their existing producers and final discharge at qt-d-1222-double-natural.
Source: Aschbacher--Smith 12.1.1--3, printed pp.788--790.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
/-- The remaining degree-five star models, with actual group identifications.
The rank-two and binary-five rows still require their source exclusions. -/
inductive FiveStarModel (A : Type*) [Group A] : Prop
  | linearThree (F : ChapterB.QuasisimpleSource.BinaryField) (equiv : A ≃* SL(3,F.Carrier))
  | symplectic (F : ChapterB.QuasisimpleSource.BinaryField) (large : 1 < F.degree)
      (equiv : A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : ChapterB.QuasisimpleSource.BinaryField) (large : 1 < F.degree)
      (equiv : A ≃* Atlas.G2.Model F.Carrier)
  | linearFiveTwo (equiv : A ≃* SL(5,ZMod 2))
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original nonsingular residual excludes A7 in both degrees and A8 in degree five.
This uses no assertion that C_T(w) is Sylow in C_G(w). -/
theorem doubleNatural_adapted_C27_not_alternating
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        ∀ d : ℕ, (d = 7 ∨ d = 8) → (d = 8 → n = 5) →
        ¬ Nonempty (starImage K Q K ≃* alternatingGroup (Fin d)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi d hd hn ⟨e⟩
  let R := B.pointResidual w
  have hRM : R ≤ B.localPointCentralizer w := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  let := (S.nonsingular_residual_local_cComponent w hw.nonsingular).perfect
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRM).toMonoidHom) (subgroupOfEquivOfLe hRM).surjective
  obtain ⟨eR⟩ := (S.nonsingular_residual_kernel_and_quotient w hw.nonsingular).2
  have hdeg : 3 ≤ n-1 := by have := B.degree; omega
  let := linear_simple hdeg
  let : IsSimpleGroup (R ⧸ pCore 2 R) :=
    (eR.trans (projectiveEquivLinear (by omega : 0 < n-1))).isSimpleGroup
  apply Nonsingular.no_alternating_star_of_section hi (le_inf hRM hRK) _ _ hd _ e
  · exact ((B.pointResidual_le w).trans inf_le_left).trans
      (le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _
          (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))))
  · rw [Nat.card_congr eR.toEquiv]
    rcases B.degree with he | he
    · subst n
      rw [Matrix.PSL3Two.card_PSL]
      decide
    · subst n
      rw [Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
        nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
  · intro he
    have hn := hn he
    subst n
    rw [Nat.card_congr eR.toEquiv,
      Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]

/-- Only the two actual binary linear groups remain in the degree-four star catalogue. -/
theorem doubleNatural_four_adapted_C27_star_linear
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        Nonempty (starImage K Q K ≃* SL(4,ZMod 2)) ∨
          Nonempty (starImage K Q K ≃* SL(5,ZMod 2)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hn hRK hi
  exact (D.doubleNatural_four_adapted_C27_star_models h B S w hw K hn hRK hi).resolve_left
    (D.doubleNatural_adapted_C27_not_alternating h B S w hw K hRK hi 7 (.inl rfl) (by omega))

/-- The degree-five star catalogue loses all alternating, small and rank-one rows.
No ambient Sylow hypothesis is added to the original nonnormal branch. -/
theorem doubleNatural_five_adapted_C27_star_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 5) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        Nonsingular.FiveStarModel (starImage K Q K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hRK hi
  let A := starImage K Q (B.pointResidual w)
  let C := starImage K Q K
  have hAC : A ≤ C := map_mono (comap_mono hRK)
  obtain ⟨_,⟨eA⟩⟩ := D.doubleNatural_adapted_C27_residual_marking h B S w hw K hRK hi
  let e := eA.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  have hc : Nat.card (A ⧸ pCore 2 A) = 20160 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  have hd : 20160 ∣ Nat.card C := hc ▸
    ((card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective _)).trans (card_dvd_of_le hAC))
  have hr : 2 ≤ primeRank 3 C := by
    have hh : 2 ≤ primeRank 3 A := by
      rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup,
        primeRank_equiv 3 e]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
    exact hh.trans (_root_.primeRank_le_of_injective 3 (inclusion hAC) (inclusion_injective hAC))
  cases star_model_from_source hi with
  | linearTwo F a =>
    have hb := Matrix.SL2.binary_odd_primeRank_le_one (F := F.Carrier) (by decide : Odd 3)
    rw [←primeRank_equiv 3 a] at hb
    change primeRank 3 C ≤ 1 at hb
    omega
  | linearThree F a => exact .linearThree F a
  | symplectic F large a => exact .symplectic F large a
  | g2 F large a => exact .g2 F large a
  | g2DerivedTwo a =>
    rw [Nat.card_congr a.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | alternating d hdegree a =>
    rcases hdegree with rfl | rfl | rfl | rfl
    all_goals
      first
      | exact (D.doubleNatural_adapted_C27_not_alternating h B S w hw K hRK hi
          8 (.inr rfl) (fun _ => rfl) ⟨a⟩).elim
      | rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hd
        norm_num [Nat.factorial] at hd
  | linearFiveTwo a => exact .linearFiveTwo a
  | tripleSix c a =>
    have hh : Nat.card C = 1080 := by
      rw [←(center C).card_mul_index,index_eq_card,Nat.card_congr c.toEquiv,
        Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [Nat.factorial]
    rw [hh] at hd
    norm_num at hd

/-- Apply both surviving star catalogues to the original nonsingular-centralizer
and degree-five closure conclusions. The J4 and remaining parabolic premises
retain their final discharge with this task; no universal C.2.7 Source is assumed. -/
theorem doubleNatural_nonsingular_controls_of_jankoFour_reduced_stars_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        (K.subgroupOf (B.pointCentralizer w)).Normal → B.pointResidual w ≤ K →
        2*(n-1) ≤ primeRank 2 (K ⧸ center K) →
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) → False) →
    (∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ¬ ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w < K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        KernelConclusion K Q → OffenderConclusion K Q →
        ((starImage K Q (B.pointResidual w)).subgroupOf
          (starM K Q (B.localPointCentralizer w))).Normal →
        Nonempty (((starImage K Q (B.pointResidual w)) ⧸
          pCore 2 (starImage K Q (B.pointResidual w))) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) →
        ((n = 5 ∧ Nonsingular.FiveStarModel (starImage K Q K)) ∨ (n = 4 ∧
          (Nonempty (starImage K Q K ≃* SL(4,ZMod 2)) ∨
            Nonempty (starImage K Q K ≃* SL(5,ZMod 2))))) →
        B.pointResidual w ≤ centralizer ((starV K Q).map (K ⊔ Q).subtype ⊓
          centralizer (B.pointSylow w : Set G) : Set G)) →
    B.NonsingularCentralizers ∧
      (n : ℕ∞) ≤ ChapterE.globalR (componentOrbit V (T : Subgroup G)) ∧
      (n = 5 → 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) := by
  let := D.doubledOrbit_elementary h
  intro hj hp
  apply D.doubleNatural_nonsingular_controls_of_jankoFour_C27_of_many h hmany B hj
  intro S w hw hc hn hout Q K hKn hRK hi hk ho hAn hAq
  apply hp S w hw hc hn hout K hKn hRK hi hk ho hAn hAq
  rcases B.degree with hn | hn
  · subst n
    exact .inr ⟨rfl,D.doubleNatural_four_adapted_C27_star_linear h B S w hw K hKn hRK.le hi⟩
  · subst n
    exact .inl ⟨rfl,D.doubleNatural_five_adapted_C27_star_models h B S w hw K hRK.le hi⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
