module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleG2
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleSmallModels
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields
public import Theory.SpecificGroups.Triality.StandardTwoRank.RankTable
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.Source
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source
public import Theory.SpecificGroups.G2Even.BinaryDerivedAutomorphismRank
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound

/-!
# All rank-two quotients of the tensor point component are excluded

The ordinary linear, symplectic, triality, Ree and Tits covers cannot have
the actual central nonsingular involution. The exceptional linear and
small derived groups have automorphism two-rank below the six forced by
the original tensor module. The separate G₂ argument handles its unique
field-four multiplier exception. The final theorem checks every literal
rank-two constructor of the source Theorem C catalogue.

Source: Aschbacher--Smith 9.4.1, printed p.735; A.2.4 and I.1.3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation PerfectCentralCovering
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The small linear quotients have insufficient rank; ordinary covers have odd center. -/
theorem tensorPoint_containing_not_psl3_even (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {n : ℕ} (hn : 1 ≤ n) :
    ¬ ClassicalGroup.IsPSL (I ⧸ center I) 3 (2 ^ n) := by
  rintro ⟨F, hField, hFinite, hF, ⟨a⟩⟩
  by_cases hsmall : n ≤ 2
  · have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
    rw [primeRank_equiv 2 (MulAut.congr a),
      Matrix.PSL3Even.automorphism_two_rank_eq F (by omega) hF] at hlo
    omega
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ n by omega)
    have hd := Matrix.PSL3.OrdinaryCenterRecognition.center_card_dvd
      (show Nat.card F ≠ 2 by omega) (show Nat.card F ≠ 4 by omega) a
    exact (by decide : ¬ 2 ∣ 3) ((m.tensorPoint_containing_two_dvd_center v hv hLI hIX).trans
      (hd.trans (Nat.gcd_dvd_left _ _)))

/-- Every ordinary even symplectic quotient has trivial universal kernel. -/
theorem tensorPoint_containing_not_psp4_even (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSp (I ⧸ center I) 2 (2 ^ n) := by
  rintro ⟨F, hField, hFinite, hF, ⟨a⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact m.tensorPoint_containing_center_ne_bot v hv hLI hIX
    (center_eq_bot_of_centralQuotientEquiv
      (Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.universalProjection_ker_eq_bot_of_card_pow
        hF (by omega))
      (a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm))

/-- The binary endpoint has rank five; all larger triality covers have odd kernel. -/
theorem tensorPoint_containing_not_triality (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {n : ℕ} (hn : 1 ≤ n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (I ⧸ center I) := by
  intro hm
  have hn0 : 0 < n := hn
  by_cases hn1 : n = 1
  · subst n
    have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
    have hr := Triality.Standard.TwoRank.automorphism_twoRank_eq_five_mul_of_model 1 hn0 hm
    omega
  · obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ n hn0).mp hm
    have hd := (centralQuotientCover a).kernel_card_dvd_universal
    rw [centralQuotientCover_ker] at hd
    exact Triality.Standard.CentralCovers.TwoPrimary.universal_not_two_dvd_kernel_of_two_le
      n hn0 (by omega) ((m.tensorPoint_containing_two_dvd_center v hv hLI hIX).trans hd)

/-- The actual positive-parameter Ree cover has odd kernel, including field eight. -/
theorem tensorPoint_containing_not_ree_f4 (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    {r : ℕ} (hr : 1 ≤ r) :
    ¬ Nonempty ((I ⧸ center I) ≃* ReeF4.Model r) := by
  rintro ⟨a⟩
  have hd := ReeF4.CentralCovers.TwoPrimary.not_two_dvd_kernel r hr (centralQuotientCover a)
  rw [centralQuotientCover_ker] at hd
  exact hd (m.tensorPoint_containing_two_dvd_center v hv hLI hIX)

/-- Compatible Parrott lifts force the actual Tits covering center to be trivial. -/
theorem tensorPoint_containing_not_tits (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G)) :
    ¬ Nonempty ((I ⧸ center I) ≃* Tits.ParrottGroup) := by
  rintro ⟨a⟩
  exact m.tensorPoint_containing_center_ne_bot v hv hLI hIX
    (center_eq_bot_of_centralQuotientEquiv
      Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot a)

/-- The actual binary G₂ derived quotient has automorphism two-rank at most three. -/
theorem tensorPoint_containing_not_g2_derived (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ Nonempty ((I ⧸ center I) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨a⟩
  have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
  rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
  have hhi := Atlas.G2.binary_derived_automorphism_two_rank_le_three
  omega


/-- The derived binary symplectic quotient is the literal alternating-six group. -/
theorem tensorPoint_containing_not_psp4_derived (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ Nonempty ((I ⧸ center I) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨a⟩
  exact m.tensorPoint_containing_not_alternating_quotient v hv hLI hIN (by decide : 6 ≤ 8)
    ⟨a.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- Every rank-two constructor of the original source C catalogue is excluded. -/
theorem tensorPoint_containing_not_rank_two_quotient (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (n : ℕ) : ¬ ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n := by
  intro hm
  cases hm with
  | linear hn hm => exact m.tensorPoint_containing_not_psl3_even v hv hLI hIX hIN hn hm
  | symplectic hn hm => exact m.tensorPoint_containing_not_psp4_even v hv hLI hIX hn hm
  | g2 hn hm => exact m.tensorPoint_containing_not_g2_even v hv hLI hIX hIN hn hm
  | triality hn hm => exact m.tensorPoint_containing_not_triality v hv hLI hIX hIN hn hm
  | ree_f4 r hr _ hm => exact m.tensorPoint_containing_not_ree_f4 v hv hLI hIX hr hm
  | symplectic_derived _ hm => exact m.tensorPoint_containing_not_psp4_derived v hv hLI hIN hm
  | g2_derived _ hm => exact m.tensorPoint_containing_not_g2_derived v hv hLI hIN hm
  | tits _ hm => exact m.tensorPoint_containing_not_tits v hv hLI hIX hm

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
