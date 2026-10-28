module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleSource
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.OddThreeRank.Automorphisms
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.SpecificGroups.PSL4Two.SchurMultiplier
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismRank
public import GorensteinWalter.PSL2EvenDefiningKernel
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.TwoPrimary
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting

/-!
# Small-model exclusions for the original tensor point component

The full tensor module forces automorphism two-rank at least six on the
literal central quotient. This excludes the odd-characteristic and small
alternating rows. The ordinary Bender covers have no central involution;
their exceptional PSL₂(4) and Sz(8) rows have automorphism rank at most three.
The binary linear rows reduce to A₈ or to the trivial multiplier of PSL₅(2).

Source: Aschbacher--Smith 9.4.1, printed p.735; the covering calculations
are the actual central-extension results underlying I.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- None of the odd-characteristic C rows can be the literal central quotient. -/
theorem tensorPoint_containing_not_odd_quotient (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I] (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ ChapterA.Section02.IsTheoremCOddModel (I ⧸ center I) := by
  intro hm
  have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  cases hm with
  | linear_two p n hp ho _ hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    let : Nontrivial PSL(2,F) := a.symm.toEquiv.nontrivial
    let : Group.IsPerfect PSL(2,F) :=
      Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    have hlarge : 3 < Nat.card F :=
      Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ ho.pow) (Group.IsPerfect.not_isSolvable _)
    have hn : 0 < n := by
      by_contra! hn
      simp only [Nat.le_zero.mp hn, pow_zero] at hF
      omega
    rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
    have hhi := Theory.PSL2.odd_automorphism_two_rank F ⟨p,n,hp,ho,hn,hF⟩ hlarge
    omega
  | linear_three p hp ho hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
    have hhi := Theory.SpecificGroups.OddThreeRank.psl3_automorphism_two_rank_le_three
      hp ho hF
    omega
  | unitary_three p hp ho hm =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨a⟩⟩ := hm
    let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      a.symm.isSimpleGroup
    rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
    have hhi := Theory.SpecificGroups.OddThreeRank.psu3_automorphism_two_rank_le_three
      J hp ho hF hconj
    omega

/-- The alternating quotient exclusion includes the A₆ symplectic-derived row. -/
theorem tensorPoint_containing_not_alternating_quotient (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I] (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {n : ℕ} (hn : n ≤ 8) :
    ¬ Nonempty ((I ⧸ center I) ≃* alternatingGroup (Fin n)) := by
  rintro ⟨a⟩
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  have hn5 : 5 ≤ n := by
    by_contra hn5
    have hn4 : n ≤ 4 := by omega
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let f : (I ⧸ center I) →* Equiv.Perm (Fin 4) :=
      (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn4)).comp
        ((alternatingGroup (Fin n)).subtype.comp a.toMonoidHom)
    have hf : Function.Injective f :=
      (Equiv.Perm.viaEmbeddingHom_injective _).comp
        (Subtype.val_injective.comp a.injective)
    exact Group.IsPerfect.not_isSolvable (I ⧸ center I)
      (Group.isSolvable_of_isSolvable_injective hf)
  have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
  rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
  by_cases hn6 : n = 6
  · subst n
    have hhi := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.alternating_six_automorphism_two_rank
    omega
  by_cases hn8 : n = 8
  · subst n
    have hhi := BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
    rw [primeRank_equiv 2 (MulAut.congr
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)] at hhi
    omega
  have hn7 : n ≤ 7 := by omega
  let b : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective _
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)
  have hhi : primeRank 2 (Equiv.Perm (Fin n)) ≤ 4 := by
    apply primeRank_le_of_prime_pow_not_dvd
    intro hd
    rw [Nat.card_perm, Nat.card_fin] at hd
    have hd' := hd.trans (Nat.factorial_dvd_factorial hn7)
    norm_num [Nat.factorial] at hd'
  rw [primeRank_equiv 2 b] at hhi
  omega

/-- Both binary linear rows are excluded on the original marked quotient. -/
theorem tensorPoint_containing_not_linear_binary_quotient (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I] (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL (I ⧸ center I) n 2 := by
  rintro ⟨F, _, _, hF, ⟨a⟩⟩
  rcases hn with rfl | rfl
  · exact m.tensorPoint_containing_not_alternating_quotient v hv hLI hIN
      (by decide : 8 ≤ 8) ⟨a.trans (Matrix.PSL4Two.binaryEquivAlternatingEight F hF)⟩
  · exact m.tensorPoint_containing_center_ne_bot v hv hLI hIX
      (center_eq_bot_of_centralQuotientEquiv
        (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
          F hF) a)

/-- All three literal Bender families are incompatible with the containing component. -/
theorem tensorPoint_containing_not_bender_quotient (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I] (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ ClassificationModels.IsBenderModel (I ⧸ center I) := by
  intro hm
  have htwo := m.tensorPoint_containing_two_dvd_center v hv hLI hIX
  have hlo := m.tensorPoint_containing_quotient_automorphism_rank v hv hLI hIN
  cases hm with
  | linear n hn hm =>
    obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    by_cases hn2 : n = 2
    · subst n
      rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
      have hhi := Theory.PSL2.BinaryAutomorphismRank.psl2_automorphism_two_rank_le hn hF
      omega
    · have hn3 : 3 ≤ n := by omega
      have hlarge : 8 ≤ Nat.card F := by
        rw [hF]
        exact (show 2 ^ 3 ≤ 2 ^ n from Nat.pow_le_pow_right (by decide) hn3)
      have heven : Even (Nat.card F) := by
        rw [hF]
        exact (Nat.even_pow' (by omega)).mpr even_two
      let c := centralQuotientCover a
      have hker := GorensteinWalter.PSL2Cover.defining_prime_not_dvd_kernel_of_even
        F heven hlarge c.toMonoidHom c.surjective c.ker_le_center
      rw [ringChar.eq F 2, centralQuotientCover_ker] at hker
      exact hker htwo
  | unitary n hn hm =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨a⟩⟩ := hm
    have hker := BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.not_two_dvd_cover_kernel
      J hn hF hconj (centralQuotientCover a)
    rw [centralQuotientCover_ker] at hker
    exact hker htwo
  | suzuki k hk hm =>
    obtain ⟨a⟩ := hm
    by_cases hk1 : k = 1
    · subst k
      rw [primeRank_equiv 2 (MulAut.congr a)] at hlo
      have hhi := BenderSuzuki.MatrixGroups.suzuki_eight_automorphism_two_rank
      omega
    · have hk2 : 2 ≤ k := by omega
      exact m.tensorPoint_containing_center_ne_bot v hv hLI hIX
        (center_eq_bot_of_centralQuotientEquiv
          (BenderSuzuki.MatrixGroups.SchurCover.Family.canonicalKernel_eq_bot k hk2) a)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
