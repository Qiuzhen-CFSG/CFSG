module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredPlacement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearWhole

/-!
# The selected linear-three component with the original covering row discharged

The covered-cubic exclusion constructs the ordinary original A₆ quotient.
Apply the natural point-centralizer calculation to obtain L₁≤K and both
reciprocal residual identities. The actual natural marking and whole-module
theorem identify the moved omega-orbit with [R₂(KT),K], its action kernel
with O₂(KT), and KT/O₂(KT) with SL₃(2). The full central seed has order four,
and its K-fixed line is exactly the original escaping involution line.

This assembles the linear-three branch of 13.4.10(2--6) on the original
five-dimensional augmentation module. No ordinary original quotient,
residual containment, module marking or whole-core equality is assumed.
The full-centralizer equality and 13.4.10(8)--17 remain with this owner.
Earlier Chapter12/13.3 inputs and the independent LargeDistanceInput retain
their producers and final discharge with qt-d-1341-fixed-core-source.
Source: Aschbacher--Smith 13.4.10, printed pp.907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Source geometry for the selected linear-three row, including the literal
reciprocal residuals and action kernel, with the original cover excluded. -/
theorem linear_component_geometry
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let H := K ⊔ (T : Subgroup G)
    let U := ⁅conjugateSpanBy Z K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Solvable.firstCentralizerResidual L z.val ≤ K ∧
      primeRank 3 (Solvable.firstCentralizerResidual L z.val) = 1 ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      (pResidual 2 (K ⊓ centralizer (Z : Set G) : Subgroup G)).map
          (K ⊓ centralizer (Z : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype ∧
      U = ⁅(ReducedModule H).map H.subtype,K⁆ ∧
      U ⊓ centralizer (K : Set G) = ⊥ ∧
      Z = V ⊓ Z ∧ Nat.card Z = 4 ∧
      Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) ∧
      Z ⊓ centralizer (K : Set G) = zpowers z.val ∧
      conjugateSpanBy Z K = U ⊔ zpowers z.val ∧
      H ⊓ centralizer (U : Set G) = H.pCoreIn 2 ∧
      H ⊓ centralizer (conjugateSpanBy Z K : Set G) = H.pCoreIn 2 ∧
      K ⊔ H.pCoreIn 2 = H ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let := h.quasisimple
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨eL⟩ := ordinary_original_of_linear_component hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,_,_,_,hfixed,mark,hZ,hcard⟩ := linear_component_marking hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨hLK,hrec,hres⟩ := ordinary_linear_component_residuals hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL
  obtain ⟨hwhole,hker,hseedker,hsupp,hquot⟩ := linear_component_whole hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hrle : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≤ 1 := by
    rw [Solvable.firstCentralizerResidual_threeRank]
    exact core_component_point_threeRank_le_one D m eL z hzL
  obtain ⟨_,hthree⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  have hrne : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≠ 0 :=
    fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  have hfix := component_full_fixed_line h structural z.val hz1 hzT hindex K hKz hKM
  have hsplit := component_seed_split h₀ hzT hz1 hKz (h1332 K hfK).1
  rw [hfix] at hsplit
  have hZL : Z ⊓ centralizer (L : Set G) = V ⊓ centralizer (L : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_right _ (hZ.le.trans inf_le_left)
    · have hd : zpowers m.constant.val = V ⊓ centralizer (L : Set G) :=
        eq_of_le_of_card_ge (zpowers_le.mpr ⟨m.constant.property,m.constant_fixed⟩) (by
          rw [m.card_fixed,Nat.card_zpowers]
          exact le_of_eq ((orderOf_eq_prime
            ((mem_omegaOneCenterAmbient_iff _ _).mp
              (m.constant_mem_central_four h structural).2).2.1
            (fun he => m.constant_ne_one (Subtype.ext he))).symm))
      rw [←hd]
      exact zpowers_le.mpr ⟨(m.constant_mem_central_four h structural).2,m.constant_fixed⟩
  exact ⟨DK,mark,⟨eL⟩,hLK,by omega,hrec,hres,hwhole,hfixed,hZ,hcard,hZL,
    hfix,hsplit,hker,hseedker,hsupp,hquot⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
