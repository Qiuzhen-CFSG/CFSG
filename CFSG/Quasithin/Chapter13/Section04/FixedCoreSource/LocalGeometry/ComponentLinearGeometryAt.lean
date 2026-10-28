module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentLinearMSAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearGeometry

/-!
# Original selected linear-three geometry from guarded source inputs

The point MS construction bounds cubic movement on the intrinsic core of
every subgroup of K by two. The source cubic L₀ lies in K by the genuine
normalizer bound, but its same intrinsic core has at least three cubic
layers. This excludes the covered original row. The natural point argument
then proves L₁≤K and both literal reciprocal residual identities.

The resulting geometry includes the chosen natural omega orbit, its equality
with [R₂(KT),K], both action kernels, the quotient KT/O₂(KT), and the full
central four-group. It preserves the original five-dimensional augmentation
marking and uses only same-G,T structural/module facts and the genuine earlier
fixed-module and natural LargeDistanceInput premises. ComponentFullLinearAt and ComponentLinearPairAt supply its full centralizer
and original pair. OriginalComponentGeometryAt
constructs the original-module application at every nonsolvable escaping point.
Source: Aschbacher--Smith 13.4.10(2--6), pp.908--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

open ChapterC.NaturalPointControl NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
private theorem ambient_embedded_core_length
    {G : Type u} [Group G] [Finite G] (K X : Subgroup G) (hKX : K ≤ X)
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (a : NaturalAction U) (hres : pResidual 2 X = K.subgroupOf X)
    (hi : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple a.LJ a.BJ)
    (N : Subgroup G) (hNK : N ≤ K) (A : Subgroup G)
    (hA : IsPGroup 3 A) (hAN : A ≤ N) :
    conjugationCubicLength A (N.pCoreIn 2) ≤ 2 := by
  let fi : N →* X := inclusion (hNK.trans hKX)
  let f : N →* a.J := fi.codRestrict a.J (fun n =>
    (show pResidual 2 X ≤ a.J from le_sup_left)
      (show fi n ∈ pResidual 2 X from hres.symm ▸ hNK n.property))
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun x : a.J => x.val.val) hxy)
  have hfK : f.range ≤ a.LJ := by
    rintro x ⟨n,rfl⟩
    change fi n ∈ pResidual 2 X
    rw [hres]
    exact hNK n.property
  obtain ⟨e,hm⟩ := a.natural_core_of_msInput hi
  let : IsElementaryAbelian 2 (U.subgroupOf a.J) := IsElementaryAbelian.subgroupOf a.module_le_J
  have hb := a.inMSGroup.embedded_core_length_le_two hi e hm f hf hfK
    (A.subgroupOf N) hA.comap_subtype
  have he := length_map_injective N.subtype N.subtype_injective (A.subgroupOf N) (pCore 2 N)
  rw [map_subgroupOf_eq_of_le hAN] at he
  exact he ▸ hb

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The covered row bounds cubic movement on the intrinsic core of every
actual subgroup of K, using its constructed Baumann MS pair. -/
theorem covered_linear_embedded_core_length_le_two_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (N : Subgroup G) (hNK : N ≤ K) (A : Subgroup G)
    (hA : IsPGroup 3 A) (hAN : A ≤ N) :
    conjugationCubicLength A (N.pCoreIn 2) ≤ 2 := by
  let R := (Solvable.firstCentralizerResidual L z.val ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K ⊔ R
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨hn,hel,a,_,hres,⟨hi⟩⟩ := covered_linear_component_ms_at hl h₀ h structural modules
    D m h1332 fixed hindex hc z hzT hzL hKz hHN hKM hfK eK
  let := hn
  let := hel
  exact ambient_embedded_core_length K X le_sup_left (U.subgroupOf X)
    a hres hi N hNK A hA hAN

/-- The three-layer lower bound and two-layer upper bound refer to the same
cubic and the same intrinsic O₂(L₀), excluding L₀ ≤ K. -/
theorem covered_zero_not_le_linear_component_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ¬ zero L ≤ K := by
  intro hZK
  have hq := Solvable.covered_zero_core_card hc
  have hd : 3 ∣ Nat.card (zero L) := by
    rw [←hq,←index_eq_card]
    exact (pCore 2 (zero L)).index_dvd_card
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := zero L) 3 hd
  let A := zpowers (a : G)
  have hA : Nat.card A = 3 := by rw [Nat.card_zpowers,(zero L).orderOf_coe a,ha]
  have hAZ : A ≤ zero L := zpowers_le.mpr a.property
  have hlo := covered_zero_cubic_length_ge_three h.toHypothesis1221 hc A hA hAZ
  have hup := covered_linear_embedded_core_length_le_two_at hl h₀ h structural modules
    D m h1332 fixed hindex hc z hzT hzL hKz hHN hKM hfK eK
    (zero L) hZK A (IsPGroup.of_card (n := 1) (by simpa using hA)) hAZ
  omega

theorem covered_linear_component_false_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : False :=
  covered_zero_not_le_linear_component_at hl h₀ h structural modules D m h1332 fixed
    hindex hc z hzT hzL hKz hHN hKM hfK eK
    (covered_zero_le_linear_component h D m hc z hzT hHN hKM eK)

/-- The selected linear-three row forces the original quotient to be ordinary A₆. -/
theorem ordinary_original_of_linear_component_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  let := h.quasisimple
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
    (augmentationCentralQuotient D m) ho with hc | ⟨_,hc⟩
  · exact ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6
      (augmentationCentralQuotient D m) hc⟩
  · exact (covered_linear_component_false_at hl h₀ h structural modules D m h1332 fixed
      hindex hc z hzT hzL hKz hHN hKM hfK eK).elim

theorem linear_component_geometry_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  obtain ⟨eL⟩ := ordinary_original_of_linear_component_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨DK,_,_,_,hfixed,mark,hZ,hcard⟩ := linear_component_marking_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨hLK,hrec,hres⟩ := ordinary_linear_component_residuals_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK eL
  obtain ⟨hwhole,hker,hseedker,hsupp,hquot⟩ := linear_component_whole_at hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hrle : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≤ 1 := by
    rw [Solvable.firstCentralizerResidual_threeRank]
    exact core_component_point_threeRank_le_one D m eL z hzL
  obtain ⟨_,hthree⟩ := Solvable.firstCentralizerResidual_order_of_marking D m z hzL
  have hrne : primeRank 3 (Solvable.firstCentralizerResidual L z.val) ≠ 0 :=
    fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  have hfix := component_full_fixed_line_at h structural z.val hz1 hzT hindex K hKz hKM
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
              (m.constant_mem_central_four_at h structural).2).2.1
            (fun he => m.constant_ne_one (Subtype.ext he))).symm))
      rw [←hd]
      exact zpowers_le.mpr ⟨(m.constant_mem_central_four_at h structural).2,m.constant_fixed⟩
  exact ⟨DK,mark,⟨eL⟩,hLK,by omega,hrec,hres,hwhole,hfixed,hZ,hcard,hZL,
    hfix,hsplit,hker,hseedker,hsupp,hquot⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
