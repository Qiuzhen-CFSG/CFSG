module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksFive
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksSeven
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple

/-!
# The equality-row chi-block exclusion and the original NI ≤ MI branch

The actual L₂, A₃, A₅ and A₇ block actions exclude every chi-block of the
original escaping I. If NI = M∩I lies in MI = Mc∩I, the source's two
maximal Sylow overgroups control every characteristic normalizer of S.
The proved known-simple C.1.28 theorem then supplies a chi-block outside
MI, closing this branch of original 15.2.23.

Only the original ResidualInput, equality row Kc = K and characteristic-two
hypothesis on the escaping I remain. The partner prime-to-three residual
identity and PlaneUniquenessPreceding are neither assumed nor constructed.

Source: Aschbacher--Smith, preliminary 15.2.23 and its first branch,
printed pp.1115--1116; C.1.28, printed p.133, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- All original chi-block alternatives are excluded in the equality row. -/
theorem no_chi_block_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (X : Subgroup I) : ¬ ChapterC.IsChiBlockIn X := by
  intro hX
  rcases r.chi_block_alternating_five_or_seven_of_eq he hI hfit hX with h5 | h7
  · exact r.a5_block_false_of_eq he hI hfit hX.1 h5
  · exact r.a7_block_false_of_eq he hI hfit hX.1 h7

/-- The first alternative of 15.2.18(3) controls the literal C(I,S). -/
theorem characteristic_control_of_intersection_le
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hNI : M ⊓ I ≤ Mc ⊓ I) :
    ((planeSylow T (⁅V,B⁆ : Subgroup G)).subgroupOf I).characteristicNormalizerClosure ≤
      (Mc ⊓ I).subgroupOf I := by
  let R := (planeSylow T (⁅V,B⁆ : Subgroup G)).subgroupOf I
  have hSI : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ I :=
    (le_sup_right.trans (r.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  have hRS : R.map I.subtype = planeSylow T (⁅V,B⁆ : Subgroup G) := map_subgroupOf_eq_of_le hSI
  have hTR : (T : Subgroup G) ≤ normalizer (R.map I.subtype : Set G) := by
    rw [hRS]
    exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (normal_of_index_eq_two (r.escape_index hI).2)
  apply (characteristicNormalizerClosure_le_iff R _).mpr
  intro C hC hne
  let := hC
  let A := (C.map R.subtype).map I.subtype
  have hTA : (T : Subgroup G) ≤ normalizer (A : Set G) := by
    apply hTR.trans
    first
    | exact normalizer_le_normalizer_characteristic_map R C I.subtype I.subtype_injective
    | exact normalizer_le_normalizer_characteristic_map I.subtype I.subtype_injective R C
  have hAp : IsPGroup 2 A :=
    ((((T.isPGroup'.to_le (show planeSylow T (⁅V,B⁆ : Subgroup G) ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
      (K := I)).to_subgroup C).map R.subtype).map I.subtype
  have hAne : A ≠ ⊥ := by
    intro h
    apply hne
    exact (C.map_eq_bot_iff_of_injective R.subtype_injective).mp
      (((C.map R.subtype).map_eq_bot_iff_of_injective I.subtype_injective).mp h)
  have hlocal : IsTwoLocal (normalizer (A : Set G)) := ⟨A,hAne,hAp,rfl⟩
  obtain ⟨N,hAN,hN⟩ := Finite.exists_le_maximal hlocal
  have hNmem : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN,hTA.trans hAN⟩
  rw [r.two_overgroups,Set.mem_insert_iff,Set.mem_singleton_iff] at hNmem
  intro x hx
  have hxA : (x : G) ∈ normalizer (A : Set G) :=
    le_normalizer_map I.subtype (mem_map_of_mem I.subtype hx)
  rcases hNmem with rfl | rfl
  · exact hNI ⟨hAN hxA,x.property⟩
  · exact ⟨hAN hxA,x.property⟩

/-- Apply the proved C.1.28 to I with its original Sylow image. -/
theorem escaping_chi_block_of_characteristic_control
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    (hcontrol : ((planeSylow T (⁅V,B⁆ : Subgroup G)).subgroupOf I).characteristicNormalizerClosure ≤
      (Mc ⊓ I).subgroupOf I) :
    ∃ X : Subgroup I, ChapterC.IsChiBlockIn X ∧
      ¬ X.map I.subtype ≤ Mc ⊓ I := by
  obtain ⟨P,hP⟩ := r.sylow_in_escape_for_blocks hI
  have hSI : planeSylow T (⁅V,B⁆ : Subgroup G) ≤ I :=
    (le_sup_right.trans (r.residual_sup_planeSylow_le_for_blocks hI)).trans inf_le_right
  have hPS : (P : Subgroup I) = (planeSylow T (⁅V,B⁆ : Subgroup G)).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hSI]
    exact hP
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he,Subgroup.map_bot]
  obtain ⟨N,hN,hIN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  have hSQTK : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hsource.ambient.twoLocal_sqtk hN.1).subgroup (I.subgroupOf N))
  have hproper : (Mc ⊓ I).subgroupOf I ≠ ⊤ := by
    intro he
    have hm := congrArg (Subgroup.map I.subtype) he
    rw [map_subgroupOf_eq_of_le (inf_le_right : Mc ⊓ I ≤ I),
      ←MonoidHom.range_eq_map,range_subtype] at hm
    exact hI.2.2 (hm ▸ inf_le_left)
  obtain ⟨X,hout,hX,_⟩ :=
    ChapterC.RankOne.ChiProduct.SelectedRankOne.outside_moved_chi_knownSimple
      hSQTK hfit P ((Mc ⊓ I).subgroupOf I) (by simpa only [hPS] using hcontrol) hproper
  refine ⟨X,hX,?_⟩
  intro hle
  apply hout
  intro x hx
  exact hle (mem_map_of_mem I.subtype hx)

/-- The first case of 15.2.23 produces an escaping chi-block, with
characteristic-normalizer control discharged. -/
theorem escaping_chi_block_of_intersection_le
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (hfit : generalizedFitting I = pCore 2 I)
    (hNI : M ⊓ I ≤ Mc ⊓ I) :
    ∃ X : Subgroup I, ChapterC.IsChiBlockIn X ∧
      ¬ X.map I.subtype ≤ Mc ⊓ I :=
  r.escaping_chi_block_of_characteristic_control hI hfit
    (r.characteristic_control_of_intersection_le hI hNI)

/-- C.1.28 closes the original NI ≤ MI branch with every chi-block
excluded on the actual escaping I and its original Sylow subgroup. -/
theorem characteristicTwo_false_of_intersection_le_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hfit : generalizedFitting I = pCore 2 I)
    (hNI : M ⊓ I ≤ Mc ⊓ I) : False := by
  obtain ⟨X,hX,_⟩ := r.escaping_chi_block_of_intersection_le hI hfit hNI
  exact r.no_chi_block_of_eq he hI hfit X hX

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
