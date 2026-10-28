module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple

/-!
# Characteristic-normalizer control in the first plane-escape case

Let S = C_T(ZS) and suppose M ∩ I lies in Mc ∩ I. Every nontrivial
characteristic subgroup of S is normalized by T, since |T:S| = 2.
Its normalizer is a two-local containing T, hence lies in M or Mc by
15.2.5. Intersecting with I controls the full characteristic-normalizer
closure C(I,S) inside Mc ∩ I.

The genuine known-simple C.1.28 theorem then produces a chi-block of I
outside Mc ∩ I if F*(I) = O₂(I). The SQTK hypothesis is inherited from
an actual maximal two-local overgroup of I; the Sylow subgroup and all
subtype maps are those of the original escaping I.

This supplies the characteristic-normalizer premise in the first case of
15.2.23, without an extra C.1.18 pair or normalizer-control hypothesis.
Excluding the resulting blocks remains a separate part of 15.2.23.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.18(3i), 15.2.19(1), and 15.2.23, printed pp.1113--1116;
C.1.28, printed p.133; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The first alternative of 15.2.18(3) controls the literal C(I,S). -/
theorem characteristic_control_of_intersection_le
    (hI : PlaneEscapes Mc ZS I) (hNI : M ⊓ I ≤ Mc ⊓ I) :
    ((planeSylow T ZS).subgroupOf I).characteristicNormalizerClosure ≤
      (Mc ⊓ I).subgroupOf I := by
  let R := (planeSylow T ZS).subgroupOf I
  have hSI : planeSylow T ZS ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hRS : R.map I.subtype = planeSylow T ZS := map_subgroupOf_eq_of_le hSI
  have hTR : (T : Subgroup G) ≤ normalizer (R.map I.subtype : Set G) := by
    rw [hRS]
    exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (normal_of_index_eq_two (d.escape_index hI).2)
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
    ((((T.isPGroup'.to_le (show planeSylow T ZS ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
      (K := I)).to_subgroup C).map R.subtype).map I.subtype
  have hAne : A ≠ ⊥ := by
    intro h
    apply hne
    exact (C.map_eq_bot_iff_of_injective R.subtype_injective).mp
      (((C.map R.subtype).map_eq_bot_iff_of_injective I.subtype_injective).mp h)
  have hlocal : IsTwoLocal (normalizer (A : Set G)) := ⟨A,hAne,hAp,rfl⟩
  obtain ⟨N,hAN,hN⟩ := Finite.exists_le_maximal hlocal
  have hNmem : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hN,hTA.trans hAN⟩
  rw [d.two_maximals,Set.mem_insert_iff,Set.mem_singleton_iff] at hNmem
  intro x hx
  have hxA : (x : G) ∈ normalizer (A : Set G) :=
    le_normalizer_map I.subtype (mem_map_of_mem I.subtype hx)
  rcases hNmem with rfl | rfl
  · exact hNI ⟨hAN hxA,x.property⟩
  · exact ⟨hAN hxA,x.property⟩

/-- Apply the proved C.1.28 to I with its original Sylow image. -/
theorem escaping_chi_block_of_characteristic_control
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hcontrol : ((planeSylow T ZS).subgroupOf I).characteristicNormalizerClosure ≤
      (Mc ⊓ I).subgroupOf I) :
    ∃ X : Subgroup I, ChapterC.IsChiBlockIn X ∧
      ¬ X.map I.subtype ≤ Mc ⊓ I := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hSI : planeSylow T ZS ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hPS : (P : Subgroup I) = (planeSylow T ZS).subgroupOf I := by
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
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hNI : M ⊓ I ≤ Mc ⊓ I) :
    ∃ X : Subgroup I, ChapterC.IsChiBlockIn X ∧
      ¬ X.map I.subtype ≤ Mc ⊓ I :=
  d.escaping_chi_block_of_characteristic_control hI hfit
    (d.characteristic_control_of_intersection_le hI hNI)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
