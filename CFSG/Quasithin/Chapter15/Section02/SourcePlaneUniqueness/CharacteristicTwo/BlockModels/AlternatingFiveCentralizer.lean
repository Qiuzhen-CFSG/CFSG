module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingFive
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.RankOne
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Core

/-!
# The A5 block centralizer lies in the original parabolic

The quotient Borel has Sylow index three. The odd nontrivial subgroup
already constructed in K ∩ X therefore generates that Borel together with
its Sylow subgroup. Using the original Borel marking gives C_X(ZS) ≤ KS.
For a normal block this supplies the core identity for X₀QI needed by the
canonical best-offender theorem, with X₀ the literal Sylow conjugate span.

The exchanged pair case and the permutation action/offender comparison
remain with qt-e-152-char2-block-exclusion. The preceding Kc orbit
alternative is discharged by the enclosing characteristic-two owner.
Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem a5_sylowNormalizer_relIndex (P : Sylow 2 G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) :
    (P : Subgroup G).relIndex (normalizer (P : Set G)) = 3 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup G) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  let R := P.mapSurjective hq
  have hmap : (normalizer (P : Set G)).map q =
      normalizer (R : Set (alternatingGroup (Fin 5))) := P.normalizer_map_surjective q hq
  have he := relIndex_map_map q (P : Subgroup G) (normalizer (P : Set G))
  have hkN : q.ker ≤ normalizer (P : Set G) := hk.trans P.toSubgroup.le_normalizer
  rw [sup_eq_left.mpr hk,sup_eq_left.mpr hkN] at he
  rw [←he,hmap]
  change (R : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (R : Set (alternatingGroup (Fin 5)))) = 3
  have hc : Nat.card R = 4 := by
    rw [R.card_eq_multiplicity,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hB : Nat.card (normalizer (R : Set (alternatingGroup (Fin 5)))) = 12 := by
    have hs : ∀ j : Fin 5,
        Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) j) = 12 := by
      simp only [Nat.card_eq_fintype_card]
      decide +kernel
    rw [hi]
    exact hs i
  have hRN : (R : Subgroup (alternatingGroup (Fin 5))) ≤
      normalizer (R : Set (alternatingGroup (Fin 5))) := R.toSubgroup.le_normalizer
  have hm := ((R : Subgroup (alternatingGroup (Fin 5))).subgroupOf
    (normalizer (R : Set (alternatingGroup (Fin 5))))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv,hc,hB] at hm
  change 4 * (R : Subgroup (alternatingGroup (Fin 5))).relIndex
    (normalizer (R : Set (alternatingGroup (Fin 5)))) = 12 at hm
  omega

private theorem a5_borel_eq_sylow_sup_odd (P : Sylow 2 G)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5))
    (D : Subgroup G) (hD : D ≤ normalizer (P : Set G))
    (ho : Odd (Nat.card D)) (hd : D ≠ ⊥) :
    normalizer (P : Set G) = (P : Subgroup G) ⊔ D := by
  let B := normalizer (P : Set G)
  let P' := (P : Subgroup G).subgroupOf B
  let D' := D.subgroupOf B
  have hnot : ¬ D ≤ (P : Subgroup G) := by
    intro hle
    obtain ⟨n,hn⟩ := (P.isPGroup'.to_le hle).exists_card_eq
    have hz : n = 0 := by
      by_contra hz
      exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hz)
    exact hd (card_eq_one.mp (by simpa only [hz,pow_zero] using hn))
  have hi : P'.index = 3 := a5_sylowNormalizer_relIndex P e
  have hgen : P' ⊔ D' = ⊤ := (isCoatom_of_index_three P' hi).2 _
    (lt_of_le_of_ne le_sup_left (by
      intro he
      apply hnot
      intro a ha
      exact (le_sup_right.trans_eq he.symm) (show (⟨a,hD ha⟩ : B) ∈ D' from ha)))
  have hPB : (P : Subgroup G) ≤ B := P.toSubgroup.le_normalizer
  have hDB : D ≤ B := hD
  have hm := congrArg (map B.subtype) hgen
  simpa only [P',D',Subgroup.map_sup,map_subgroupOf_eq_of_le hPB,
    map_subgroupOf_eq_of_le hDB,← MonoidHom.range_eq_map,range_subtype] using hm.symm

namespace PlaneUniquenessPreceding
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual block centralizer is contained in KS, using the constructed odd intersection. -/
theorem a5_block_centralizer_le_parabolic
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 5) :
    X.map I.subtype ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS := by
  obtain ⟨D,hDX,ho,hd,hDK⟩ := d.chi_block_odd_intersection hI hfit
    ⟨hX,Or.inr ⟨5,by decide,hb⟩⟩
  obtain ⟨hCJ,P,e,i,hP,hJN,_⟩ := d.a5_block_borel_marking_of_source horbit hI hfit hX hb
  let f := I.subtype.comp X.subtype
  let D' := D.subgroupOf X
  have hDC : D' ≤ (centralizer (ZS : Set G)).comap f := by
    intro a ha
    exact d.residual_centralizes (hDK (mem_map_of_mem I.subtype ha))
  have hDN : D' ≤ normalizer (P : Set X) := by
    rwa [hCJ,hJN] at hDC
  have ho' : Odd (Nat.card D') := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv]
  have hd' : D' ≠ ⊥ := by
    intro he
    apply hd
    have hm := congrArg (map X.subtype) he
    simpa only [D',map_subgroupOf_eq_of_le hDX,Subgroup.map_bot] using hm
  have hgen := a5_borel_eq_sylow_sup_odd P e D' hDN ho' hd'
  have hm : (normalizer (P : Set X)).map f ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS := by
    rw [hgen,Subgroup.map_sup]
    apply sup_le
    · rw [hP]
      exact inf_le_left.trans le_sup_right
    · have he : D'.map f = D.map I.subtype := by
        rw [←map_map,map_subgroupOf_eq_of_le hDX]
      rw [he]
      exact hDK.trans le_sup_left
  rintro x ⟨⟨x,hx,rfl⟩,hc⟩
  have hn : (⟨x,hx⟩ : X) ∈ normalizer (P : Set X) := by
    rw [←hJN,←hCJ]
    exact hc
  exact hm (mem_map_of_mem f hn)

/-- In the singleton orbit branch, the literal extension has the required two-core. -/
theorem a5_normal_blockOrbit_core_eq
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) [X.Normal]
    (hb : ChapterC.IsAlternatingBlock X 5) :
    (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer
        (conjugateSpanBy ZS (planeBlockOrbit T ZS X) : Set G) := by
  let Y := X.map I.subtype
  let e : X ≃* Y := X.equivMapOfInjective I.subtype I.subtype_injective
  obtain ⟨a⟩ := hb.2.2.quotient_iso
  let eQ : (Y ⧸ pCore 2 Y) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans a
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (Y ⧸ pCore 2 Y) := eQ.isSimpleGroup
  have hn : I ≤ normalizer (Y : Set G) := by
    have hh := X.le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hSI : planeSylow T ZS ≤ I :=
    le_sup_right.trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have he : planeBlockOrbit T ZS X = Y :=
    le_antisymm (conjugateSpanBy_le le_rfl (hSI.trans hn)) (le_conjugateSpanBy _ _)
  rw [he]
  exact d.plane_span_extension_core_eq_of_simple_marking hI (map_subtype_le _) hn
    (hb.2.1.twoPerfect.of_surjective e.toMonoidHom e.surjective)
    (d.alternating_block_not_le_partner horbit hI hfit hX (Or.inl rfl) hb)
    (d.a5_block_centralizer_le_parabolic horbit hI hfit hX hb)

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
