module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Omega
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PerfectLift
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroQuotient

/-!
# Nonsolvable chi-block orbits outside the partner

The intrinsic signalizer module of an overgroup containing a block is
nonzero: its vanishing would kill the genuine block commutator module.
An A₅, A₇ or even-field L₂ block is perfect and equals its prime-to-three
residual, as does
its Sylow conjugate span. The normal-perfect-subgroup exclusion therefore
puts both this orbit and the original block outside the partner Mc.

The earlier orbit-residual alternative is supplied by the source geometry
owner and discharged by qt-e-152-plane-characteristic-two. All block,
residual and signalizer-module facts used here are proved from the actual
block structure, including orbits with more than one conjugate block.
Source: Aschbacher--Smith, preliminary 15.2.23, printed pp.1114--1115,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem block_overgroup_signalizer_ne_bot
    {X Y : Subgroup G} (hX : ChapterC.IsBlock X) (hXY : X ≤ Y) :
    intrinsicSignalizerModule Y ≠ ⊥ := by
  let A := X.subgroupOf Y
  have hA : ChapterC.IsBlock A :=
    ⟨inferInstance,ChapterC.RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe hXY).symm hX.short,hX.subnormal.subgroupOf⟩
  intro hz
  have he : (⁅(⊤ : Subgroup Y),omegaCenterIn (pCore 2 Y)⁆).map Y.subtype =
      intrinsicSignalizerModule Y := by
    unfold intrinsicSignalizerModule
    rw [signalizerModule_eq_commutator_omegaCenter]
    rw [map_commutator,omegaOneCenterAmbient_map_injective _ Y.subtype_injective,
      ← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hh : ⁅(⊤ : Subgroup Y),omegaCenterIn (pCore 2 Y)⁆ = ⊥ :=
    (map_eq_bot_iff_of_injective _ Y.subtype_injective).mp (he.trans hz)
  have hu : (ChapterC.blockU A).map A.subtype = ⊥ := by
    rw [← ChapterC.BlockOmega.omega_commutator hA]
    apply bot_unique
    rw [← hh,commutator_comm (omegaCenterIn (pCore 2 Y)) A]
    exact commutator_mono le_top le_rfl
  exact hA.short.blockU_ne_bot ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hu)

omit [Finite G] in
private theorem conjugateSpan_primeToResidual_eq_top (p : ℕ) (X S : Subgroup G)
    (hr : primeToResidual p X = ⊤) : primeToResidual p (conjugateSpanBy X S) = ⊤ := by
  let Y := conjugateSpanBy X S
  let R := (primeToResidual p Y).map Y.subtype
  have hXR : X ≤ R := by
    have hh := embedded_primeToResidual_mono p (le_conjugateSpanBy X S)
    simpa only [hr,← MonoidHom.range_eq_map,range_subtype] using hh
  have hSR : S ≤ normalizer (R : Set G) :=
    (le_normalizer_conjugateSpanBy X S).trans
      (normalizer_le_normalizer_characteristic_image Y (primeToResidual p Y))
  apply map_injective (f := Y.subtype) Y.subtype_injective
  rw [← MonoidHom.range_eq_map,range_subtype]
  exact le_antisymm (map_subtype_le _) (conjugateSpanBy_le hXR hSR)

namespace PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

theorem blockOrbit_signalizer_ne_bot (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) :
    intrinsicSignalizerModule (planeBlockOrbit T ZS X) ≠ ⊥ := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have he : (conjugateSpanBy X (P : Subgroup I)).map I.subtype = planeBlockOrbit T ZS X := by
    rw [map_conjugateSpanBy,hP]
  rw [← he,intrinsicSignalizerModule_map_of_injective _ I.subtype_injective]
  intro hz
  exact block_overgroup_signalizer_ne_bot hX (le_conjugateSpanBy X (P : Subgroup I))
    ((map_eq_bot_iff_of_injective _ I.subtype_injective).mp hz)

omit d [Finite G] in
theorem alternating_blockOrbit_perfect {X : Subgroup I} {n : ℕ}
    (hn : n = 5 ∨ n = 7) (hb : ChapterC.IsAlternatingBlock X n) :
    Group.IsPerfect (planeBlockOrbit T ZS X) := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rcases hn with rfl | rfl <;> simp)⟩
  let : Group.IsPerfect (X ⧸ pCore 2 X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect X := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  let eX := X.equivMapOfInjective I.subtype I.subtype_injective
  let : Group.IsPerfect (X.map I.subtype) :=
    Group.IsPerfect.ofSurjective (f := eX.toMonoidHom) eX.surjective
  exact conjugateSpanBy_isPerfect _ _

omit d in
theorem alternating_blockOrbit_threeResidual {X : Subgroup I} {n : ℕ}
    (hn : n = 5 ∨ n = 7) (hb : ChapterC.IsAlternatingBlock X n) :
    primeToResidual 3 (planeBlockOrbit T ZS X) = ⊤ := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  have hr := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 X)
    pCore_isPGroup hb.2.1.twoPerfect hd
  let eX := X.equivMapOfInjective I.subtype I.subtype_injective
  have hmap : primeToResidual 3 (X.map I.subtype) = ⊤ := by
    rw [← map_primeToResidual (p := 3) eX,hr,map_top_of_surjective _ eX.surjective]
  exact conjugateSpan_primeToResidual_eq_top 3 _ _ hmap

omit d [Finite G] in
theorem l2_blockOrbit_perfect {X : Subgroup I} {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : Group.IsPerfect (planeBlockOrbit T ZS X) := by
  have hq : Group.IsPerfect (X ⧸ pCore 2 X) := by
    rcases hb.2.1.quotient with hp | hc
    · let := hp
      infer_instance
    · obtain ⟨F,_,_,hF,_,hm⟩ := hb.2.2
      obtain ⟨e⟩ := hm.quotient_iso
      rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two] at hc
      have hl : 4 ≤ Nat.card F := by
        rw [hF]
        exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by have hn := hb.1; omega : 2 ≤ n)
      have hh := Nat.mul_le_mul hl
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hl 2) 1)
      norm_num at hh
      omega
  let := hq
  let : Group.IsPerfect X := hb.2.1.twoPerfect.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  let eX := X.equivMapOfInjective I.subtype I.subtype_injective
  let : Group.IsPerfect (X.map I.subtype) :=
    Group.IsPerfect.ofSurjective (f := eX.toMonoidHom) eX.surjective
  exact conjugateSpanBy_isPerfect _ _

omit d in
theorem l2_blockOrbit_threeResidual {X : Subgroup I} {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : primeToResidual 3 (planeBlockOrbit T ZS X) = ⊤ := by
  let : IsSimpleGroup (X ⧸ pCore 2 X) :=
    (show ChapterC.IsChiZeroBlock X from Or.inl ⟨n,hb⟩).quotient_simple
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    have hh := ChapterC.RankOne.ChiProduct.three_dvd_card_of_chi (Or.inl ⟨n,hb⟩)
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X)] at hh
    apply (Nat.prime_three.dvd_mul.mp hh).resolve_right
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    apply Nat.prime_three.coprime_iff_not_dvd.mp
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hr := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 X)
    pCore_isPGroup hb.2.1.twoPerfect hd
  let eX := X.equivMapOfInjective I.subtype I.subtype_injective
  have hmap : primeToResidual 3 (X.map I.subtype) = ⊤ := by
    rw [← map_primeToResidual (p := 3) eX,hr,map_top_of_surjective _ eX.surjective]
  exact conjugateSpan_primeToResidual_eq_top 3 _ _ hmap

theorem l2_blockOrbit_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hb : ChapterC.IsL2EvenBlock X n) : ¬ planeBlockOrbit T ZS X ≤ Mc := by
  let := l2_blockOrbit_perfect hb (T := T) (ZS := ZS)
  apply d.perfect_chi_orbit_not_le_partner horbit hI hfit ⟨hX,Or.inl ⟨n,hb⟩⟩
  · exact l2_blockOrbit_threeResidual hb
  · exact d.blockOrbit_signalizer_ne_bot hI hX

theorem alternating_blockOrbit_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hn : n = 5 ∨ n = 7) (hb : ChapterC.IsAlternatingBlock X n) :
    ¬ planeBlockOrbit T ZS X ≤ Mc := by
  let := alternating_blockOrbit_perfect hn hb (T := T) (ZS := ZS)
  apply d.perfect_chi_orbit_not_le_partner horbit hI hfit
    ⟨hX,Or.inr ⟨n,by rcases hn with rfl | rfl <;> decide,hb⟩⟩
  · exact alternating_blockOrbit_threeResidual hn hb
  · exact d.blockOrbit_signalizer_ne_bot hI hX

theorem alternating_block_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X) {n : ℕ}
    (hn : n = 5 ∨ n = 7) (hb : ChapterC.IsAlternatingBlock X n) :
    ¬ X.map I.subtype ≤ Mc := by
  intro hXM
  apply d.alternating_blockOrbit_not_le_partner horbit hI hfit hX hn hb
  apply conjugateSpanBy_le hXM
  exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left).trans
    Mc.le_normalizer

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
