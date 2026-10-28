module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Lifting the actual Hall-kernel action from the central quotient

The full module satisfies V=[V,L₀]. An actor in the literal section
centralizer of L₀ commutes with L₀ on V, since O₂(L₀) centralizes V.
The three-subgroups lemma therefore lifts fixation of V/C_V(L₀) to V.
The action constructed here is conjugation on that exact quotient.

For the original odd Hall kernel, the proved coprimality then reduces
fixation to a prime-support bound on its quotient-action image. A power
of |L/O₂(L)| is allowed, so this criterion does not incorrectly impose
the order bound for one constituent on the product of its two factors.
The FF model calculation proving that bound and the non-FF branch remain
with the Hall-faithfulness owner qt-d-10-nona5-hall-faithfulness.

Source: Aschbacher--Smith, 10.2.3(2), printed p.745, using 3.2.2(3)
and 10.1.3 (combined manuscript of 1 March 2004).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

private theorem orbit_core_centralizes_full :
    (localOrbit T L).pCoreIn 2 ≤ centralizer (D.fullModule : Set G) := by
  apply (pCoreIn_mono_of_normalizes (localOrbit T L).le_normalizer le_rfl).trans
  apply le_centralizer_iff.mpr
  intro v hv q hq
  obtain ⟨v',hv',rfl⟩ := D.fullModule_le_reduced (uniqueness D) hv
  obtain ⟨q',hq',rfl⟩ := hq
  exact congrArg Subtype.val
    (reducedPSubgroup_le_centralizer_pCore 2 D.maximalLocal hv' q' hq')

/-- Conjugation on the literal original V_M/C_{V_M}(L₀). -/
def sourceFullModuleQuotientAction : D.maximalLocal →* MulAut D.fullCentralQuotient :=
  (exists_quotient_conjugation_action D.maximalLocal D.fullModule
    (centralizer (localOrbit T L : Set G)) D.maximalLocal_normalizes_fullModule
    (normalizer_le_normalizer_centralizer (localOrbit T L))
    (show D.fullCentralizer.Normal from
      inferInstance)).choose

/-- The action preserves the original quotient projection and conjugation convention. -/
theorem sourceFullModuleQuotientAction_apply (m : D.maximalLocal) (v : D.fullModule) :
    sourceFullModuleQuotientAction D m (QuotientGroup.mk' D.fullCentralizer v) =
      QuotientGroup.mk' D.fullCentralizer
        ⟨(m : G) * (v : G) * (m : G)⁻¹,
          (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
            v.property⟩ :=
  (exists_quotient_conjugation_action D.maximalLocal D.fullModule
    (centralizer (localOrbit T L : Set G)) D.maximalLocal_normalizes_fullModule
    (normalizer_le_normalizer_centralizer (localOrbit T L))
    (show D.fullCentralizer.Normal from
      inferInstance)).choose_spec m v

/-- For a section-kernel actor, fixation of the central quotient lifts to
the full original module, without a splitting or irreducibility hypothesis. -/
theorem source_sectionKernel_fullModule_fixation
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hfix : B.subgroupOf D.maximalLocal ≤ (sourceFullModuleQuotientAction D).ker) :
    B ≤ centralizer (D.fullModule : Set G) := by
  have hBM : B ≤ D.maximalLocal := ((le_sectionCentralizer_iff B _).mp hB).1
  have hmove : ⁅B,D.fullModule⁆ ≤ centralizer (localOrbit T L : Set G) := by
    apply commutator_le.mpr
    intro b hb v hv
    let bM : D.maximalLocal := ⟨b,hBM hb⟩
    have hbfix : sourceFullModuleQuotientAction D bM = 1 := hfix hb
    have he := sourceFullModuleQuotientAction_apply D bM ⟨v,hv⟩
    rw [hbfix] at he
    have hh := QuotientGroup.eq_iff_div_mem.mp he.symm
    change b * v * b⁻¹ / v ∈ centralizer (localOrbit T L : Set G) at hh
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh
  have hcomm : ⁅localOrbit T L,B⁆ ≤ centralizer (D.fullModule : Set G) := by
    rw [commutator_comm]
    exact (((le_sectionCentralizer_iff B _).mp hB).2).trans
      (orbit_core_centralizes_full D)
  have ht := commutator_commutator_eq_bot_of_rotate
    (commutator_eq_bot_iff_le_centralizer.mpr hcomm)
    (commutator_eq_bot_iff_le_centralizer.mpr hmove)
  rw [←D.fullModule_eq_commutator (uniqueness D)] at ht
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ht)

/-- Fixing the full module is equivalent to fixing its literal central quotient
for subgroups of the original orbit-section kernel. -/
theorem source_sectionKernel_fullModule_fixation_iff
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L)) :
    B ≤ centralizer (D.fullModule : Set G) ↔
      B.subgroupOf D.maximalLocal ≤ (sourceFullModuleQuotientAction D).ker := by
  refine ⟨?_, source_sectionKernel_fullModule_fixation D B hB⟩
  intro hc
  apply quotient_conjugation_action_kills_commutator_layer
    D.maximalLocal D.fullModule (centralizer (localOrbit T L : Set G)) B
    (show D.fullCentralizer.Normal from inferInstance) D.maximalLocal_normalizes_fullModule
      ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)).le.trans bot_le)
    (sourceFullModuleQuotientAction D) (sourceFullModuleQuotientAction_apply D)

/-- The literal section kernel acts in the commutant of the original L₀
action on V_M/C_{V_M}(L₀), the group used by the FF scalar argument. -/
theorem source_sectionKernel_quotient_action_commutes :
    ((sectionCentralizer (localOrbit T L)).subgroupOf D.maximalLocal).map
        (sourceFullModuleQuotientAction D) ≤
      centralizer ((((localOrbit T L).subgroupOf D.maximalLocal).map
        (sourceFullModuleQuotientAction D)) : Set (MulAut D.fullCentralQuotient)) := by
  let C := sectionCentralizer (localOrbit T L)
  let X := localOrbit T L
  let M := D.maximalLocal
  have hCM : C ≤ M := ((le_sectionCentralizer_iff C X).mp le_rfl).1
  have hc : ⁅C,X⁆ ≤ centralizer (D.fullModule : Set G) :=
    (((le_sectionCentralizer_iff C X).mp le_rfl).2).trans
      (orbit_core_centralizes_full D)
  have hk : (centralizer (D.fullModule : Set G)).subgroupOf M ≤
      (sourceFullModuleQuotientAction D).ker := by
    exact quotient_conjugation_action_kills_commutator_layer M D.fullModule
      (centralizer (X : Set G)) (centralizer (D.fullModule : Set G))
      (show D.fullCentralizer.Normal from inferInstance) D.maximalLocal_normalizes_fullModule
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (le_rfl : centralizer (D.fullModule : Set G) ≤
          centralizer (D.fullModule : Set G)))).le.trans bot_le)
      (sourceFullModuleQuotientAction D) (sourceFullModuleQuotientAction_apply D)
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator, Subgroup.map_eq_bot_iff]
  apply le_trans _ hk
  apply map_le_iff_le_comap.mp
  rw [map_commutator, map_subgroupOf_eq_of_le hCM,
    map_subgroupOf_eq_of_le X.le_normalizer]
  exact hc

/-- Coprimality eliminates the actual quotient-action image once its prime
support is bounded by that of the original component quotient. -/
theorem source_odd_sectionKernel_fixes_of_quotient_image_dvd
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hodd : Odd (Nat.card B))
    (hB : B ≤ sectionCentralizer (localOrbit T L)) (n : ℕ)
    (hd : Nat.card ((B.subgroupOf D.maximalLocal).map
      (sourceFullModuleQuotientAction D)) ∣ Nat.card (L ⧸ pCore 2 L) ^ n) :
    B ≤ centralizer (D.fullModule : Set G) := by
  have hBM : B ≤ D.maximalLocal := ((le_sectionCentralizer_iff B _).mp hB).1
  have hc := (source_nonnormal_odd_sectionKernel_coprime D hn B hodd hB).pow_right n
  have hi : Nat.card ((B.subgroupOf D.maximalLocal).map
      (sourceFullModuleQuotientAction D)) ∣ Nat.card B := by
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv] using
      card_map_dvd (B.subgroupOf D.maximalLocal) (sourceFullModuleQuotientAction D)
  have he := eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hc hi hd)
  exact source_sectionKernel_fullModule_fixation D B hB ((Subgroup.map_eq_bot_iff _).mp he)

/-- The original Hall kernel fixes D.fullModule under precisely the remaining
quotient-image order bound. Its oddness and coprimality are discharged here. -/
theorem source_hall_kernel_fixes_of_quotient_image_dvd
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (n : ℕ)
    (hd : Nat.card (((B.map H.subtype ⊓ sectionCentralizer (localOrbit T L)).subgroupOf
      D.maximalLocal).map (sourceFullModuleQuotientAction D)) ∣
        Nat.card (L ⧸ pCore 2 L) ^ n) :
    B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G) := by
  have ho : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact OddHall.odd_hall_odd hB
  have hm : Odd (Nat.card (B.map H.subtype)) := by
    rwa [card_map_of_injective H.subtype_injective]
  exact source_odd_sectionKernel_fixes_of_quotient_image_dvd D hn _
    (hm.of_dvd_nat (card_dvd_of_le inf_le_left)) inf_le_right n hd

end CFSG.Quasithin.Chapter10
