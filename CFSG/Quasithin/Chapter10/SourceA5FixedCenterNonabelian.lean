module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterTransvection
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveNonabelian

/-!
# Nonabelian Sylow action on the original fixed-center orbit

The actual H-star orbit W lies in the Baumann center and is moved by
T∩L₀. Apply the paired residual-action theorem inside the original local
join, then transport its derived-subgroup movement to G. Consequently
the prescribed Sylow image in H/C_H(W) is nonabelian and has order greater
than two. This removes the single S₃ possibility from the G.6 comparison.

No alignment with the original component pair, module coordinates or
independently chosen action is assumed. Source: Aschbacher–Smith 10.2.1,
printed p.743, using E.2.3 and G.6.4.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original Sylow derived subgroup moves every eligible H-star orbit W. -/
theorem source_a5_fixed_center_derived_not_centralizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G))) :
    ¬ ⁅(T : Subgroup G),(T : Subgroup G)⁆ ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H : Set G) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let J := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf J
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set J)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set J) := QuotientGroup.ker_mk' C
  obtain ⟨d,t,ht₁,ht₂,⟨c⟩⟩ := source_a5_paired_five_action D e hn hout
  have hWT : W ≤ (T : Subgroup G) :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1
  have hWJ : W ≤ J := hWT.trans le_sup_right
  have hW0 : W.subgroupOf J ≤ omegaOneCenterAmbient (ChapterB.baumann (S : Subgroup J)) := by
    apply (Subgroup.map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWJ,source_local_baumann_center_map]
    exact hWE
  have hnorm : (S : Subgroup J) ≤ normalizer (W.subgroupOf J : Set J) := by
    intro x hx
    exact le_normalizer_comap J.subtype
      (le_normalizer_conjugateSpanBy _ _ (hH.1.1.2 hx))
  have hmove : ¬ (S : Subgroup J) ⊓ pResidual 2 J ≤
      centralizer (W.subgroupOf J : Set J) := by
    intro hfix
    apply source_a5_fixed_center_orbit_action D e hn hne H hH
    intro g hg x hx
    have hgR : (⟨g,mem_sup_right hg.1⟩ : J) ∈ pResidual 2 J := by
      have hh := hg.2
      rw [←source_join_residual D] at hh
      obtain ⟨a,ha,he⟩ := hh
      have he' : a = (⟨g,mem_sup_right hg.1⟩ : J) := Subtype.ext he
      exact he' ▸ ha
    exact congrArg Subtype.val (hfix ⟨hg.1,hgR⟩ ⟨x,hWJ hx⟩ hx)
  have hnon := paired_baumann_derived_not_centralizes S
    (source_a5_minimal_parabolic D e hn) U hU (source_local_thompson_not_centralizes D hout)
    q hq hk d c ⟨t,ht₁,ht₂⟩ (W.subgroupOf J) hW0 hnorm hmove
  intro hc
  apply hnon
  have hmap : (⁅(S : Subgroup J),(S : Subgroup J)⁆ : Subgroup J).map J.subtype =
      ⁅(T : Subgroup G),(T : Subgroup G)⁆ := by
    rw [map_commutator]
    have hs : (S : Subgroup J).map J.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)
    rw [hs]
  intro g hg x hx
  apply Subtype.ext
  exact hc (hmap ▸ mem_map_of_mem J.subtype hg) x hx

/-- The prescribed Sylow image in the actual centralizer quotient is nonabelian. -/
theorem source_a5_fixed_center_sylow_image_nonabelian
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)))
    (hred : IsPReduced 2
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    letI := hred.normal
    ¬ IsMulCommutative (((T : Subgroup G).subgroupOf H).map
      (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)))) := by
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let S := (T : Subgroup G).subgroupOf H
  let := hred.normal
  let C := centralizer (W.subgroupOf H : Set H)
  let q := QuotientGroup.mk' C
  change ¬ IsMulCommutative (S.map q)
  intro ha
  let := ha
  have hbot : (⁅S,S⁆ : Subgroup H).map q = ⊥ := by
    rw [map_commutator,commutator_self_eq_bot_iff]
    infer_instance
  have hker : (⁅S,S⁆ : Subgroup H) ≤ C := by
    have hh : (⁅S,S⁆ : Subgroup H) ≤ q.ker := by
      rwa [Subgroup.map_eq_bot_iff] at hbot
    rwa [QuotientGroup.ker_mk'] at hh
  have hmap : (⁅S,S⁆ : Subgroup H).map H.subtype = ⁅(T : Subgroup G),(T : Subgroup G)⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hH.1.1.2]
  apply source_a5_fixed_center_derived_not_centralizes D e hn hne hout H hH hWE
  rw [←hmap]
  rintro g ⟨a,ha,rfl⟩ x hx
  have hxH : x ∈ H := hH.1.1.2
    (((mem_omegaOneCenterAmbient_iff _ _).mp (hWE hx)).1.1)
  exact congrArg H.subtype (hker ha ⟨x,hxH⟩ hx)

/-- In particular the same Sylow image has order greater than two, excluding
the single S3 row in the source model comparison. -/
theorem source_a5_fixed_center_sylow_image_card_gt_two
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hWE : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H ≤
      omegaOneCenterAmbient (ChapterB.baumann (T : Subgroup G)))
    (hred : IsPReduced 2
      ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H)) :
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
    letI := hred.normal
    2 < Nat.card (((T : Subgroup G).subgroupOf H).map
      (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)))) := by
  let := hred.normal
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H
  let A := ((T : Subgroup G).subgroupOf H).map
    (QuotientGroup.mk' (centralizer (W.subgroupOf H : Set H)))
  have hnon := source_a5_fixed_center_sylow_image_nonabelian D e hn hne hout H hH hWE hred
  change 2 < Nat.card A
  by_contra! hc
  have hd : Nat.card A ∣ 2 := by
    have hp : 0 < Nat.card A := Nat.card_pos
    rcases (show Nat.card A = 1 ∨ Nat.card A = 2 by omega) with he | he <;> simp [he]
  let : IsCyclic A := isCyclic_of_card_dvd_prime hd
  exact hnon inferInstance

end CFSG.Quasithin.Chapter10
