module
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# The residual has trivial centralizer in the Sylow subgroup

In the original plane setup, the Sylow omega-center has order two. A nontrivial
T-normal subgroup of C_T(L) would meet that center. Normality of L in M then
makes L centralize the whole M-span of the central line, contradicting its
proved nontrivial action of order three on that plane.

This is original 14.2.2(6), with the residual L and every rank-two hypothesis
constructed from the actual source data. It supplies the centralizer
contradictions used in the abelian branch, notably 14.6.9 and 14.6.10.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.981, 1026, 1029.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

private theorem rankTwo_sylow_centralizer_eq_bot
    {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
  by_contra hne
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (h.sylow_normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf (T : Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hTC
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hne
  let : Nontrivial (C.subgroupOf (T : Subgroup G)) :=
    (subgroupOfEquivOfLe (show C ≤ (T : Subgroup G) from inf_le_left)).toEquiv.nontrivial
  let : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨A,_,hAC,hA,hAZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (C.subgroupOf (T : Subgroup G)) (p := 2) inferInstance
  let B := A.map (T : Subgroup G).subtype
  have hB : Nat.card B = 2 := by rw [card_map_of_injective (T : Subgroup G).subtype_injective,hA]
  have hBZ : B ≤ sylowOmega T := by
    rintro x ⟨a,ha,rfl⟩
    rw [Section02.sylowOmega_eq_centralInvolutions]
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨a.property,?_,?_⟩
    · have hh := pow_card_eq_one' (x := (⟨a,ha⟩ : A))
      rw [hA] at hh
      exact congrArg (fun x : A => ((x : T) : G)) hh
    · intro t ht
      exact congrArg Subtype.val (mem_center_iff.mp (hAZ ha) ⟨t,ht⟩)
  have hZcard : Nat.card (sylowOmega T) = 2 := by
    obtain ⟨_,F,_⟩ := h.exists_flag_geometry
    rw [h.sylowOmega_eq_point F]
    simpa using F.card 1 (by decide)
  have hBeq : B = sylowOmega T := eq_of_le_of_card_ge hBZ (by rw [hB,hZcard])
  have hZL : sylowOmega T ≤ centralizer (L : Set G) := by
    rw [←hBeq]
    rintro x ⟨a,ha,rfl⟩
    exact (hAC ha).2
  have hLC : L ≤ centralizer (rankTwoSeed T M : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes L (sylowOmega T) M
      ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
      (le_centralizer_iff.mp hZL)
  have hf : setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed = 1 := by
    ext l v
    change (l : G) * (v : G) * (l : G)⁻¹ = v
    rw [←hLC l.property v v.property,mul_inv_cancel_right]
  have hc := h.L_action_card
  rw [hf] at hc
  simp at hc

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original 14.2.2(6) on the actual residual used throughout §14.6. -/
theorem source_residual_sylow_centralizer_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    (T : Subgroup G) ⊓ centralizer (sourceResidual M Mc : Set G) = ⊥ :=
  rankTwo_sylow_centralizer_eq_bot
    (Section02.source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)

end CFSG.Quasithin.Chapter14.Section06
