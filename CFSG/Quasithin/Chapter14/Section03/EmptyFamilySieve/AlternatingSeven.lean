module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.OriginalCubic
public import Theory.SpecificGroups.AlternatingSeven.CubicSylowGeneration

/-!
# The actual alternating-seven empty-family exclusion

Original 14.3.5 places every index-three overgroup of the ambient Sylow
subgroup in M. If the extracted local component contains that Sylow subgroup
and its two-core quotient is A₇, lift the concrete cubic Sylow overgroups of A₇.
Interval closure of H(T) puts the lifts in the original source family, so they
all lie in M. Their quotient images generate A₇; the two-core already lies in
T, hence the full component lies in M. The last theorem records the additional Sylow-containment specialization.
The source orbit equality K = ⟨K^T⟩ alone does not provide that hypothesis;
the normalized-component application is separate.

Source: Aschbacher--Smith 14.3.5, 14.3.6(5) and 14.3.15, printed pp.991--995.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 14.3.5, in the cubic case used by the model generation sieve. -/
theorem source_index_three_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hi : (T : Subgroup G).relIndex H = 3) : H ≤ M := by
  by_contra hout
  exact hnot (SolvableAmalgam.source_theoremE_of_index_three
    hG T hempty hM hu hmany hcard e H hH hout hi)

/-- When the ambient Sylow lies in the A₇ lift, its cubic overgroups lift
    through the two-core and force `K ≤ M`. -/
theorem source_a7_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hTK : (T : Subgroup G) ≤ K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : K ≤ M := by
  let P := T.subtype hTK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  have hkerP : q.ker ≤ (P : Subgroup K) := hker ▸ pCore_isPGroup.le_sylow_of_normal P
  let N := M.subgroupOf K
  have hPN : (P : Subgroup K) ≤ N := fun _ hx => hM.1.2 hx
  have hkerN : q.ker ≤ N := hkerP.trans hPN
  have hKover : K ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,hTK⟩
    intro hb
    have hc := hK.2
    rw [sup_eq_left.mpr hTK] at hc
    exact hc ((map_eq_bot_iff_of_injective (pCore 2 K) K.subtype_injective).mp hb)
  let Pq := P.mapSurjective hq
  have hgen : N.map q = ⊤ := by
    apply AlternatingSeven.CubicSylowGeneration.sylow_index_three_generation Pq
    · exact map_mono hPN
    · intro J hPJ hi
      let Jpre := J.comap q
      let Y := Jpre.map K.subtype
      have hPJpre : (P : Subgroup K) ≤ Jpre := (map_le_iff_le_comap).mp hPJ
      have hTY : (T : Subgroup G) ≤ Y := by
        have hh := map_mono (f := K.subtype) hPJpre
        simpa only [P,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTK] using hh
      have hYover := Chapter3.mem_HOver_of_sylow_interval T hTY (map_subtype_le Jpre) hKover
      have hkerJ : q.ker ≤ Jpre := hkerP.trans hPJpre
      have hpreIndex : (P : Subgroup K).relIndex Jpre = 3 := by
        have hh := relIndex_map_map q (P : Subgroup K) Jpre
        rw [sup_eq_left.mpr hkerP,sup_eq_left.mpr hkerJ,
          map_comap_eq_self_of_surjective hq] at hh
        exact hh.symm.trans hi
      have hYindex : (T : Subgroup G).relIndex Y = 3 := by
        have hh := relIndex_map_map_of_injective (f := K.subtype)
          (P : Subgroup K) Jpre K.subtype_injective
        rw [show (P : Subgroup K).map K.subtype = (T : Subgroup G) by
          simp only [P,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTK]] at hh
        exact hh.trans hpreIndex
      have hYM := source_index_three_le hG T hempty hM hu hmany hcard e hnot Y hYover hYindex
      have hpreN : Jpre ≤ N := (map_le_iff_le_comap).mp hYM
      have hh := map_mono (f := q) hpreN
      rwa [map_comap_eq_self_of_surjective hq] at hh
  have hN : N = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hgen
    rwa [comap_map_eq,sup_eq_left.mpr hkerN,comap_top] at hh
  intro k hk
  exact show (⟨k,hk⟩ : K) ∈ N from hN ▸ mem_top _

/-- The Sylow-containment specialization of the A₇ exclusion. The displayed
    join is not the conjugate closure occurring in the source extraction. -/
theorem source_a7_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hjoin : K = K ⊔ (T : Subgroup G)) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : False := by
  exact hout (source_a7_le hG T hempty hM hu hmany hcard e hnot K hK
    (hjoin ▸ le_sup_right) eK)

end CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
