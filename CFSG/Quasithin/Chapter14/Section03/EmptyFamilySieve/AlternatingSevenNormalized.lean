module
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.AlternatingSeven
public import Theory.SpecificGroups.AlternatingSeven.InvariantCubicGeneration
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
import all Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The normalized A₇ component in the empty-family sieve

The source equality K = ⟨K^T⟩ says that T normalizes K; it does not put T
inside K. Intersect T with K and pass to K/O₂(K). Three cubic overgroups
of this Sylow subgroup generate A₇ and are invariant under every automorphism
preserving the Sylow. Their preimages are therefore normalized by the actual
T. Adjoining T preserves their relative index three. Original 14.3.5 places
these actual overgroups in M, and generation then forces K ≤ M.

The last theorem consumes the literal conjugate-closure mark and the outside
mark of the selected source component. Source: Aschbacher--Smith 14.3.6(5)
and the nonsolvable branch of 14.3.15, printed pp.992 and 994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual normalized local A₇ lift lies in M. -/
theorem source_normalized_a7_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : K ≤ M := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  have hkerP : q.ker ≤ (P : Subgroup K) := hker ▸ pCore_isPGroup.le_sylow_of_normal P
  let N := M.subgroupOf K
  have hPN : (P : Subgroup K) ≤ N := by
    rw [hP]
    exact fun _ hx => hM.1.2 hx
  have hkerN : q.ker ≤ N := hkerP.trans hPN
  have hKover : K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right⟩
    intro hb
    exact hK.2 ((map_eq_bot_iff_of_injective (pCore 2 ↥(K ⊔ (T : Subgroup G)))
      (K ⊔ (T : Subgroup G)).subtype_injective).mp hb)
  let Pq := P.mapSurjective hq
  have hgen : N.map q = ⊤ := by
    apply AlternatingSeven.InvariantCubicGeneration.sylow_invariant_cubic_generation Pq
    · exact map_mono hPN
    · intro J hPJ hi hinv
      let Jpre := J.comap q
      let Jamb := Jpre.map K.subtype
      let Y := Jamb ⊔ (T : Subgroup G)
      have hPJpre : (P : Subgroup K) ≤ Jpre := (map_le_iff_le_comap).mp hPJ
      have hnorm : (T : Subgroup G) ≤ normalizer (Jamb : Set G) := by
        intro t ht
        let a := K.normalizerMonoidHom ⟨t,hn ht⟩
        let b := (MulAut.congr eK) ((pCore 2 K).quotientAut a)
        have he (k : K) : b (q k) = q (a k) := by
          dsimp only [b,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, eK.symm_apply_apply,quotientAut_apply_mk]
        have hehom : b.toMonoidHom.comp q = q.comp a.toMonoidHom :=
          MonoidHom.ext he
        have haP : (P : Subgroup K).map a.toMonoidHom = P := by
          rw [hP]
          exact NormalSylowQuotientAction.action_preserves_intersection K (T : Subgroup G) _ ht
        have hbP : (Pq : Subgroup (alternatingGroup (Fin 7))).map b.toMonoidHom = Pq := by
          change ((P : Subgroup K).map q).map b.toMonoidHom = (P : Subgroup K).map q
          rw [map_map,hehom,←map_map,haP]
        have hbJ := hinv b hbP
        have haJ : Jpre.map a.toMonoidHom = Jpre := by
          apply le_antisymm
          · rintro k ⟨l,hl,rfl⟩
            change q (a l) ∈ J
            rw [←he]
            exact hbJ ▸ mem_map_of_mem b.toMonoidHom hl
          · intro k hk
            refine ⟨a.symm k,?_,a.apply_symm_apply k⟩
            change q (a.symm k) ∈ J
            have hm : b (q (a.symm k)) ∈ J := by rwa [he,a.apply_symm_apply]
            have hcom : J.comap b.toMonoidHom = J := by
              have hh := congrArg (Subgroup.comap b.toMonoidHom) hbJ
              simpa only [comap_map_eq, (b.toMonoidHom.ker_eq_bot b.injective), sup_bot_eq] using hh.symm
            exact hcom ▸ hm
        apply mem_normalizer_iff_map_conj_eq.mpr
        change (Jpre.map K.subtype).map (MulAut.conj t).toMonoidHom = Jpre.map K.subtype
        have hc : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp a.toMonoidHom := by
          apply MonoidHom.ext
          intro k
          exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ k).symm
        rw [map_map,hc,←map_map,haJ]
      have hYover := Chapter3.mem_HOver_of_sylow_interval T
        (show (T : Subgroup G) ≤ Y from le_sup_right)
        (show Y ≤ K ⊔ (T : Subgroup G) from sup_le_sup (map_subtype_le Jpre) le_rfl) hKover
      have hkerJ : q.ker ≤ Jpre := hkerP.trans hPJpre
      have hpreIndex : (P : Subgroup K).relIndex Jpre = 3 := by
        have hh := relIndex_map_map q (P : Subgroup K) Jpre
        rw [sup_eq_left.mpr hkerP,sup_eq_left.mpr hkerJ,
          map_comap_eq_self_of_surjective hq] at hh
        exact hh.symm.trans hi
      have hYindex : (T : Subgroup G).relIndex Y = 3 := by
        rw [show Y = Jamb ⊔ (T : Subgroup G) from rfl,
          relIndex_sup_of_normalizes_left Jamb (T : Subgroup G) hnorm]
        have hh := relIndex_comap (T : Subgroup G) K.subtype Jpre
        change ((T : Subgroup G).subgroupOf K).relIndex Jpre =
          (T : Subgroup G).relIndex Jamb at hh
        rw [←hP] at hh
        exact hh.symm.trans hpreIndex
      have hYM := source_index_three_le hG T hempty hM hu hmany hcard e hnot Y hYover hYindex
      have hpreN : Jpre ≤ N := (map_le_iff_le_comap).mp (le_sup_left.trans hYM)
      have hh := map_mono (f := q) hpreN
      rwa [map_comap_eq_self_of_surjective hq] at hh
  have hN : N = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hgen
    rwa [comap_map_eq,sup_eq_left.mpr hkerN,comap_top] at hh
  intro k hk
  exact show (⟨k,hk⟩ : K) ∈ N from hN ▸ mem_top _


/-- The A₇ row of the original empty-family sieve, with the actual conjugate
closure equality rather than a join with the ambient Sylow. -/
theorem source_orbit_a7_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (horbit : K = conjugateSpanBy K (T : Subgroup G)) (hout : ¬ K ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) : False := by
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have hh := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [←horbit] at hh
  exact hout (source_normalized_a7_le hG T hempty hM hu hmany hcard e hnot K hK hn eK)

end CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
