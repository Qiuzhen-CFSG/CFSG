module
public import Theory.SpecificGroups.AlternatingSix.NaturalCubicGeneration
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.Preparation
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
import all Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The A₆ parabolic exclusion in original 14.3.6(2)

Suppose T normalizes a local component K and the actual K/O₂(K) action
lies in the natural S₆ subgroup of Aut(A₆). Both cubic parabolics over
T∩K are then T-invariant. Lift them using the equivariant quotient map
and adjoin T; their indices remain three. Original 14.3.5 puts both in M,
and their generating join forces K≤M.

The quotient kernel and natural action are explicit local hypotheses.
The subsequent terminal consumer must recover them from the flag geometry.
In particular T≤K is never assumed and natural outer transpositions remain
allowed. Source: Aschbacher--Smith 14.3.5--6(2), printed p.991.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open EmptyFamilySieve
variable {G : Type*} [Group G] [Finite G]

private theorem source_actual_cubic_le
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
    {B : Type*} [Group B] [Finite B]
    (q : K →* B) (hq : Function.Surjective q) (hker : q.ker = pCore 2 K)
    (a : T → MulAut B)
    (ha : ∀ (t : T) (k : K), a t (q k) = q (K.normalizerMonoidHom ⟨t,hn t.property⟩ k))
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B) (hPJ : (P : Subgroup K).map q ≤ J)
    (hi : ((P : Subgroup K).map q).relIndex J = 3)
    (hinv : ∀ t : T, J.map (a t).toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map q := by
  have hkerP : q.ker ≤ (P : Subgroup K) := hker ▸ pCore_isPGroup.le_sylow_of_normal P
  let N := M.subgroupOf K
  have hKover : K ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right⟩
    intro hb
    exact hK.2 ((map_eq_bot_iff_of_injective (pCore 2 ↥(K ⊔ (T : Subgroup G)))
      (K ⊔ (T : Subgroup G)).subtype_injective).mp hb)
  let Jpre := J.comap q
  let Jamb := Jpre.map K.subtype
  let Y := Jamb ⊔ (T : Subgroup G)
  have hPJpre : (P : Subgroup K) ≤ Jpre := (map_le_iff_le_comap).mp hPJ
  have hnorm : (T : Subgroup G) ≤ normalizer (Jamb : Set G) := by
    intro t ht
    let c := K.normalizerMonoidHom ⟨t,hn ht⟩
    let b := a ⟨t,ht⟩
    have he (k : K) : b (q k) = q (c k) := ha ⟨t,ht⟩ k
    have hbJ : J.map b.toMonoidHom = J := hinv ⟨t,ht⟩
    have hcJ : Jpre.map c.toMonoidHom = Jpre := by
      apply le_antisymm
      · rintro k ⟨l,hl,rfl⟩
        change q (c l) ∈ J
        rw [←he]
        exact hbJ ▸ mem_map_of_mem b.toMonoidHom hl
      · intro k hk
        refine ⟨c.symm k,?_,c.apply_symm_apply k⟩
        change q (c.symm k) ∈ J
        have hm : b (q (c.symm k)) ∈ J := by rwa [he,c.apply_symm_apply]
        have hcom : J.comap b.toMonoidHom = J := by
          have hh := congrArg (Subgroup.comap b.toMonoidHom) hbJ
          simpa only [comap_map_eq, (b.toMonoidHom.ker_eq_bot b.injective), sup_bot_eq] using hh.symm
        exact hcom ▸ hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Jpre.map K.subtype).map (MulAut.conj t).toMonoidHom = Jpre.map K.subtype
    have hc : (MulAut.conj t).toMonoidHom.comp K.subtype = K.subtype.comp c.toMonoidHom := by
      apply MonoidHom.ext
      intro k
      exact (normalizerMonoidHom_apply_apply_coe K ⟨t,hn ht⟩ k).symm
    rw [map_map,hc,←map_map,hcJ]
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

/-- The A₆ case of the local exclusion: the natural diagram kernel suffices. -/
theorem source_normalized_a6_le_of_natural_action
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
    (q : K →* alternatingGroup (Fin 6)) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 K) (a : T → MulAut (alternatingGroup (Fin 6)))
    (ha : ∀ (t : T) (k : K), a t (q k) = q (K.normalizerMonoidHom ⟨t,hn t.property⟩ k))
    (hnatural : ∀ t : T, a t ∈ AlternatingSix.ShadowLocal.natural) : K ≤ M := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let Pq := P.mapSurjective hq
  have haP (t : T) : ((Pq : Subgroup (alternatingGroup (Fin 6)))).map (a t).toMonoidHom = Pq := by
    have he : (a t).toMonoidHom.comp q =
        q.comp (K.normalizerMonoidHom ⟨t,hn t.property⟩).toMonoidHom := MonoidHom.ext (ha t)
    change ((P : Subgroup K).map q).map (a t).toMonoidHom = (P : Subgroup K).map q
    rw [hP,map_map,he,←map_map,
      NormalSylowQuotientAction.action_preserves_intersection K (T : Subgroup G) _ t.property]
  obtain ⟨J₁,J₂,h₁,h₂,hi₁,hi₂,hjoin,hinv⟩ :=
    AlternatingSix.NaturalCubicGeneration.invariant_cubic_pair Pq
  have hJ₁ := source_actual_cubic_le hG T hempty hM hu hmany hcard e hnot
    K hK hn q hq hker a ha P hP J₁ h₁ hi₁
    (fun t => (hinv (a t) (hnatural t) (haP t)).1)
  have hJ₂ := source_actual_cubic_le hG T hempty hM hu hmany hcard e hnot
    K hK hn q hq hker a ha P hP J₂ h₂ hi₂
    (fun t => (hinv (a t) (hnatural t) (haP t)).2)
  have himage : (M.subgroupOf K).map q = ⊤ := by
    exact top_le_iff.mp (hjoin ▸ sup_le hJ₁ hJ₂)
  have hkerM : q.ker ≤ M.subgroupOf K := by
    rw [hker]
    apply (pCore_isPGroup.le_sylow_of_normal P).trans
    rw [hP]
    exact fun _ hx => hM.1.2 hx
  have hMtop : M.subgroupOf K = ⊤ := by
    have hh := congrArg (Subgroup.comap q) himage
    rwa [comap_map_eq,sup_eq_left.mpr hkerM,comap_top] at hh
  intro k hk
  exact show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hMtop ▸ mem_top _
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
