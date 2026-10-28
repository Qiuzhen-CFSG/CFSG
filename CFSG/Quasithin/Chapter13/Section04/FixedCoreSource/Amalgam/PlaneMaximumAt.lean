module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearShortThompson
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneActionAt

/-!
# Maximum elementary families from the guarded plane action

If J1(T) lies in the actual plane radical, its simultaneous marking
bounds maximum elementary images by two. Cardinal replacement gives
A(O2(LT)) contained in A(T), with the full centralizer kernel retained.
The second theorem constructs the marking on the original plane.
Source: Aschbacher--Smith 13.2.2(10), p.878, used in 13.4.7(4), p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V B : Subgroup G}

/-- The original LT core has the full maximum family when J₁ stays in
an actually marked second-parabolic radical. -/
theorem original_core_maximum_family_of_thompson_one_bound_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 6))
    (hk : q.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (hker : q.ker = centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)))
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (hT : ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map q =
      ChapterB.Offenders.Six.sylowCarrier ⊓ q.range)
    (hB : ((B.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map q ≤
      ChapterB.Offenders.D 6)
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G) := by
  let H := L ⊔ (T : Subgroup G)
  let S : Sylow 2 H := T.subtype le_sup_right
  let U := V.subgroupOf H
  have hVH : V ≤ H := D.le_sylow.trans le_sup_right
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le D.normalizes (((structural L h).2.2 V D).1)
  let : U.Normal := normal_subgroupOf_of_le_normalizer hHV
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVH
  have hUS : U ≤ (S : Subgroup H) := comap_mono D.le_sylow
  have hu : Nat.card U = 32 := (Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv).trans m.card_module
  have hr : 1 < ChapterB.twoRank (S : Subgroup H) := by
    have hb := elementary_card_le_maxOrder (S : Subgroup H) U hUS inferInstance
    rw [hu,ChapterB.maxOrder_eq_two_pow_rank] at hb
    by_contra! hn
    have hh : 2 ^ ChapterB.twoRank (S : Subgroup H) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by decide) hn
    omega
  have hjmap : (ChapterB.thompsonJ (S : Subgroup H) 1).map H.subtype =
      ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hj : (ChapterB.thompsonJ (S : Subgroup H) 1).map q ≤ ChapterB.Offenders.D 6 := by
    apply (map_mono (show ChapterB.thompsonJ (S : Subgroup H) 1 ≤
        (B.pCoreIn 2).subgroupOf H from ?_)).trans hB
    intro x hx
    exact hJ (hjmap ▸ mem_map_of_mem H.subtype hx)
  obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty (S : Subgroup H)
  have hc := ChapterB.maximum_image_le_two_of_thompson_one_image_le_D S q hr hY hT hj E hE
  have hf := max_family_centralizer_of_small_image (S : Subgroup H) U E hUS hE q hker hc
  have hcore : (S : Subgroup H) ⊓ centralizer (U : Set H) = pCore 2 H := by
    rw [←hker,hk,inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)]
  rw [hcore] at hf
  intro A hA
  let A0 := A.subgroupOf H
  have haH : A ≤ H := hA.1.trans (H.pCoreIn_le 2)
  have ha : A0.map H.subtype = A := map_subgroupOf_eq_of_le haH
  have hA0 : A0 ∈ elementaryAbelianMaxSubgroups (pCore 2 H) := by
    rw [←ChapterB.thompsonFamily_zero]
    apply (ChapterB.thompsonFamily_map_iff_of_injective H.subtype H.subtype_injective
      (pCore 2 H) A0 0).mp
    rw [ChapterB.thompsonFamily_zero,ha]
    exact hA
  have hAS := hf hA0
  have hh := (ChapterB.thompsonFamily_map_iff_of_injective H.subtype H.subtype_injective
    (S : Subgroup H) A0 0).mpr (by rwa [ChapterB.thompsonFamily_zero])
  have hsmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
  simpa only [ChapterB.thompsonFamily_zero,ha,hsmap] using hh

/-- Failure of J₁ movement in the original plane gives the source maximum
family inclusion, with the action and both image markings constructed. -/
theorem original_plane_maximum_family_of_thompson_one_bound_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    elementaryAbelianMaxSubgroups ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊆
      elementaryAbelianMaxSubgroups (T : Subgroup G) := by
  obtain ⟨q,hk,hker,hY,hT,hQ⟩ :=
    exists_original_plane_action_marking_at h structural D m eL W hW hTW
  rw [←hB] at hQ
  exact original_core_maximum_family_of_thompson_one_bound_at
    h structural D m q hk hker hY hT hQ hJ

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
