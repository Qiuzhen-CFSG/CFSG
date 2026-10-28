module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.LocalReduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.SylowKernelCore
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic

/-!
# Local reductions for the rank-one paragraph of 15.3.37

The hypotheses below are the genuine local conclusions preceding the
rank-one argument. They do not assert any restricted model or inner action.
Relative component subnormality restricts the supplied Sylow subgroup to L.
The nontrivial two-residual Y_L has order divisible by three, since it lies
in the two-by-three group Y₊ and cannot be a two-group.

For a rank-one Borel B = N_L(S ∩ L), uniqueness of the proper Sylow
overgroup gives M ∩ L ≤ B. Its two-core is S ∩ L, making B invariant under
Y₊S. Source 15.3.33(1) then gives B = M ∩ L once the concrete Borel's
characteristic-two property is proved. Thus B normalizes Y₊ by 15.3.11(4).
This property of the Borel remains an explicit model input here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11--12, 15.3.33(1), and the rank-one paragraph of 15.3.37,
printed pp.1123--1125 and 1134--1135.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
variable {G : Type*} [Group G] [Finite G]

structure Setup (Yplus S M I L : Subgroup G) : Prop where
  outside : I ∈ outsideFamily Yplus S M
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S
  sylow_le : S ≤ M
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  component_outside : ¬ L ≤ M
  orbit_eq : L = localSpan L S
  orbit_bound : (normalizer (L : Set G)).relIndex I ≤ 2
  theta_eq : theta (M ⊓ I) = Yplus
  normalizer_eq : I ⊓ normalizer (Yplus : Set G) = M ⊓ I
  quotient_three : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus)
  rank_component : primeRank 3 L = 1
  rank_yplus : primeRank 3 Yplus = 2
  residual_ne : componentPart Yplus L ≠ ⊥
  characteristic_two_containment : ∀ D : Subgroup G, D ≤ localSpan L S →
    Yplus ⊔ S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ M ⊓ I

variable {Yplus S M I L : Subgroup G} (h : Setup Yplus S M I L)
include h

omit [Finite G] in
theorem Setup.yplus_le : Yplus ≤ M ⊓ I := by
  rw [← h.theta_eq]
  exact theta_le _

theorem Setup.normalizes_component : Yplus ⊔ S ≤ normalizer (L : Set G) := by
  apply sup_le
  · exact ComponentIntersection.normalizes_of_index_le_two
      (le_sup_left.trans h.outside.1.2)
      (h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) h.orbit_bound
  · rw [h.orbit_eq]
    exact le_normalizer_conjugateSpanBy L S

theorem Setup.normalizes_intersection :
    Yplus ⊔ S ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
  le_normalizer_inf
    ((sup_le (h.yplus_le.trans inf_le_left) h.sylow_le).trans M.le_normalizer)
    h.normalizes_component

theorem Setup.component_sylow : ∃ P : Sylow 2 L,
    (P : Subgroup L).map L.subtype = S ⊓ L := by
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨T, hT⟩ := Q.exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf I) h.component.1
  let e := subgroupOfEquivOfLe h.component_le
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup L) = S.subgroupOf L := by
    change (T : Subgroup (L.subgroupOf I)).map e.toMonoidHom = _
    rw [hT, ← hQ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(y : I), hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, ?_⟩, hy, ?_⟩
      · change (y : G) ∈ L
        change (y : G) = (x : G) at hxy
        exact hxy.symm ▸ x.property
      · exact Subtype.ext hxy
  exact ⟨P, by rw [hP, subgroupOf_map_subtype]⟩

omit [Finite G] in
theorem Setup.intersection_proper : (M ⊓ L : Subgroup G) < L :=
  lt_of_le_of_ne inf_le_right (fun he => h.component_outside (he.symm.le.trans inf_le_left))

omit [Finite G] in
theorem Setup.component_nonsolvable : ¬ Group.IsSolvable L := by
  let e := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr (by
    intro hL
    apply h.residual_ne
    apply le_bot_iff.mp
    exact (ComponentIntersection.intersectionResidual_le Yplus L).trans
      (inf_le_right.trans hL.le))
  exact Group.IsPerfect.not_isSolvable L

theorem Setup.three_dvd_residual : 3 ∣ Nat.card (componentPart Yplus L) := by
  by_contra hn
  have hle : componentPart Yplus L ≤ Yplus.pCoreIn 2 :=
    SuzukiExclusion.le_twoCore_of_three_free
      ((ComponentIntersection.intersectionResidual_le Yplus L).trans inf_le_left)
      h.quotient_three hn
  have hp := (isPGroup_pCoreIn 2 Yplus).to_le hle
  have he := (ComponentIntersection.intersectionResidual_isPPerfect Yplus L).hom_eq_one_of_isPGroup
    hp (MonoidHom.id (componentPart Yplus L))
  apply h.residual_ne
  apply eq_bot_iff.mpr
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

theorem Setup.three_dvd_intersection : 3 ∣ Nat.card (M.subgroupOf L) := by
  have hle : componentPart Yplus L ≤ M ⊓ L := by
    intro x hx
    have hx' := ComponentIntersection.intersectionResidual_le Yplus L hx
    exact ⟨h.yplus_le hx'.1 |>.1, hx'.2⟩
  have hd := h.three_dvd_residual.trans (card_dvd_of_le hle)
  rwa [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
    (M ⊓ L : Subgroup G) ≤ L)).toEquiv,
    inf_subgroupOf_right] at hd

omit [Finite G] in
theorem Setup.intersection_le_borel (hb : ChapterF.Source.RankOneBorelFacts L S) :
    M ⊓ L ≤ ChapterF.Source.borel L S :=
  hb.unique_maximal _ (inf_le_inf_right L h.sylow_le) h.intersection_proper

theorem Setup.intersection_twoCore (hb : ChapterF.Source.RankOneBorelFacts L S) :
    (M ⊓ L : Subgroup G).pCoreIn 2 = S ⊓ L := by
  obtain ⟨P, hP⟩ := h.component_sylow
  have hPD : (P : Subgroup L) ≤ (M ⊓ L : Subgroup G).subgroupOf L := by
    intro x hx
    exact inf_le_inf_right L h.sylow_le (hP ▸ mem_map_of_mem L.subtype hx)
  have hnormal : M ⊓ L ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    h.intersection_le_borel hb |>.trans inf_le_right
  apply le_antisymm
  · have hc := pCoreIn_le_sylow ((M ⊓ L : Subgroup G).subgroupOf L) (P.subtype hPD)
    have hc' := map_mono (f := L.subtype) hc
    rw [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective,
      map_subgroupOf_eq_of_le inf_le_right] at hc'
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPD,
      hP] using hc'
  · apply le_pCoreIn_of_normalizes _ (inf_le_inf_right L h.sylow_le) hnormal
    rw [← hP]
    exact P.isPGroup'.map L.subtype

theorem Setup.borel_invariant (hb : ChapterF.Source.RankOneBorelFacts L S) :
    Yplus ⊔ S ≤ normalizer (ChapterF.Source.borel L S : Set G) := by
  have hT : Yplus ⊔ S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [← h.intersection_twoCore hb]
    exact h.normalizes_intersection.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ L) (pCore 2 (M ⊓ L : Subgroup G)))
  exact le_normalizer_inf h.normalizes_component
    (hT.trans (normalizer ((S ⊓ L : Subgroup G) : Set G)).le_normalizer)

theorem Setup.borel_eq_intersection (hb : ChapterF.Source.RankOneBorelFacts L S)
    (hchar : generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S)) :
    ChapterF.Source.borel L S = M ⊓ L := by
  apply le_antisymm _ (h.intersection_le_borel hb)
  apply le_inf
  · exact h.characteristic_two_containment _
      (hb.proper.le.trans h.orbit_eq.le) (h.borel_invariant hb) hchar |>.trans inf_le_left
  · exact hb.proper.le

theorem Setup.borel_normalizes_yplus (hb : ChapterF.Source.RankOneBorelFacts L S)
    (hchar : generalizedFitting (ChapterF.Source.borel L S) =
      pCore 2 (ChapterF.Source.borel L S)) :
    ChapterF.Source.borel L S ≤ normalizer (Yplus : Set G) := by
  rw [h.borel_eq_intersection hb hchar]
  exact (le_inf inf_le_left (inf_le_right.trans h.component_le)).trans
    (h.normalizer_eq.symm.le.trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.Candidates.RankOneAction
