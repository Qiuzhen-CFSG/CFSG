module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoTwoHigmanSims
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.EvenSetup

/-!
# Rudvalis rank-one reduction through the marked eight-subgroup

The sporadic step of Aschbacher--Smith 15.3.43 excludes Ru from the genuine
local configuration. This module proves a conditional reduction of that step
to five explicit calculations on the existing degree-4060 carrier.

First intersect the ambient Sylow subgroup with the normal component and
conjugate its image onto the certified `localP`. The exhaustive elementary
catalogue then identifies the source four-group with a row of order four.
The row-selection premise identifies it with `elementary 1`, whose full
inner normalizer is already proved to lie in `max4`.

The proposed enlargement uses `elementary 2`. Characteristicity inside
`localP` retains the conjugation action of every ambient Sylow element, even
when that action is outer on the component. Its two-group centralizer and
component--Sylow generation give an ambient characteristic-two normalizer.
Maximality forces this to equal the source local subgroup, contradicting a
member of `max4` that moves the four-group.

The row-selection, characteristicity, centralizer bound, max4 normalization
and movement premises of the terminal theorem still require proofs. This
module completes their compatible implication, not the unconditional Ru
exclusion. In particular, the existing maximal-subgroup cover is not applied
to a subgroup merely maximal subject to local characteristic two.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.43,
printed p.1140; the precise sporadic list is 1.1.5(3)(f), p.502. The marked
subgroups and ATLAS attribution are in `Rudvalis.Model.SylowOvergroups.Definitions`
and `RadicalCoverage.LocalCover.Data`; GLS3 Table 5.3r describes the local
structures motivating the remaining fixed-subgroup calculations.
-/

public section

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
namespace RudvalisLocalAction
variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

/-- An actual component marking aligns the Sylow intersection with `localP`
and the source plane with one of the certified elementary catalogue rows.
The order-four conclusion is derived from the source, not a catalogue label. -/
theorem exists_plane_marking (c : LocalConfiguration K S M Y V) (e : K ≃* Model) :
    ∃ (f : K ≃* Model) (i : Fin 6),
      (S.subgroupOf K).map f.toMonoidHom = localP ∧
      (V.subgroupOf K).map f.toMonoidHom = elementary i ∧
      Nat.card (elementary i) = 4 := by
  let : K.Normal := c.normal
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal K
  rw [hP] at hT
  let T' : Sylow 2 Model := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model T' MainConverse.SporadicLocal.RuEven.sylowTwo
  let f := e.trans (MulAut.conj g)
  have hfS : (S.subgroupOf K).map f.toMonoidHom = localP := by
    rw [← hT]
    have he := congrArg (fun Q : Sylow 2 Model => (Q : Subgroup Model)) hg
    rw [MainConverse.SporadicLocal.RuEven.sylowTwo_coe] at he
    change ((T : Subgroup K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = localP at he
    rw [map_map] at he
    exact he
  have hVK := JankoTwoHigmanSims.plane_le_component c
  let W := (V.subgroupOf K).map f.toMonoidHom
  let : IsElementaryAbelian 2 V := c.plane_elementary
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map f.toMonoidHom
  have hWcard : Nat.card W = 4 := by
    rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv, c.plane_card]
  have hWne : W ≠ ⊥ := by
    intro h
    simp [h] at hWcard
  have hWP : W ≤ localP := by
    rw [← hfS]
    exact map_mono (fun _ hx => c.plane_le_sylow hx)
  have hnormal : localP ≤ normalizer (W : Set Model) := by
    rw [← hfS]
    apply le_trans (map_mono ?_) ((V.subgroupOf K).le_normalizer_map f.toMonoidHom)
    rw [← subgroupOf_normalizer_eq hVK]
    exact fun _ hx => ((normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal)
      (c.sylow_le_local hx)
  obtain ⟨i, hi⟩ := elementaryCatalogue W hWne hWP hnormal inferInstance
  exact ⟨f, i, hfS, hi, hi ▸ hWcard⟩

private theorem characteristic_image_fixed
    (hchar : ((elementary 2).subgroupOf localP).Characteristic)
    (α : MulAut Model) (hP : localP.map α.toMonoidHom = localP) :
    (elementary 2).map α.toMonoidHom = elementary 2 := by
  let φ : MulAut localP := (α.subgroupMap localP).trans (MulEquiv.subgroupCongr hP)
  have hh := congrArg (Subgroup.map localP.subtype) (characteristic_iff_map_eq.mp hchar φ)
  have hcomp : localP.subtype.comp φ.toMonoidHom = α.toMonoidHom.comp localP.subtype := rfl
  rw [map_map, hcomp, ← map_map, map_subgroupOf_eq_of_le (elementary_le_localP 2)] at hh
  exact hh

end RudvalisLocalAction

variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

/-- Exact remaining Rudvalis inputs for the source rank-one obstruction.
All five premises refer to the same fixed subgroups on the actual carrier.
The characteristic premise is intrinsic to `localP`; the proof transports
it through the actual ambient conjugation action. These model premises must
be discharged before claiming the unconditional sporadic source branch. -/
theorem LocalConfiguration.not_rudvalis_of_fixed_subgroup_calculations
    (c : LocalConfiguration K S M Y V) (e : K ≃* Model)
    (hfour : ∀ i : Fin 6, Nat.card (elementary i) = 4 → i = 1)
    (hchar : ((elementary 2).subgroupOf localP).Characteristic)
    (hcentral : IsPGroup 2 (centralizer (elementary 2 : Set Model)))
    (henlarge : max4 ≤ normalizer (elementary 2 : Set Model))
    (hmove : ¬ max4 ≤ normalizer (elementary 1 : Set Model)) : False := by
  let : K.Normal := c.normal
  obtain ⟨f, i, hS, hV, hcard⟩ := RudvalisLocalAction.exists_plane_marking c e
  have hi := hfour i hcard
  subst i
  let Q : Subgroup K := (elementary 2).map f.symm.toMonoidHom
  have hQ : Q.map f.toMonoidHom = elementary 2 := by simp [Q, map_map]
  have hq : IsPGroup 2 Q :=
    (IntrinsicSylow.localP_isPGroup.to_le (elementary_le_localP 2)).map f.symm.toMonoidHom
  have hc : IsPGroup 2 (centralizer (Q : Set K)) := by
    have hm : (centralizer (Q : Set K)).map f.toMonoidHom ≤
        centralizer (elementary 2 : Set Model) := by
      rw [← hQ]
      exact map_centralizer_le_centralizer_image (Q : Set K) f.toMonoidHom
    exact (hcentral.to_le hm).of_equiv (f.subgroupMap (centralizer (Q : Set K))).symm
  have hnQ : (normalizer (Q : Set K)).map f.toMonoidHom =
      normalizer (elementary 2 : Set Model) := by rw [map_equiv_normalizer_eq, hQ]
  have hnV : (normalizer (V.subgroupOf K : Set K)).map f.toMonoidHom =
      normalizer (elementary 1 : Set Model) := by rw [map_equiv_normalizer_eq, hV]
  have hcover : normalizer (V.subgroupOf K : Set K) ≤ normalizer (Q : Set K) := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hnV, hnQ]
    exact (max4NormalizerBounds 1 (by decide) (by decide)).trans henlarge
  have hbad : ¬ normalizer (Q : Set K) ≤ normalizer (V.subgroupOf K : Set K) := by
    intro h
    apply hmove
    have hm := map_mono (f := f.toMonoidHom) h
    rw [hnQ, hnV] at hm
    exact henlarge.trans hm
  apply JankoTwoHigmanSims.component_normalizer_contradiction c Q hq hc ?_ hcover (Or.inr hbad)
  intro s hs
  let β : MulAut K := MulAut.conjNormal s
  let α : MulAut Model := MulAut.congr f β
  have hSβ : (S.subgroupOf K).map β.toMonoidHom = S.subgroupOf K := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨t, ht, rfl⟩
      change s * (t : G) * s⁻¹ ∈ S
      exact S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)
    · exact (Nat.card_congr (β.subgroupMap (S.subgroupOf K)).toEquiv).le
  have hcomp : α.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp β.toMonoidHom := by
    ext x
    simp [α]
  have hP : localP.map α.toMonoidHom = localP := by
    rw [← hS, map_map, hcomp, ← map_map, hSβ]
  have hfixed := RudvalisLocalAction.characteristic_image_fixed hchar α hP
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [map_map, ← hcomp, ← map_map, hQ, hfixed]

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
