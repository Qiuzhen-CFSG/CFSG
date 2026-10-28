module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Rudvalis.LocalAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Rudvalis.EvenNormalizer
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneRows
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightAction
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core
public import CFSG.Quasithin.MainConverse.Transport
/-!
# The Rudvalis rank-one local obstruction

The source four-group is carried onto `elementary 1` by the proved Sylow
catalogue and the order-four row selection. The marked eight-subgroup
`elementary 2` is characteristic in `localP` and normalized by max4, whereas
max4 moves the plane. Enlarging to its ambient normalizer contradicts
maximality. Characteristicity retains every allowed ambient Sylow action
on K, including possible outer actions.

The concrete Rudvalis even-characteristic theorem supplies characteristic
two of the inner normalizer. The component--Sylow quotient then supplies
characteristic two of the full ambient normalizer, by `EvenNormalizer`.
Thus the former separate premise on the centralizer of `elementary 2` is
unnecessary. The original five-premise reduction remains available through
`LocalAction`.

The terminal theorem `LocalConfiguration.not_rudvalis` supplies all three
concrete facts from their checked proofs on the original degree-4060 model.
Its only inputs are the source local configuration and an actual component
isomorphism with that model. The conditional reduction remains available.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the sporadic
paragraph of 15.3.43, printed p.1140; the exact list is 1.1.5(3)(f), p.502.
The original ATLAS words and their attribution are in
`Rudvalis.Model.SylowOvergroups.Definitions` and `LocalCover.Data`.
-/

public section
open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

/-- The Rudvalis source branch follows from the marked characteristic
subgroup and max4 action. The three model premises are discharged in
`LocalConfiguration.not_rudvalis` below. -/
theorem LocalConfiguration.not_rudvalis_of_eight_action
    (c : LocalConfiguration K S M Y V) (e : K ≃* Model)
    (hchar : ((elementary 2).subgroupOf localP).Characteristic)
    (henlarge : max4 ≤ normalizer (elementary 2 : Set Model))
    (hmove : ¬ max4 ≤ normalizer (elementary 1 : Set Model)) : False := by
  let : K.Normal := c.normal
  obtain ⟨f, i, hS, hV, hcard⟩ := RudvalisLocalAction.exists_plane_marking c e
  have hi := RankOneRows.index_eq_one_of_card_four i hcard
  subst i
  let Q : Subgroup K := (elementary 2).map f.symm.toMonoidHom
  let R : Subgroup G := Q.map K.subtype
  have hQ : Q.map f.toMonoidHom = elementary 2 := by simp [Q, map_map]
  have hq : IsPGroup 2 Q :=
    (IntrinsicSylow.localP_isPGroup.to_le (elementary_le_localP 2)).map f.symm.toMonoidHom
  have hRcard : Nat.card R = Nat.card (elementary 2) := by
    rw [card_map_of_injective K.subtype_injective, card_map_of_injective f.symm.injective]
  have hRne : R ≠ ⊥ := by
    intro hb
    have hh := RankOneRows.five_le_card_elementary_two
    rw [← hRcard, hb] at hh
    norm_num at hh
  have hnQ : (normalizer (Q : Set K)).map f.toMonoidHom =
      normalizer (elementary 2 : Set Model) := by rw [map_equiv_normalizer_eq, hQ]
  have hnV : (normalizer (V.subgroupOf K : Set K)).map f.toMonoidHom =
      normalizer (elementary 1 : Set Model) := by rw [map_equiv_normalizer_eq, hV]
  have hcover : normalizer (V.subgroupOf K : Set K) ≤ normalizer (Q : Set K) := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hnV, hnQ]
    exact (max4NormalizerBounds 1 (by decide) (by decide)).trans henlarge
  have hstable (s : G) (hs : s ∈ S) : Q.map (MulAut.conjNormal s).toMonoidHom = Q := by
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
    have hfixed : (elementary 2).map α.toMonoidHom = elementary 2 := by
      let φ : MulAut localP := (α.subgroupMap localP).trans (MulEquiv.subgroupCongr hP)
      have hh := congrArg (Subgroup.map localP.subtype) (characteristic_iff_map_eq.mp hchar φ)
      have hcomp' : localP.subtype.comp φ.toMonoidHom = α.toMonoidHom.comp localP.subtype := rfl
      rw [map_map, hcomp', ← map_map, map_subgroupOf_eq_of_le (elementary_le_localP 2)] at hh
      exact hh
    apply map_injective (f := f.toMonoidHom) f.injective
    rw [map_map, ← hcomp, ← map_map, hQ, hfixed]
  have hSN : S ≤ normalizer (R : Set G) := by
    apply le_normalizer_iff.mpr
    intro s hs r hr
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hr
    have hm := mem_map_of_mem (MulAut.conjNormal s).toMonoidHom hq
    rw [hstable s hs] at hm
    exact mem_map.mpr ⟨MulAut.conjNormal s q, hm, rfl⟩
  have hVK := JankoTwoHigmanSims.plane_le_component c
  have hVnormalizer : (normalizer (V : Set G)).subgroupOf K =
      normalizer (V.subgroupOf K : Set K) := subgroupOf_normalizer_eq hVK
  have hcover' : K ⊓ normalizer (V : Set G) ≤ normalizer (R : Set G) := by
    intro x hx
    have hv : (⟨x, hx.1⟩ : K) ∈ normalizer (V.subgroupOf K : Set K) := by
      rw [← hVnormalizer]
      exact hx.2
    exact Q.le_normalizer_map K.subtype (mem_map.mpr ⟨⟨x, hx.1⟩, hcover hv, rfl⟩)
  have hMV : M ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.plane_le_local).mp c.plane_normal
  have hMN : M ≤ normalizer (R : Set G) := by
    intro x hx
    have hgen : x ∈ K ⊔ S := c.generated.ge (mem_top x)
    obtain ⟨k, hk, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hgen
    have hkM : k ∈ M := by
      have hh := M.mul_mem hx (M.inv_mem (c.sylow_le_local hs))
      simpa only [mul_inv_cancel_right] using hh
    exact (normalizer (R : Set G)).mul_mem (hcover' ⟨hk, hMV hkM⟩) (hSN hs)
  have heven : IsEvenCharacteristic K := MainConverse.evenCharacteristic_of_model_equiv e
    (MainConverse.SporadicLocal.RuEven.evenCharacteristic_of_max6
      MainConverse.SporadicLocal.RuEven.max6_characteristicTwo)
  have he := RudvalisLocalAction.local_eq_normalizer_of_even c heven R
    (map_subtype_le Q) (hq.map K.subtype) hRne hMN
  have hNM : (normalizer (Q : Set K)).map K.subtype ≤ M :=
    he.symm ▸ Q.le_normalizer_map K.subtype
  have hn : normalizer (Q : Set K) ≤ normalizer (V.subgroupOf K : Set K) := by
    intro x hx
    rw [← hVnormalizer]
    exact hMV (hNM (mem_map.mpr ⟨x, hx, rfl⟩))
  apply hmove
  have hm := map_mono (f := f.toMonoidHom) hn
  rw [hnQ, hnV] at hm
  exact henlarge.trans hm

/-- The Rudvalis case of the sporadic inspection in 15.3.43 is impossible.
All marked subgroup calculations are proved on the actual Rudvalis carrier;
no restriction to inner ambient automorphisms is imposed. -/
theorem LocalConfiguration.not_rudvalis
    (c : LocalConfiguration K S M Y V) (e : K ≃* Model) : False :=
  c.not_rudvalis_of_eight_action e
    RankOneEightCharacteristic.elementary_two_characteristic
    RankOneEightAction.max4_le_normalizer_eight
    RankOneEightAction.max4_not_le_normalizer_plane

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
