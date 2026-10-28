module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Extensions
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import BenderSuzuki.External.Huppert.II.theorem_6_14


/-!
# The original binary triality parabolic

The outer group of the genuine triality carrier at two has odd order. Thus
its faithful component extension by the source Sylow subgroup is the component
itself. The original normal four-group puts the whole local subgroup inside a
root parabolic. Minimality of the original outside subgroup forces equality.
Sylow conjugacy inside that same parabolic supplies simultaneous markings of
the local subgroup and the source Sylow.

The arms parabolic contains PSL₂(8), whose order has a factor nine. This
contradicts the actual three-residual's two-core index three, leaving only the
central node for the separate centralizer computation.

Source: Aschbacher--Smith, 15.3.43(a)--(e) and the binary paragraph, printed
pp.1139--1140; triality root geometry in F.1.11--12, pp.262--264.
-/

public section

open Subgroup
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource.Triality
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
open BinaryInspection.LinearInspection

/-- Every three-subgroup of the actual local image has order dividing three. -/
theorem three_subgroup_card_dvd_three (hs : IsSimpleGroup L)
    (A : Subgroup c.toComponentAction.Quotient) (hA : IsPGroup 3 A)
    (hAM : A ≤ c.toComponentAction.image M) : Nat.card A ∣ 3 := by
  let d := c.toComponentAction
  have hAY : A ≤ d.image Yplus := by
    intro x hx
    obtain ⟨n, hn⟩ := hA (⟨x, hx⟩ : A)
    rw [c.quotient.residual]
    exact mem_map.mpr ⟨⟨x, hAM hx⟩,
      mem_primePowerGenerated_of_pow (Subtype.ext (congrArg (fun a : A => (a : d.Quotient)) hn)), rfl⟩
  have hd := card_dvd_of_le hAY
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := d.image Yplus)).exists_card_eq
  have hc : Nat.card (d.image Yplus) = 2 ^ k * 3 := by
    rw [← (pCore 2 (d.image Yplus)).card_mul_index, hk, quotient_actor_index c hs]
  rw [hc] at hd
  obtain ⟨j, hj⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (2 ^ k) := by
    rw [hj]
    exact ((by decide : Nat.Coprime 3 2).pow_left j).pow_right k
  exact hcop.dvd_mul_left.mp hd

private theorem arms_card : Nat.card (levi (binaryParameters 1 Nat.zero_lt_one) .arms) = 504 := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let : CharP (ExtensionField P) 2 := inferInstanceAs (CharP (ExtensionField P) P.prime)
  rw [Nat.card_congr (leviArmsEquivPSL2 P rfl).toEquiv,
    ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    card_extensionField]
  norm_num [P, Parameters.q, binaryParameters]

/-- The arms Levi has a nine-divisible order, contradicting the source index. -/
theorem not_arms_parabolic (hs : IsSimpleGroup L)
    (e : c.toComponentAction.Quotient ≃* BinaryCarrier 1 Nat.zero_lt_one)
    (he : (c.toComponentAction.image M).map e.toMonoidHom =
      parabolic (binaryParameters 1 Nat.zero_lt_one) .arms) : False := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let T : Sylow 3 (levi P .arms) := default
  let f := e.symm.toMonoidHom.comp (levi P .arms).subtype
  have hf : Function.Injective f := e.symm.injective.comp (levi P .arms).subtype_injective
  let A := (T : Subgroup (levi P .arms)).map f
  have hAM : A ≤ c.toComponentAction.image M := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : (x : Carrier P) ∈ (c.toComponentAction.image M).map e.toMonoidHom := by
      rw [he]
      exact levi_le_parabolic P .arms x.property
    obtain ⟨y, hy, hyx⟩ := hxP
    change e.symm (x : Carrier P) ∈ _
    rw [← hyx]
    change e.symm (e y) ∈ c.toComponentAction.image M
    rw [e.symm_apply_apply]
    exact hy
  have hdiv := three_subgroup_card_dvd_three c hs A (T.isPGroup'.map f) hAM
  have h9 : 9 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (n := 2)
    (by rw [show Nat.card (levi P .arms) = 504 from arms_card]; decide)
  have hc : Nat.card A = Nat.card T := card_map_of_injective hf
  rw [hc] at hdiv
  exact (by decide : ¬ 9 ∣ 3) (h9.trans hdiv)

/-- The actual faithful quotient has no outer two-extension at field order two. -/
theorem quotient_component_eq_top (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) :
    c.toComponentAction.image L = ⊤ := by
  let d := c.toComponentAction
  let h := SporadicModels.localConfiguration_of_reduced c
  obtain ⟨e⟩ := (isTrialityGroupAt_two_iff L).mp iso
  let f := (BinaryInspection.subgroupImageEquiv c (component_center_eq_bot c hs) L le_rfl).symm.trans e
  obtain ⟨P, hP⟩ := h.sylow
  have htwo := isPGroup_quotient_of_sup_eq_top (d.image L) (d.image S)
    (hP ▸ P.isPGroup') h.generated
  exact ParabolicOuterTwo.normalExtension_eq_top_at_two (d.image L) f h.faithful htwo

/-- Identify the whole actual quotient with the genuine binary triality carrier. -/
theorem exists_quotient_equiv (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) :
    Nonempty (c.toComponentAction.Quotient ≃* BinaryCarrier 1 Nat.zero_lt_one) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_two_iff L).mp iso
  let f := (BinaryInspection.subgroupImageEquiv c (component_center_eq_bot c hs) L le_rfl).symm.trans e
  exact ⟨topEquiv.symm.trans ((MulEquiv.subgroupCongr
    (quotient_component_eq_top c hs iso).symm).trans f)⟩

/-- The original normal four-group and minimality give a full root parabolic. -/
theorem exists_quotient_parabolic (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) :
    ∃ e : c.toComponentAction.Quotient ≃* BinaryCarrier 1 Nat.zero_lt_one,
      ∃ a : Node, (c.toComponentAction.image M).map e.toMonoidHom =
        parabolic (binaryParameters 1 Nat.zero_lt_one) a := by
  let d := c.toComponentAction
  let h := SporadicModels.localConfiguration_of_reduced c
  obtain ⟨f⟩ := exists_quotient_equiv c hs iso
  let R := (d.image V₂).map f.toMonoidHom
  have hR : R ≠ ⊥ := by
    intro hh
    have hc : Nat.card R = 4 := (card_map_of_injective f.injective).trans h.plane_card
    rw [hh, card_bot] at hc
    omega
  let : IsElementaryAbelian 2 (d.image V₂) := h.plane_elementary
  have hp : IsPGroup 2 R := (IsElementaryAbelian.isPGroup 2 (d.image V₂)).map f.toMonoidHom
  obtain ⟨g, a, hg⟩ := TwoLocalCover.normalizer_cover 1 Nat.zero_lt_one R hR hp
  let e := f.trans (MulAut.conj g)
  have hM : (d.image M).map e.toMonoidHom ≤ parabolic (binaryParameters 1 Nat.zero_lt_one) a := by
    change (d.image M).map ((MulAut.conj g).toMonoidHom.comp f.toMonoidHom) ≤ _
    rw [← map_map]
    apply le_trans (map_mono ?_) hg
    rw [← map_equiv_normalizer_eq]
    exact map_mono ((normal_subgroupOf_iff_le_normalizer h.plane_le_local).mp h.plane_normal)
  refine ⟨e, a, le_antisymm hM ?_⟩
  let Q := (parabolic (binaryParameters 1 Nat.zero_lt_one) a).comap e.toMonoidHom
  have hQ : Q ≠ ⊤ := by
    intro hh
    have he := congrArg (map e.toMonoidHom) hh
    rw [map_comap_eq_self_of_surjective e.surjective, map_top_of_surjective _ e.surjective] at he
    exact parabolic_ne_top_binary _ rfl a he
  have hMQ : d.image M ≤ Q := map_le_iff_le_comap.mp hM
  have hYQ : d.image Yplus ⊔ d.image S ≤ Q := sup_le
    ((map_mono (comap_mono ((actor_le_local c).trans inf_le_left))).trans hMQ)
    (h.sylow_le_local.trans hMQ)
  have hle := quotient_proper_overgroup_le c Q hYQ hQ
  have hm := map_mono (f := e.toMonoidHom) hle
  rwa [map_comap_eq_self_of_surjective e.surjective] at hm

/-- Mark the local parabolic and its original Sylow simultaneously. -/
theorem exists_marked_quotient_parabolic (hs : IsSimpleGroup L) (iso : IsTrialityGroupAt 2 L) :
    ∃ e : c.toComponentAction.Quotient ≃* BinaryCarrier 1 Nat.zero_lt_one,
      ∃ a : Node, (c.toComponentAction.image M).map e.toMonoidHom =
        parabolic (binaryParameters 1 Nat.zero_lt_one) a ∧
      (c.toComponentAction.image S).map e.toMonoidHom =
        unipotent (binaryParameters 1 Nat.zero_lt_one) := by
  let d := c.toComponentAction
  let h := SporadicModels.localConfiguration_of_reduced c
  let P := binaryParameters 1 Nat.zero_lt_one
  obtain ⟨f, a, hM⟩ := exists_quotient_parabolic c hs iso
  obtain ⟨T, hT⟩ := h.sylow
  let U := T.mapSurjective (f := f.toMonoidHom) f.surjective
  let U₀ := unipotentSylow P rfl
  have hU : (U : Subgroup (Carrier P)) = (d.image S).map f.toMonoidHom := by
    change (T : Subgroup d.Quotient).map f.toMonoidHom = _
    rw [hT]
  have hUP : (U : Subgroup (Carrier P)) ≤ parabolic P a := by
    rw [hU, ← hM]
    exact map_mono h.sylow_le_local
  have hU₀P : (U₀ : Subgroup (Carrier P)) ≤ parabolic P a :=
    (unipotent_le_borel P).trans (borel_le_parabolic P a)
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq (parabolic P a)
    (U.subtype hUP) (U₀.subtype hU₀P)
  have hpU : (p : Carrier P) • U = U₀ := by
    apply Sylow.subtype_injective (N := parabolic P a)
    exact (Sylow.smul_subtype hUP p).symm.trans hp
  have hmap : (U : Subgroup (Carrier P)).map (MulAut.conj (p : Carrier P)).toMonoidHom =
      unipotent P := congrArg Sylow.toSubgroup hpU
  refine ⟨f.trans (MulAut.conj (p : Carrier P)), a, ?_, ?_⟩
  · change (d.image M).map ((MulAut.conj (p : Carrier P)).toMonoidHom.comp f.toMonoidHom) = _
    rw [← map_map, hM]
    exact mem_normalizer_iff_map_conj_eq.mp ((parabolic P a).le_normalizer p.property)
  · change (d.image S).map ((MulAut.conj (p : Carrier P)).toMonoidHom.comp f.toMonoidHom) = _
    rw [← map_map, ← hU]
    exact hmap

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.OriginalSource.Triality
