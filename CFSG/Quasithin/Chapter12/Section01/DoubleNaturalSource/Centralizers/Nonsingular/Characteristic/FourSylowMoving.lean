module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.ModelReduction
public import Theory.GroupTheory.NormalSylowElementaryBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.NormalElementaryBound

/-!
# The moving subgroup is normal in a component Sylow subgroup

In degree four the corrected point Sylow is an ambient point-centralizer
Sylow. Restrict it to the actual normal ordinary component, keeping the
original intersection, and then apply the literal central quotient map.
The moving subgroup has order64 and is normal in this Sylow; its map
through the center is injective by the proved residual fixed-space bound.
The native J₂ bound of four on normal elementary Sylow subgroups excludes
that component quotient. `FourModels` consumes the exclusion.

Source: Aschbacher--Smith, 12.1.1, printed p.788; GLS3 Table5.3g.
The remaining component and ambient branches stay with
qt-d-double-natural-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The moving subgroup in degree four is normal in an actual component Sylow subgroup. -/
theorem doubleNatural_four_adapted_component_moving_normalSylow
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        let U := (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K
        ∃ P : Sylow 2 K, U ≤ (P : Subgroup K) ∧
          (U.subgroupOf (P : Subgroup K)).Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 64 ∧
          Function.Injective ((QuotientGroup.mk' (center K)).comp U.subtype) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK
  let H := B.pointCentralizer w
  let R := B.pointResidual w
  let W := componentOrbit V (T : Subgroup G)
  let U := ⁅W,R⁆
  have hUK : U ≤ K := (D.doubleNatural_moving_le_residual h B w).trans
    (D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK).1
  have hUW : U ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (B.pointResidual_normalizes_orbit w)
  have hUP : U ≤ B.pointSylow w := hUW.trans
    (le_inf (D.doubledOrbit_E322 h).le_sylow (B.orbit_le_pointCentralizer w))
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hPN : B.pointSylow w ≤ normalizer (U : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change U.map (MulAut.conj t).toMonoidHom = U
    dsimp only [U]
    rw [map_commutator]
    have hWN : B.pointSylow w ≤ normalizer (W : Set G) := by
      apply le_trans (hPM.trans inf_le_left)
      change normalizer (L : Set G) ≤ normalizer (componentOrbit V (T : Subgroup G) : Set G)
      rw [B.orbit_eq]
      exact le_normalizer_componentOrbit _ _
    have heW : W.map (MulAut.conj t).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hWN ht)
    have heR : R.map (MulAut.conj t).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp ((hPM.trans (B.localPointCentralizer_normalizes_residual w)) ht)
    rw [heW,heR]
  let K₀ := K.subgroupOf H
  let : K₀.Normal :=
    (D.doubleNatural_adapted_ordinary_component_contains_residual h B S w hw K hK).2
  obtain ⟨P₀,hP₀⟩ := D.doubleNatural_four_adapted_ambientSylow h B S w hw
  obtain ⟨P₁,hP₁⟩ := P₀.exists_sylow_map_eq_inf_of_normal K₀
  let eK := subgroupOfEquivOfLe hK.1
  let P := P₁.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hP : (P : Subgroup K).map K.subtype = B.pointSylow w ⊓ K := by
    change ((P₁ : Subgroup K₀).map eK.toMonoidHom).map K.subtype = _
    rw [map_map]
    have he : K.subtype.comp eK.toMonoidHom = H.subtype.comp K₀.subtype := rfl
    rw [he,←map_map,hP₁,map_inf _ _ _ H.subtype_injective,hP₀,
      map_subgroupOf_eq_of_le hK.1]
  have hUle : U.subgroupOf K ≤ (P : Subgroup K) := by
    intro u hu
    have hh : (u : G) ∈ (P : Subgroup K).map K.subtype := hP.symm ▸ ⟨hUP hu,hUK hu⟩
    obtain ⟨v,hv,he⟩ := hh
    exact (Subtype.ext he : v = u) ▸ hv
  have hnormal : ((U.subgroupOf K).subgroupOf (P : Subgroup K)).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hUle).mpr
    rw [←subgroupOf_normalizer_eq hUK]
    intro p hp
    have hh : (p : G) ∈ B.pointSylow w ⊓ K := hP ▸ mem_map_of_mem K.subtype hp
    exact hPN hh.1
  let i : U.subgroupOf K →* W :=
    (inclusion hUW).comp (subgroupOfEquivOfLe hUK).toMonoidHom
  have hele : IsElementaryAbelian 2 (U.subgroupOf K) := IsElementaryAbelian.of_injective i
    ((inclusion_injective hUW).comp (subgroupOfEquivOfLe hUK).injective)
  refine ⟨P,hUle,hnormal,hele,?_,?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv]
    exact S.nonsingular_moving_card w hw.nonsingular
  · let f := (QuotientGroup.mk' (center K)).comp (U.subgroupOf K).subtype
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro u hu
    apply Subtype.ext
    apply Subtype.ext
    have hz : (u : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp hu
    have hc : ((u : K) : G) ∈ centralizer (K : Set G) := by
      intro k hk
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k,hk⟩)
    exact mem_bot.mp ((D.doubleNatural_adapted_component_moving_centralizer h B S w hw K hK) ▸
      (show ((u : K) : G) ∈ U ⊓ centralizer (K : Set G) from ⟨u.property,hc⟩))

/-- The Hall--Janko normal-Sylow bound excludes its literal central quotient. -/
theorem doubleNatural_four_adapted_component_not_jankoTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ∀ K : Subgroup G, IsComponentIn K (B.pointCentralizer w) →
        ¬ Nonempty ((K ⧸ center K) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  let := D.doubledOrbit_elementary h
  intro S w hw K hK ⟨e⟩
  obtain ⟨P,hUP,hn,he,hcard,hi⟩ := D.doubleNatural_four_adapted_component_moving_normalSylow h B S w hw K hK
  let U := (⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  have hb := NormalSylowElementary.bound_surjective (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) 4
    (NormalSylowElementary.bound_equiv e 4
      Sporadic.LeechRelated.J2.sylow_normal_elementary_card_le_four)
    P U hUP hn hi
  rw [hcard] at hb
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
