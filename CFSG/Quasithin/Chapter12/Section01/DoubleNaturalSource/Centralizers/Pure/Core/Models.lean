module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Identification
public import GorensteinWalter.PSL2Center

/-!
# The surviving component models at a pure point

The central involution just constructed excludes the centerless Lie and
odd-characteristic alternatives of 1.1.5 and both alternating alternatives,
whose possible centers have odd order. The surviving two-cover and sporadic
branches retain the literal quotient by O₂ and the original automorphism.

The final applications supply this reduction from the original chosen-module
hypotheses and connect it to the fusion, abelian-closure and intersection
conclusions in dimension five. The surviving models still need exclusion;
this module does not claim 12.1.6. Their exclusion and the dimension-four
ambient Sylow proof remain with `qt-d-double-natural-pure-fusion`.
Source: Aschbacher--Smith, 12.1.6, printed p.791, and 1.1.5(3), pp.501--503.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels

private theorem centerless_simple_perfect {K : Type*} [Group K]
    [IsSimpleGroup K] [Group.IsPerfect K] : center K = ⊥ := by
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp ht)).elim

private theorem centerless_psl {K : Type*} [Group K] {d q : ℕ}
    (hd : 2 ≤ d) (hm : ClassicalGroup.IsPSL K d q) : center K = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
  have hc : center PSL(d,F) = ⊥ := by
    by_cases h₂ : d = 2
    · subst d
      exact GorensteinWalter.psl2_center_eq_bot F
    · let := Atlas.sl_perfect (F := F) d (by omega)
      exact Group.IsPerfect.center_quotient_center_eq_bot SL(d,F)
  apply (center K).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  exact mem_bot.mp (hc ▸ (centerCongr e ⟨x,hx⟩).property)

private theorem no_alternating_of_central_involution {K : Type*} [Group K]
    {d : ℕ} (hd : 4 ≤ d) (a : MulAut K) (s : Equiv.Perm (Fin d))
    (ha : AlternatingAction a d s)
    (v : K) (hv : v ∈ center K) (hv2 : orderOf v = 2) : False := by
  rcases ha with ⟨e,_⟩ | ⟨_,⟨e⟩,_⟩
  · have hc := alternatingGroup.center_eq_bot (α := Fin d) (by simpa using hd)
    have he : e v = 1 := mem_bot.mp (hc ▸ (centerCongr e ⟨v,hv⟩).property)
    have hv1 : v = 1 := e.injective (he.trans (map_one e).symm)
    simp only [hv1, orderOf_one] at hv2
    omega
  · have hc : Nat.card (center K) = 3 := by
      rw [Nat.card_congr e.toEquiv]
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    have he : orderOf (⟨v,hv⟩ : center K) = 2 := by
      exact (orderOf_injective (center K).subtype (center K).subtype_injective ⟨v,hv⟩).symm.trans hv2
    have hh := orderOf_dvd_natCard (⟨v,hv⟩ : center K)
    rw [hc,he] at hh
    norm_num at hh

/-- A central involution excludes the centerless and odd-center branches of
1.1.5. The two-cover and sporadic alternatives retain their actual quotients. -/
theorem model115_of_central_involution {K : Type*} [Group K]
    [Group.IsPerfect K] (a : MulAut K) (hm : ModelAction115 K a)
    (v : K) (hv : v ∈ center K) (hv2 : orderOf v = 2) :
    (center K = pCore 2 K ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨ IsG2At (K ⧸ pCore 2 K) 4) ∧
      a ∈ (MulAut.conj (G := K)).range) ∨
    (∃ name : SporadicName, name ≠ .j3 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) ∧ TwoCentralInner a) := by
  have hn (hc : center K = ⊥) : False := by
    have he : v = 1 := mem_bot.mp (hc ▸ hv)
    simp only [he,orderOf_one] at hv2
    omega
  cases hm with
  | lie hs _ _ =>
    let := hs
    exact (hn centerless_simple_perfect).elim
  | two_cover _ hc hm hi => exact Or.inl ⟨hc,hm,hi⟩
  | six s _ ha => exact (no_alternating_of_central_involution (by decide) a s ha v hv hv2).elim
  | seven s _ ha => exact (no_alternating_of_central_involution (by decide) a s ha v hv hv2).elim
  | odd hm _ =>
    rcases hm with hm | ⟨p,_,hm⟩
    · exact (hn (centerless_psl (by decide) hm)).elim
    · exact (hn (centerless_psl (by decide) hm)).elim
  | sporadic name hj hm ha => exact Or.inr ⟨name,hj,hm,ha⟩

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual ordinary component contains the residual, is the whole layer,
and has a central involution. The exact quotient and action survive the
exclusion of the centerless and alternating branches of 1.1.5. -/
theorem doubleNatural_pure_component_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K →
      ∀ z : G, HasModelAction115 K z →
        K.Normal ∧ K = componentLayer (B.pointCentralizer w) ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧
        B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype ∧
        (B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⊓
          ((center K).map K.subtype).map (B.pointCentralizer w).subtype = zpowers (w : G) ∧
        center K = pCore 2 K ∧
        ∃ a : MulAut K, (∀ x : K, ((a x : B.pointCentralizer w) : G) = z * (x : G) * z⁻¹) ∧
          (((ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨ IsG2At (K ⧸ pCore 2 K) 4) ∧
              a ∈ (MulAut.conj (G := K)).range) ∨
            ∃ name : SporadicName, name ≠ .j3 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) ∧ TwoCentralInner a) := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix K hK z hz
  obtain ⟨hn,hX,hU⟩ :=
    D.doubleNatural_pure_component_identification_of_many h hmany B S hns hs w hw hp hfix K hK
  have hLayer : K = componentLayer (B.pointCentralizer w) := by
    apply le_antisymm (show K ≤ componentLayer (B.pointCentralizer w) from le_sSup hK)
    apply sSup_le
    intro J hJ
    have he := S.pure_component_eq_containing (D.doubledOrbit_normalizer_eq h B.orbit_eq)
      hns w hw hp (D.doubleNatural_pure_local_characteristicTwo_of_many h hmany B w hw)
      J K hJ hK.isCComponent hX
    exact he.le
  let := hK.2
  have hc : center K = pCore 2 K := IsQuasisimple.center_eq_pCore
    (hK.1.pPrimeCore_eq_bot (D.doubleNatural_pure_oddCore_eq_bot_of_many h hmany B S hns w hw hp) K)
  refine ⟨hn,hLayer,hX,hU,S.pure_moving_center_intersection w hw hp K hX hU,hc,?_⟩
  obtain ⟨v,_,hv,hv2⟩ := S.pure_component_central_point w hw hp K hU
  obtain ⟨a,ha,hm⟩ := hz
  refine ⟨a,ha,?_⟩
  rcases DoubledBranch.SourceModel.model115_of_central_involution a hm v hv hv2 with hm | hm
  · exact Or.inl hm.2
  · exact Or.inr hm

/-- The original point has characteristic two unless one of the remaining
two-cover or sporadic models contains the actual moved subgroup. -/
theorem doubleNatural_pure_characteristicTwo_or_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      S.MarkedAmbientSylow D.sylow_normalizes_component →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) ∨
      ∃ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K ∧
        K.Normal ∧ K = componentLayer (B.pointCentralizer w) ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧
        B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype ∧
        (B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⊓
          ((center K).map K.subtype).map (B.pointCentralizer w).subtype = zpowers (w : G) ∧
        center K = pCore 2 K ∧
        ∃ a : MulAut K, (∀ x : K, ((a x : B.pointCentralizer w) : G) = z * (x : G) * z⁻¹) ∧
          (((ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨ IsG2At (K ⧸ pCore 2 K) 4) ∧
              a ∈ (MulAut.conj (G := K)).range) ∨
            ∃ name : SporadicName, name ≠ .j3 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) ∧ TwoCentralInner a) := by
  let := D.doubledOrbit_elementary h
  intro S hns hs w hw hp hfix z hz hzT
  rcases D.doubleNatural_pure_component_alternative_of_many h hmany B S hns hs
      w hw hp hfix z hz hzT with hc | ⟨K,hK,_,_,hm⟩
  · exact Or.inl hc
  · exact Or.inr ⟨K,hK,D.doubleNatural_pure_component_models_of_many
      h hmany B S hns hs w hw hp hfix K hK z hm⟩

/-- Application to all three original conclusions in dimension five. The
earlier positive globalW premise supplies the ambient Sylow, leaving exactly
the displayed component models for this task's final assembly to exclude. -/
theorem doubleNatural_five_pure_conclusions_or_models_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 5)
    (hW : 0 < ChapterE.globalW (componentOrbit V (T : Subgroup G)) T) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, B.NonsingularCentralizers →
      ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ∀ z : G, orderOf z = 2 → z ∈ centerIn (T : Subgroup G) →
      (B.PureFusion ∧ B.PureCentralizerClosureAbelian ∧ B.PureIntersectionCentralizes) ∨
      ∃ K : Subgroup (B.pointCentralizer w), IsComponent (B.pointCentralizer w) K ∧
        K.Normal ∧ K = componentLayer (B.pointCentralizer w) ∧
        (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K ∧
        B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype ∧
        (B.naturalSummand ⊔ S.pureDualHyperplane w hp) ⊓
          ((center K).map K.subtype).map (B.pointCentralizer w).subtype = zpowers (w : G) ∧
        center K = pCore 2 K ∧
        ∃ a : MulAut K, (∀ x : K, ((a x : B.pointCentralizer w) : G) = z * (x : G) * z⁻¹) ∧
          (((ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨ IsG2At (K ⧸ pCore 2 K) 4) ∧
              a ∈ (MulAut.conj (G := K)).range) ∨
            ∃ name : SporadicName, name ≠ .j3 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier) ∧ TwoCentralInner a) := by
  let := D.doubledOrbit_elementary h
  intro S hns w hw hp hfix z hz hzT
  have hs : S.MarkedAmbientSylow D.sylow_normalizes_component := by
    intro v hv hpv hfixv
    exact (D.doubleNatural_five_marked_pure_sylow_of_many h hmany B hW S v hv hpv hfixv).2
  rcases D.doubleNatural_pure_characteristicTwo_or_models_of_many h hmany B S hns hs
      w hw hp hfix z hz hzT with hc | hm
  · exact Or.inl (D.doubleNatural_five_pure_conclusions_of_one_characteristicTwo_of_many
      h hmany B hW S hns w hw hp hc)
  · exact Or.inr hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
