module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreLifts
public import Theory.GroupTheory.TwoPerfectNormalizerControl

/-!
# Ambient normalizer control for the selected three-core lifts

A nontrivial T-invariant two-perfect subgroup of an original local J whose
L-commutators lie in O₂(L) has full normalizer in M = N_G(L). Thus an actual
normal two-perfect lift in an escaping J cannot centralize L/O₂(L). When
it lies in M, the literal quotient action is nontrivial.

For the selected Heisenberg subgroup, lift its actual cubic center within
the same normal Y. This is a proper normal two-perfect cubic lift with
exactly O₂(Z) as the original star-map kernel. Its two-core is nontrivial,
and the ambient normalizer argument supplies the same L-commutator
obstruction. This proves the normalizer step, not the full 14.7.9 restriction.

Source: Aschbacher–Smith, 14.5.20, printed pp.1018–1019; 14.7.9 and
14.7.27, printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The source's full normalizer bound for T-invariant two-perfect subgroups
centralizing L modulo its intrinsic two-core. -/
theorem local_twoPerfect_core_commutator_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup G) (hXJ : X ≤ J) (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hc : ⁅L,X⁆ ≤ L.pCoreIn 2) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro A _ _ hA S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hA S hM
  apply normalizer_le_of_twoPerfect_core_commutator T L J (normalizer (L : Set G)) X
    (fun x hx => hJ.1.2 (Or.inr hx))
    (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ)
    hXJ hTX hp hne (InvariantFlag.localKernel_L_core_le_T L (h.sylow_normalizes structural)) hc
  intro N hN hLN
  exact Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
    show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
      from ⟨hN,hLN⟩)

/-- A nontrivial normal two-perfect lift in an escaping original local
cannot centralize L modulo O₂(L). No containment of the lift in M is needed. -/
theorem local_normal_twoPerfect_not_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y) (hne : Y ≠ ⊥) :
    ¬ ⁅L,Y.map J.subtype⁆ ≤ L.pCoreIn 2 := by
  intro hc
  have hJY : J ≤ normalizer (Y.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hn := local_twoPerfect_core_commutator_normalizer h structural J hJ
    (Y.map J.subtype) (map_subtype_le Y)
    (hp.of_surjective (J.subtype.subgroupMap Y) (J.subtype.subgroupMap_surjective Y))
    (fun he => hne ((Y.map_eq_bot_iff_of_injective J.subtype_injective).mp he))
    ((show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx)).trans hJY) hc
  exact hJ.2.2 (hJY.trans hn)

/-- If such a lift lies in M, its literal action on L/O₂(L) is nontrivial. -/
theorem local_normal_twoPerfect_quotient_action_nontrivial
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y) (hne : Y ≠ ⊥)
    (hM : Y.map J.subtype ≤ normalizer (L : Set G)) :
    ∃ x : Y.map J.subtype,
      normalizerQuotientAction L (pCore 2 L) (inclusion hM x) ≠ 1 := by
  by_contra hn
  push Not at hn
  exact local_normal_twoPerfect_not_core_commutator h structural J hJ Y hp hne
    (commutator_le_of_normalizerQuotientAction_eq_one L (Y.map J.subtype) (pCore 2 L) hM hn)

/-- The selected Heisenberg lift has a proper normal cubic-center lift,
with the full original star-map kernel and nontrivial ambient L-action. -/
theorem local_solvable_heisenberg_center_lift
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    ∃ Z : Subgroup J, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
      Z.map (QuotientGroup.mk' (pCore 2 J)) =
        ((center X).map X.subtype).map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Z.subtype).ker = pCore 2 Z ∧
      Nat.card (Z ⧸ pCore 2 Z) = 3 ∧
      Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
      pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map J.subtype⁆ ≤ L.pCoreIn 2 := by
  let P := pCore 3 (HStar J)
  let q := QuotientGroup.mk' (pCore 2 J)
  let : X.Characteristic := hX.characteristic
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let C := (center X).map X.subtype
  let D := C.map P.subtype
  let : D.Characteristic := inferInstance
  have hD : Nat.card D = 3 := by
    rw [card_map_of_injective P.subtype_injective,card_map_of_injective X.subtype_injective,
      IsExtraspecial.center_order_p 3 X]
  have hDY : D ≤ Y.map q := by
    rw [hm]
    exact map_mono (map_subtype_le (center X))
  obtain ⟨Z,hZY,hZp,hZm,hZN,hZQ,hZk,⟨eZ⟩⟩ := exists_three_lift_within_normal q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) Y D ⊤ hDY
    le_normalizer_of_normal (IsPGroup.of_card (n := 1) (by simpa using hD))
  have hZn : Z.Normal := normalizer_eq_top_iff.mp (top_unique (by simpa using hZN))
  let := hZn
  have hZne : Z ≠ ⊥ := by
    intro he
    have hd := hZm
    rw [he,Subgroup.map_bot] at hd
    rw [←hd,card_bot] at hD
    omega
  have hZYlt : Z < Y := lt_of_le_of_ne hZY (by
    intro he
    have hc : Nat.card (Y.map q) = 27 := by
      rw [hm,card_map_of_injective P.subtype_injective,Nat.card_congr e.toEquiv,
        HeisenbergPrime.card]
      decide
    rw [←he,hZm,hD] at hc
    omega)
  have hcore : pCore 2 Z ≠ ⊥ := by
    have hZJ : Z.map J.subtype ≤ J := map_subtype_le Z
    have hnJ : J ≤ normalizer (Z.map J.subtype : Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
        Z.le_normalizer_map J.subtype
    have hn := pCore_ne_bot_of_core_normalizes J (Z.map J.subtype) hZJ
      (F.localKernel_characteristicTwo h.source.simpleQTKE L _ J hJ)
      ((pCoreIn_le 2 J).trans hnJ)
      (fun he => hZne ((Z.map_eq_bot_iff_of_injective J.subtype_injective).mp he))
    intro he
    apply hn
    rw [←pCore_map_iso 2 (equivMapOfInjective Z J.subtype J.subtype_injective),he,Subgroup.map_bot]
  let eC : center X ≃* D :=
    (equivMapOfInjective (center X) X.subtype X.subtype_injective).trans
      (equivMapOfInjective C P.subtype P.subtype_injective)
  exact ⟨Z,hZYlt,hZn,hZp,hZm,hZk,(Nat.card_congr eZ.toEquiv).trans hD,
    ⟨eZ.trans eC.symm⟩,hcore,
    local_normal_twoPerfect_not_core_commutator h structural J hJ Z hZp hZne⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
