module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.SevenMaximal
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits

/-!
# Ordinary A₇ blocks lie in characteristic-normalizer control

The constructed maximal six-point preimage contains no χ-block. Applying
the independently owned C.1.28 outside-block implication within that actual
Sylow overgroup makes its intrinsic control the whole subgroup. Restriction
of characteristic-normalizer control and maximality then give C(G,T)=G
when G=KT. Restricting to KT proves that every ordinary A₇ block K lies in
C(G,T) without a generation assumption.

The only earlier-source parameter is the literal universal C.1.28
outside-block theorem (C.1.26–27 producer, owned by ChiProduct). No action,
module, normality, quotient, residual, or decomposition is an input.
Source: C.1.29, printed p.134.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.LocalC129
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}

/-- The C.1.28 source implication eliminates the actual maximal six-point
overgroup and forces full characteristic-normalizer control in an A₇ extension. -/
theorem alternating_seven_control_eq_top_of_c128_outside
    (outside : ∀ {A : Type u} [Group A] [Finite A], IsSQTK C A →
      generalizedFitting A = pCore 2 A → ∀ (S : Sylow 2 A) (N : Subgroup A),
      (S : Subgroup A).characteristicNormalizerClosure ≤ N → N ≠ ⊤ →
      ∃ L : Subgroup A, ¬L ≤ N ∧ IsChiBlockIn L ∧
        L = ⁅L, elementaryAbelianMaxJ (S : Subgroup A)⁆)
    (hG : IsSQTK C G) (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) {K : Subgroup G} (hK : IsBlock K)
    (ha : IsAlternatingBlock K 7) (hgen : K ⊔ (T : Subgroup G) = ⊤) :
    (T : Subgroup G).characteristicNormalizerClosure = ⊤ := by
  obtain ⟨H, hTH, hmax, hno, hout⟩ :=
    alternating_seven_six_point_obstruction hG.stronglyQuasithin T hK ha hgen
  let S := T.subtype hTH
  have hfH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le H
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
        ((pCore_isPGroup.le_sylow_of_normal T).trans hTH))
  have htop : (S : Subgroup H).characteristicNormalizerClosure = ⊤ := by
    by_contra hn
    obtain ⟨L, _, hL, _⟩ := outside (hG.subgroup H) hfH S
      (S : Subgroup H).characteristicNormalizerClosure le_rfl hn
    exact hno L hL
  have hHC : H ≤ (T : Subgroup G).characteristicNormalizerClosure := by
    have hh := map_characteristicNormalizerClosure_le H.subtype H.subtype_injective
      (S : Subgroup H)
    rw [htop, ← MonoidHom.range_eq_map, range_subtype] at hh
    simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hh
  exact hmax.lt_iff.mp (lt_of_le_not_ge hHC hout)

/-- Restriction to K T removes the generation assumption. Every ordinary
A₇ block lies in C(G,T), using only the independently proved C.1.28 source. -/
theorem alternating_seven_le_control_of_c128_outside
    (outside : ∀ {A : Type u} [Group A] [Finite A], IsSQTK C A →
      generalizedFitting A = pCore 2 A → ∀ (S : Sylow 2 A) (N : Subgroup A),
      (S : Subgroup A).characteristicNormalizerClosure ≤ N → N ≠ ⊤ →
      ∃ L : Subgroup A, ¬L ≤ N ∧ IsChiBlockIn L ∧
        L = ⁅L, elementaryAbelianMaxJ (S : Subgroup A)⁆)
    (hG : IsSQTK C G) (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) {K : Subgroup G} (hK : IsBlock K)
    (ha : IsAlternatingBlock K 7) :
    K ≤ (T : Subgroup G).characteristicNormalizerClosure := by
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  let S := T.subtype hTH
  let B := K.subgroupOf H
  let e : K ≃* B := (subgroupOfEquivOfLe hKH).symm
  have hB : IsBlock B := ⟨inferInstance, RankOne.Solvable.isShort_of_equiv e hK.short,
    hK.subnormal.subgroupOf⟩
  have haB : IsAlternatingBlock B 7 := RankOne.Solvable.isAlternatingBlock_of_equiv e ha
  have hfH : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le H
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
        ((pCore_isPGroup.le_sylow_of_normal T).trans hTH))
  have hgen : B ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH, ← MonoidHom.range_eq_map, range_subtype]
  have htop := alternating_seven_control_eq_top_of_c128_outside outside
    (hG.subgroup H) hfH S hB haB hgen
  have hh := map_characteristicNormalizerClosure_le H.subtype H.subtype_injective
    (S : Subgroup H)
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at hh
  have hHC : H ≤ (T : Subgroup G).characteristicNormalizerClosure := by
    simpa only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hh
  exact hKH.trans hHC
end CFSG.Quasithin.ChapterC.LocalC129
