module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.Seed
public import Theory.Mathieu.M11.Properties.OuterRestriction
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.SemidihedralNormalElementary
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.Quasithin.EvenCharacteristic

/-!
# Exclusion of M₁₁ from the rank-two configuration

An SD₁₆ Sylow subgroup has just one nontrivial normal elementary subgroup,
its central involution line. Every Sylow-containing maximal two-local is
therefore an involution centralizer and has order 48. The source shadow
forces divisibility by 36, a contradiction. The already proved innerness
of every automorphism discharges all possible component extensions.

Source: Aschbacher--Smith, 15.3.41--42, printed p.1138; GLS3 Table 5.3a.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion

private theorem m11_sylow_generators (T : Sylow 2 M11) :
    ∃ a b : T, orderOf a = 8 ∧ orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ 3 ∧ closure ({a, b} : Set T) = ⊤ := by
  obtain ⟨U, a, b, ha, hb, hc, hg⟩ := m11_exists_semidihedral_sylow
  let e := U.equiv T
  refine ⟨e a, e b, (e.orderOf_eq a).trans ha, (e.orderOf_eq b).trans hb, ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, hc, map_pow]
  · have hh := congrArg (Subgroup.map e.toMonoidHom) hg
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hh
    convert hh using 1
    rfl

private theorem m11_maximalLocal_centralizer (T : Sylow 2 M11) {N : Subgroup M11}
    (hN : IsMaximalTwoLocal N) (hTN : (T : Subgroup M11) ≤ N) :
    ∃ z : M11, orderOf z = 2 ∧ N = centralizer ({z} : Set M11) := by
  obtain ⟨a, b, ha, hb, hc, hg⟩ := m11_sylow_generators T
  obtain ⟨R, hR, hn, he, hNR⟩ :=
    exists_normal_elementary_normalizer_of_sylow_le T hN hTN
  let : R.Normal := hn
  let : IsElementaryAbelian 2 R := he
  rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg R hR,
    MonoidHom.map_zpowers] at hNR
  have hz : orderOf (((a ^ 4 : T) : M11)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_pow, ha]
    norm_num
  refine ⟨((a ^ 4 : T) : M11), hz, ?_⟩
  change N = normalizer (zpowers (((a ^ 4 : T) : M11)) : Set M11) at hNR
  rwa [normalizer_zpowers_eq_centralizer_of_order_two _ hz] at hNR

private theorem m11_centralizer_card (z : M11) (hz : orderOf z = 2) :
    Nat.card (centralizer ({z} : Set M11)) = 48 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (m11_involution_isConj_generatorA z hz)
  let f : M11 ≃* M11 := MulAut.conj g
  have hfz : f z = m11GeneratorAInM11 := hg
  have hc : Nat.card (centralizer ({z} : Set M11)) = Nat.card m11InvolutionCentralizer := by
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    change a ∈ centralizer ({z} : Set M11) ↔
      f a ∈ centralizer ({m11GeneratorAInM11} : Set M11)
    simp only [mem_centralizer_singleton_iff, ← hfz, ← map_mul, f.injective.eq_iff]
  exact hc.trans m11_involutionCentralizer_card

/-- No actual M₁₁ ambient model has the full rank-two local configuration. -/
theorem m11_no_localConfiguration {H : Type*} [Group H] [Finite H]
    (e : H ≃* M11) (K N Y S : Subgroup H) (d : LocalConfiguration K N Y S) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  obtain ⟨J, hNJ, hJ⟩ := Finite.exists_le_maximal d.twoLocal
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTJ : (T : Subgroup M11) ≤ J.map e.toMonoidHom :=
    map_mono ((hP.symm ▸ d.sylow_le).trans hNJ)
  obtain ⟨z, hz, hJz⟩ := m11_maximalLocal_centralizer T
    (Theory.Quasithin.isMaximalTwoLocal_map e hJ) hTJ
  have hc : Nat.card J = 48 := by
    calc
      Nat.card J = Nat.card (J.map e.toMonoidHom) :=
        Nat.card_congr (e.subgroupMap J).toEquiv
      _ = 48 := by rw [hJz]; exact m11_centralizer_card z hz
  have hd := (shadow_local_order_bounds P N Y S hP d.sylow_le
    (d.yplus_le.trans inf_le_left) d.shadow).1
  have hdJ := hd.trans (card_dvd_of_le hNJ)
  rw [hc] at hdJ
  norm_num at hdJ

/-- M₁₁ and all its possible component actions are excluded. -/
theorem not_m11 {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* M11) : False := by
  have hi : Function.Surjective (MulAut.conj : M11 →* MulAut M11) :=
    fun a => m11_automorphism_inner a
  exact m11_no_localConfiguration (wholeModelOfInner d e hi) _ _ _ _ d.quotient_local

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
