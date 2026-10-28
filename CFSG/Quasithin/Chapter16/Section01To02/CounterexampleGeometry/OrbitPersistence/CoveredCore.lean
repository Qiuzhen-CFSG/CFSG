module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.PersistenceReduction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Persistence for involutions in a covered Suzuki component's two-core

The full outer automorphism group of the concrete Sz(8) model has odd
order. Faithfulness of automorphisms of a perfect group on its central
quotient lifts innerness of two-elements to L. Thus N_T(L) centralizes
Z(L) = O₂(L), and the orbit's index-two calculation gives 16.2.6(2)
through the earlier small-centralizer-index transfer.

This also constructs an involution of the embedded nontrivial two-core.
No Schur multiplier calculation or model order formula is needed here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
p.1174, Lemma 16.2.6(2). Its transfer prerequisite remains with §16.1.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
universe v
variable {G : Type v} [Group G] [Finite G]
variable {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G} {K : GroupClass.{v}}

private theorem inner_of_two_power_of_odd_outer {B : Type*} [Group B] [Finite B]
    (hodd : Odd (MulAut.conj : B →* MulAut B).range.index)
    (a : MulAut B) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ b : B, a = MulAut.conj b := by
  let I := (MulAut.conj : B →* MulAut B).range
  have hcard : Odd (Nat.card (MulAut B ⧸ I)) := hodd
  have hpow : (QuotientGroup.mk' I a) ^ (2 ^ n) = 1 := by
    rw [← map_pow, ha, map_one]
  have heq : QuotientGroup.mk' I a = 1 :=
    (hcard.coprime_two_right.pow_right n).pow_left_bijective.injective (by simpa using hpow)
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff a).mp heq
  exact ⟨b, hb.symm⟩

/-- A nontrivial two-core contains an actual ambient involution. -/
theorem exists_embedded_core_involution (hne : pCore 2 L ≠ ⊥) :
    ∃ s : G, s ∈ (pCore 2 L).map L.subtype ∧ orderOf s = 2 := by
  let : Nontrivial (pCore 2 L) := (nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨x, hx⟩ := exists_ne (1 : pCore 2 L)
  have hd : 2 ∣ Nat.card (pCore 2 L) :=
    (pCore_isPGroup.dvd_orderOf hx).trans (orderOf_dvd_natCard x)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 L) 2 hd
  exact ⟨s, ⟨s.val, s.property, rfl⟩, by simpa only [orderOf_coe] using hs⟩

namespace CounterexampleSetup
variable (c : CounterexampleSetup K T z L)
include c

/-- The actual Sz(8) quotient makes every two-element automorphism of L inner. -/
theorem coveredSuzuki_two_power_inner
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (a : MulAut L) (n : ℕ) (ha : a ^ (2 ^ n) = 1) :
    ∃ b : L, a = MulAut.conj b := by
  let := c.localSetup.component.quasisimple
  have he : Nonempty ((L ⧸ center L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) := by
    obtain ⟨e⟩ := iso
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (c.global.evenType.component_center_eq_twoCore c.localSetup.involution
        c.localSetup.component)).trans e⟩
  obtain ⟨e⟩ := he
  apply (MulAut.centralQuotientAction_inner_iff e a).mp
  apply inner_of_two_power_of_odd_outer
    (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index 1 (by decide)) _ n
  rw [← map_pow, ha, map_one]

/-- The embedded two-core centralizes the Sylow normalizer of the component. -/
theorem coveredSuzuki_core_centralizes_normalizer
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    (pCore 2 L).map L.subtype ≤
      centralizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) := by
  rintro s ⟨s, hs, rfl⟩
  have hsc : s ∈ center L := by
    rwa [c.global.evenType.component_center_eq_twoCore c.localSetup.involution
      c.localSetup.component]
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨n, hn⟩ := T.isPGroup' (⟨x, hx.1⟩ : T)
  have hn' : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  let a : MulAut L := L.normalizerMonoidHom ⟨x, hx.2⟩
  have ha : a ^ (2 ^ n) = 1 := by
    change (L.normalizerMonoidHom ⟨x, hx.2⟩) ^ (2 ^ n) = 1
    rw [← map_pow]
    have he : (⟨x, hx.2⟩ : normalizer (L : Set G)) ^ (2 ^ n) = 1 :=
      Subtype.ext hn'
    rw [he, map_one]
  obtain ⟨b, hb⟩ := c.coveredSuzuki_two_power_inner iso a n ha
  have hfix : a s = s := by
    rw [hb]
    change b * s * b⁻¹ = s
    rw [(mem_center_iff.mp hsc b), mul_inv_cancel_right]
  have hf : x * (s : G) * x⁻¹ = s := congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul.mp hf)

/-- Lemma 16.2.6(2), conditional only on the permitted small-index transfer.
All model automorphism facts are discharged for the concrete Sz(8) quotient. -/
theorem coveredSuzuki_core_persistence
    (o : TwoComponentOrbit T z L u)
    (transfer : SmallCentralizerIndexTransfer G)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    {s : G} (hs : s ∈ (pCore 2 L).map L.subtype) (hs2 : orderOf s = 2) :
    IsCentralizerComponent s L := by
  obtain ⟨s, hs, rfl⟩ := hs
  have hsC : (s : G) ∈ centralizer (L : Set G) := by
    have hsc : s ∈ center L := by
      rwa [c.global.evenType.component_center_eq_twoCore c.localSetup.involution
        c.localSetup.component]
    exact mem_centralizer_iff.mpr fun x hx =>
      congrArg Subtype.val (mem_center_iff.mp hsc (⟨x, hx⟩ : L))
  obtain ⟨S, hS⟩ := c.localSetup.exists_component_sylow
  have hsT : (s : G) ∈ T := by
    have hm := pCore_isPGroup.le_sylow_of_normal S hs
    rwa [hS] at hm
  apply c.localSetup.component_of_small_index_of_transfer transfer hs2 ⟨hsT, hsC⟩
  have hN : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ involutionCentralizer (s : G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (c.coveredSuzuki_core_centralizes_normalizer iso
        (mem_map_of_mem _ hs)) x hx)
  have hi := relIndex_le_of_le_left hN (show
    ((T : Subgroup G) ⊓ normalizer (L : Set G)).relIndex (T : Subgroup G) ≠ 0 from
    Subgroup.index_ne_zero_of_finite)
  rw [inf_relIndex_left, o.normalizer_index c.localSetup] at hi
  exact hi

/-- The seed component normalizes every component in the new centralizer.
Perfectness and the two-element orbit bound replace the residual argument. -/
theorem seed_normalizes_centralizer_components
    (a134 : ComponentPairExhaustion K G) (o : TwoComponentOrbit T z L u)
    {t : G} (ht : t ∈ involutionContainer z L u) (ht2 : orderOf t = 2)
    {J : Subgroup G} (hJ : IsCentralizerComponent t J) :
    L ≤ normalizer (J : Set G) := by
  let := c.localSetup.component.quasisimple
  apply perfect_le_component_normalizer a134
    (c.global.involution_centralizer_sqtk ht2).isKGroup _ hJ
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (o.container_le_centralizer c.localSetup ht) x hx)

end CounterexampleSetup
end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
