module

public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.MarkedModel
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.ReplacementSource
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.OddCommutatorSource
public import Theory.Representation.QuadraticFourGroup.Recognition.NormalizerActors

/-!
# The replacement contradiction for a moving component

The actual quadratic model marks the original component. Any nonidentity
normalizing replacement element produces an odd commutator in its first
factor, and hence moves at least twice the field degree in the original
module. The normalizer rank bound contradicts the offender inequality.
The remaining orbit has order two, excluded by the order-two offender bound.

This proves GLS2, Theorem 26.24, Steps 2--5 and the final contradiction,
including its application when the component orbit generates the moved space.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentNormalization.ReplacementSource
open Representation.QuadraticFourGroup
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

lemma pair_orbit_of_replacement_eq (hf : Function.Injective ρ)
    {A L : Subgroup G} (hA : IsBestOffender ρ A) (hL : IsComponent G L)
    {a : G} (ha : a ∈ A) (haN : a ∉ normalizer (L : Set G))
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (heq : displacementCentralizer ρ A = A) (c : A) :
    L.map (MulAut.conj (c:G)).toMonoidHom = L ∨
      L.map (MulAut.conj (c:G)).toMonoidHom = L.map (MulAut.conj a).toMonoidHom := by
  classical
  by_cases hc1 : (c:G) = 1
  · left
    rw [hc1]
    convert L.map_id using 1
    ext x
    simp
  by_cases hca : (c:G) = a
  · exact Or.inr (hca ▸ rfl)
  have hc : (c:G) ∈ displacementCentralizer ρ A := heq.symm ▸ c.property
  obtain ⟨hBA,hBe,hcard,haB,hcB,hquad,hcentral⟩ :=
    displacement_pair_fourGroup ρ hA.1 ha haN hc hc1 hca hcent (Or.inl heq)
  let B := closure ({a,(c:G)} : Set G)
  let := hA.1.2
  have ha1 : a ≠ 1 := fun he => haN (he ▸ (normalizer (L : Set G)).one_mem)
  have h : Hypotheses ρ L B a := {
    faithful := hf
    component := hL
    elementary := hBe.2
    card_four := hcard
    mem := haB
    involution := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    moves := fun he => haN (mem_normalizer_iff_map_conj_eq.mpr he)
    quadratic := hquad
    centralizer := hcentral }
  obtain ⟨M⟩ := QuadraticSource.twoFactorModel h
  exact QuadraticSource.orbit_conjugate_cases h M ⟨c,hcB⟩

theorem normalizes_of_replacement_centralizer (hf : Function.Injective ρ)
    {A L : Subgroup G} (hA : IsBestOffender ρ A) (hL : IsComponent G L)
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (halt : displacementCentralizer ρ A = A ∨
      displacementCentralizer ρ A ≤ normalizer (L : Set G)) :
    A ≤ normalizer (L : Set G) := by
  classical
  by_contra hAN
  obtain ⟨a,ha,_,haN,_,_⟩ := exists_moving_component_involution hA.1 hL hAN
  obtain ⟨c₀,hc₀,hc₀1,hc₀a,B,hB,hBA,hq,_⟩ :=
    exists_classified_fourGroup.{u,v,v} ρ hf hA hL ha haN hcent halt
  obtain ⟨M,f,hfM,hk,hmark⟩ := QuadraticSource.exists_marked_model hq
  let C := displacementCentralizer ρ A
  have hC : IsBestOffender ρ C := hA.displacementCentralizer_isBestOffender ρ
  let := hC.1.2
  let := hL.2
  let e : L ⧸ center L ≃* Factor M.n :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfM)
  have hn : 2 ≤ M.n := by have := M.one_lt; omega
  have hcard : Nat.card C ≤ 2 ^ (M.n+1) := by
    rcases halt with he | hN
    · have horbit := pair_orbit_of_replacement_eq ρ hf hA hL ha haN hcent he
      have heC : C = A := he
      let := hA.1.2
      have hb := NormalizerActors.card_le_of_pair_orbit A L hn e
        (by simpa only [he] using hcent) ⟨a,ha⟩ horbit
      simpa only [heC] using hb
    · exact (NormalizerActors.card_le_of_normalizes C L hn e hcent hN).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_succ M.n))
  have hrank : rank C ≤ M.n+1 :=
    (Nat.log_le_clog 2 (Nat.card C)).trans (Nat.clog_le_of_le_pow hcard)
  have hCN : C ⊓ normalizer (L : Set G) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    rintro c ⟨hc,hcN⟩
    by_contra hc1
    have hcne : c ≠ 1 := by simpa only [mem_bot] using hc1
    obtain ⟨l,x,g,hg,ho,hgne,hx⟩ := NormalizerActors.twoFactor_odd_commutator
      C L (le_componentOrbit L B) M f hfM hk hmark hcent c hc hcN hcne
    have hb := OddCommutatorSource.two_mul_degree_le_fixedCodim hq M x g hg ho hgne c l hx
    have hm := NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr hc)
    have hcOff := (hC.isOffender ρ).2
    omega
  rcases halt with he | hN
  · have horbit := pair_orbit_of_replacement_eq ρ hf hA hL ha haN hcent he
    have heC : C = A := he
    have hNbot : (normalizer (L : Set G)).subgroupOf A = ⊥ := by
      rw [subgroupOf_eq_bot, disjoint_iff]
      simpa only [← heC, inf_comm] using hCN
    have hind := NormalizerActors.normalizer_index_dvd_two A L ⟨a,ha⟩ horbit
    rw [hNbot, index_bot] at hind
    have hcardA : Nat.card A = 2 := by
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hind
      have hgt := (one_lt_card_iff_ne_bot A).mpr hA.1.1
      omega
    exact haN ((hA.isOffender ρ).le_normalizer_component_of_card_two ρ hf hcardA hL ha)
  · have hCbot : C = ⊥ := (inf_eq_left.mpr hN).symm.trans hCN
    exact hC.1.1 hCbot

theorem normalizes_of_moved_space
    (hf : Function.Injective ρ) {A L : Subgroup G}
    (hA : IsBestOffender ρ A) (hL : IsComponent G L)
    (hmin : ∀ C ≤ A, IsBestOffender ρ C → C = A ∨ C ≤ normalizer (L : Set G))
    (hV : Submodule.span (ZMod 2)
      (Set.range fun ev : componentOrbit L A × V => ρ ev.1 ev.2 - ev.2) = ⊤) :
    A ≤ normalizer (L : Set G) := by
  classical
  by_contra hAN
  let := hA.1.2
  have hEA := (hL.orbit_properties A hAN).2.2
  have hcent := displacementCentralizer_inf_centralizer_orbit_eq_bot ρ A L hf hEA hV
  have halt := hmin (displacementCentralizer ρ A) (displacementCentralizer_le ρ A)
    (hA.displacementCentralizer_isBestOffender ρ)
  exact hAN (normalizes_of_replacement_centralizer ρ hf hA hL hcent halt)
end CFSG.Quasithin.ChapterB.ComponentNormalization.ReplacementSource
