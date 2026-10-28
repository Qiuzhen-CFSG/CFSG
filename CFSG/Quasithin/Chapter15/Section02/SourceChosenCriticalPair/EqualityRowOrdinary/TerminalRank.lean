module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary

/-!
# Full-rank marked ordinary components in the direct source route

The source residual forces three-rank two in the same marked fixed subgroup.
For PSL₃(3), A₆ and A₇, that fixed subgroup embeds in a group of order 48.
This proves the contradiction directly on the original component without
assuming the partner residual identity or a plane-uniqueness packet.

Source: Aschbacher--Smith 15.2.24 and the proof of 15.2.15, pp.1117--1118.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06 ChapterD.UniqueFactor
open OrdinaryComponents Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)

open scoped MatrixGroups

/-- The actual PSL₃(3) row contradicts the three-rank of its marked fixed subgroup. -/
theorem ResidualInput.ordinary_linear_three_false
    (hcard : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : ClassicalGroup.IsPSL c.component 3 3)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let eq := e.trans (Atlas.fieldEquivPSL 3 ef)
  have hc : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr (eq.trans Matrix.PSL3Three.equiv.symm) ⟨x,hx⟩).property
    change Matrix.PSL3Three.equiv.symm (eq x) ∈ center Matrix.PSL3Three.SL at hh
    have h1 := Matrix.PSL3Three.center_eq_bot.le hh
    exact (eq.trans Matrix.PSL3Three.equiv.symm).map_eq_one_iff.mp (mem_bot.mp h1)
  have hr : 2 ≤ primeRank 3 c.component := by
    rw [primeRank_congr 3 eq]
    exact Matrix.PSL3Three.primeRank_three_ge_two
  have ho := Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr eq).symm
  have hlow := r.fixed_three_rank_of_full_component_direct c hI hcard hz hzne hc hr ho a ha
  let b := MulAut.congr eq a
  have hb : orderOf b = 2 := (MulAut.congr eq).orderOf_eq a |>.trans
    (marked_component_action_order_two c (r.marked_centralizer_of_seed_card hcard hz hzne).1 hz hzne a ha)
  have hbi : ∃ x, b = MulAut.conj x := by
    apply (MulAut.congr_inner_iff eq a).mpr
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,hx.symm⟩
  let efix := (MulAut.fixedSubgroupCongr eq a).trans
    (Matrix.PSL3Three.innerInvolutoryAutFixedEquiv b hb hbi)
  have hcard : Nat.card a.fixedSubgroup = 48 := by
    rw [Nat.card_congr efix.toEquiv, Matrix.card_GL_field]
    decide
  have hu : primeRank 3 a.fixedSubgroup ≤ 1 :=
    primeRank_le_of_prime_pow_not_dvd (by rw [hcard]; decide)
  omega

omit r [Group G] [Finite G] in
private theorem center_bot_of_equiv_alternating {L : Type*} [Group L] {n : ℕ} (hn : 4 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center (alternatingGroup (Fin n)) at he
  rw [alternatingGroup.center_eq_bot (by simpa using hn),mem_bot] at he
  exact e.map_eq_one_iff.mp he

private theorem not_alternating_component_direct
    (hcardSeed : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (hcard : Nat.card (centralizer ({σ} : Set (Equiv.Perm (Fin n)))) = 48)
    (hm : AlternatingAction a n σ) : False := by
  rcases hm with ⟨e,he⟩ | ⟨_,⟨e⟩,_⟩
  · have hr : 2 ≤ primeRank 3 c.component := by
      rw [primeRank_congr 3 e]
      exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by omega)
    have houter : IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
      rcases hn with rfl | rfl
      · exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
      · exact alternatingGroup.SevenComponent.outer_two
    have ho := houter.of_equiv (MulAut.outerCongr e).symm
    have hlow := r.fixed_three_rank_of_full_component_direct c hI hcardSeed hz hzne
      (center_bot_of_equiv_alternating (by omega) e) hr ho a ha
    let C := centralizer ({σ} : Set (Equiv.Perm (Fin n)))
    let f : a.fixedSubgroup →* C :=
      (((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom).comp a.fixedSubgroup.subtype).codRestrict C (by
        intro x
        apply mem_centralizer_singleton_iff.mpr
        have hh := he x
        rw [(MulAut.mem_fixedSubgroup _ _).mp x.property] at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm)
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply e.injective
      exact Subtype.ext (congrArg (fun w : C => (w : Equiv.Perm (Fin n))) h)
    have hc : Nat.card C = 48 := hcard
    have hu : primeRank 3 C ≤ 1 := primeRank_le_of_prime_pow_not_dvd (by rw [hc]; decide)
    have hb := (_root_.primeRank_le_of_injective 3 f hf).trans hu
    omega
  · have hc : Nat.card (center c.component) = 3 := by
      rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card]
    obtain ⟨n,hn⟩ := c.center_two.exists_card_eq
    have hd : 3 ∣ 2 ^ n := by rw [←hn,hc]
    have hh := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hh

/-- The source triple-transposition action excludes the A₇ component row. -/
theorem ResidualInput.ordinary_seven_false
    (hcardSeed : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (hm : AlternatingAction a 7 σ) : False := by
  apply not_alternating_component_direct r c hcardSeed hI hz hzne a ha (Or.inr rfl) σ ?_ hm
  rw [Equiv.Perm.nat_card_centralizer,hσ]
  norm_num [Nat.factorial]

/-- The source transposition action excludes the A₆ row of15.2.24. -/
theorem ResidualInput.ordinary_six_false
    (hcardSeed : Nat.card (centralInvolutions T) = 2) (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hm : AlternatingAction a 6 σ) : False := by
  apply not_alternating_component_direct r c hcardSeed hI hz hzne a ha (Or.inl rfl) σ ?_ hm
  rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hσ]
  norm_num [Nat.factorial]


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
