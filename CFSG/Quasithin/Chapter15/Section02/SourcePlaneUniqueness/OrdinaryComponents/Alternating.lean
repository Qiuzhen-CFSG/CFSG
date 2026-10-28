module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.FullRank
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# The marked six- and seven-letter ordinary components

The transposition on A₆ and the triple transposition on A₇ each have
centralizer of order48 in the corresponding symmetric group. Their actual
fixed subgroups embed in these centralizers, so have three-rank at most one.
The full-rank source argument gives the opposite lower bound. Perfect
triple covers are excluded by the original two-group component center.

These are the alternating row in15.2.24 and the A₇ terminal row of15.2.15.
Source: Aschbacher--Smith, printed pp.1117--1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

omit d [Group G] [Finite G] in
private theorem center_bot_of_equiv_alternating {L : Type*} [Group L] {n : ℕ} (hn : 4 ≤ n)
    (e : L ≃* alternatingGroup (Fin n)) : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center (alternatingGroup (Fin n)) at he
  rw [alternatingGroup.center_eq_bot (by simpa using hn),mem_bot] at he
  exact e.map_eq_one_iff.mp he

private theorem not_alternating_component (hI : PlaneEscapes Mc ZS I)
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
    have hlow := fixed_three_rank_of_full_component d c hI hz hzne
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
theorem not_seven_component (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 7)) (hσ : σ.cycleType = {2,2,2})
    (hm : AlternatingAction a 7 σ) : False := by
  apply not_alternating_component d c hI hz hzne a ha (Or.inr rfl) σ ?_ hm
  rw [Equiv.Perm.nat_card_centralizer,hσ]
  norm_num [Nat.factorial]

/-- The source transposition action excludes the A₆ row of15.2.24. -/
theorem not_six_component (hI : PlaneEscapes Mc ZS I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ.IsSwap)
    (hm : AlternatingAction a 6 σ) : False := by
  apply not_alternating_component d c hI hz hzne a ha (Or.inl rfl) σ ?_ hm
  rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hσ]
  norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
