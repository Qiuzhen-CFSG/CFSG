module

public import Theory.Quasithin
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import BenderSuzuki.SE.Basic

/-!
# Multiple maximal two-locals force a four-group

Two distinct maximal two-local subgroups containing a fixed Sylow two-subgroup
force a four-group in the ambient involution core. No local solvability or
characteristic-two hypothesis is needed for this elementary reduction in the
setup for Stellmacher's Theorem 1.

Otherwise, a central involution of the Sylow subgroup is its unique involution:
a second one would commute with it and generate a four-group in the involution
core. For any two-local over the Sylow, the normal two-subgroup that defines it
lies in the Sylow and contains the unique involution. Conjugation by the local
fixes this involution. Consequently every such local lies in its normalizer,
itself a two-local; maximality makes the original two maximal locals equal.

Source: the strong-embedding exclusion implicit in Section 11 of
`refs/latex/stellmacher-n-group.tex`, with the elementary rank-one reduction
spelled out to preserve the original theorem-one hypotheses.
-/

namespace Stellmacher.SectionEleven

open BenderSuzuki BenderSuzuki.PFchapter1section1

universe u

variable {H : Type u} [Group H] [Finite H]

private theorem exists_order_two_in_two_subgroup
    (Q : Subgroup H) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ q : H, q ∈ Q ∧ orderOf q = 2 := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  obtain ⟨n, hn, hcard⟩ := hQ.nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card Q := by
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 hdiv
  exact ⟨q, q.property, by simpa only [Subgroup.orderOf_coe] using hq⟩

omit [Finite H] in
private theorem normal_two_witness_le_sylow
    (S0 : Sylow 2 H) (P Q : Subgroup H)
    (hSP : (S0 : Subgroup H) ≤ P)
    (hQ : IsPGroup 2 Q) (hPQ : P = Subgroup.normalizer Q) :
    Q ≤ (S0 : Subgroup H) := by
  have hQP : Q ≤ P := hPQ ▸ Subgroup.le_normalizer
  let : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPQ.le
  have hQp : IsPGroup 2 (Q.subgroupOf P) :=
    hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hQT := hQp.le_sylow_of_normal (S0.subtype hSP)
  intro q hq
  exact hQT (show (⟨q, hQP hq⟩ : P) ∈ Q.subgroupOf P from hq)

/-- The involution core has two-rank at least two whenever two distinct maximal
2-locals contain the prescribed Sylow subgroup. -/
public theorem involutionCore_twoRank_of_multiple_maximal
    (S0 : Sylow 2 H)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧ IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧ (S0 : Subgroup H) ≤ P2) :
    TwoRankAtLeastTwo (involutionCore H) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra hno
  obtain ⟨P1, P2, hne, hP1, hP2, hS1, hS2⟩ := hmax
  obtain ⟨Q, hQne, hQp, _⟩ := hP1.prop
  obtain ⟨q, _, hq⟩ := exists_order_two_in_two_subgroup Q hQp hQne
  have hdiv : 2 ∣ Nat.card H := hq ▸ orderOf_dvd_natCard q
  let : Nontrivial S0 := (Subgroup.nontrivial_iff_ne_bot (S0 : Subgroup H)).mpr
    (S0.ne_bot_of_dvd_card hdiv)
  let : Nontrivial (Subgroup.center S0) := S0.isPGroup'.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center S0) :=
    S0.isPGroup'.to_subgroup (Subgroup.center S0)
  obtain ⟨n, hn, hZcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
  have hZdiv : 2 ∣ Nat.card (Subgroup.center S0) := by
    rw [hZcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S0) 2 hZdiv
  have hzH : orderOf ((z : S0) : H) = 2 := by
    simpa only [Subgroup.orderOf_coe] using hz
  have unique (x : H) (hxS : x ∈ (S0 : Subgroup H)) (hx : orderOf x = 2) :
      x = ((z : S0) : H) := by
    by_contra hxz
    have hxL : x ∈ involutionCore H := by
      apply Subgroup.subset_closure
      exact ⟨by intro h; simp [h] at hx, by simpa [hx] using pow_orderOf_eq_one x⟩
    have hzL : ((z : S0) : H) ∈ involutionCore H := by
      apply Subgroup.subset_closure
      exact ⟨by intro h; simp [h] at hzH,
        by simpa [hzH] using pow_orderOf_eq_one ((z : S0) : H)⟩
    let xL : involutionCore H := ⟨x, hxL⟩
    let zL : involutionCore H := ⟨((z : S0) : H), hzL⟩
    have hxLorder : orderOf xL = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hx
    have hzLorder : orderOf zL = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hzH
    have hxLzL : xL ≠ zL := fun h => hxz (congrArg Subtype.val h)
    have hcomm : Commute xL zL := by
      change xL * zL = zL * xL
      apply Subtype.ext
      change x * ((z : S0) : H) = ((z : S0) : H) * x
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property) ⟨x, hxS⟩)
    let E : Subgroup (involutionCore H) := Subgroup.closure ({xL, zL} : Set _)
    let : IsKleinFour E :=
      Subgroup.isKleinFour_closure_pair_of_orderOf xL zL hxLorder hzLorder hxLzL hcomm
    exact hno ⟨E, IsKleinFour.card_four, fun y => by
      simpa only [IsKleinFour.exponent_two] using Monoid.pow_exponent_eq_one y⟩
  let N : Subgroup H := Subgroup.normalizer (Subgroup.zpowers ((z : S0) : H))
  have hN : IsTwoLocal N := by
    refine ⟨Subgroup.zpowers ((z : S0) : H), ?_, ?_, rfl⟩
    · intro hbot
      have hz1 : ((z : S0) : H) = 1 := Subgroup.zpowers_eq_bot.mp hbot
      simp [hz1] at hzH
    · exact IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hzH)
  have local_le (P : Subgroup H) (hP : IsTwoLocal P)
      (hSP : (S0 : Subgroup H) ≤ P) : P ≤ N := by
    obtain ⟨R, hRne, hRp, hPR⟩ := hP
    have hRS := normal_two_witness_le_sylow S0 P R hSP hRp hPR
    obtain ⟨r, hr, hrord⟩ := exists_order_two_in_two_subgroup R hRp hRne
    have hzR : ((z : S0) : H) ∈ R := unique r (hRS hr) hrord ▸ hr
    intro g hg
    have hconjR : g * ((z : S0) : H) * g⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hPR ▸ hg) _).mp hzR
    have hfix : (MulAut.conj g) ((z : S0) : H) = ((z : S0) : H) := by
      apply unique _ (hRS hconjR)
      change orderOf ((MulAut.conj g) ((z : S0) : H)) = 2
      exact (MulEquiv.orderOf_eq _ _).trans hzH
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hfix
  have hP1N := local_le P1 hP1.prop hS1
  have hP2N := local_le P2 hP2.prop hS2
  exact hne ((le_antisymm hP1N (hP1.2 hN hP1N)).trans
    (le_antisymm hP2N (hP2.2 hN hP2N)).symm)

end Stellmacher.SectionEleven
