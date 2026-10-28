module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Sporadic.Actions
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Lifting an odd elementary cube in an ambient local section

A subgroup H of the normalizer of a nontrivial two-subgroup Q may have
an elementary abelian odd-prime cube in H/N, where N is a normal two-subgroup
of H. The coprime-kernel lifting theorem supplies an elementary cube in H.
A subgroup of order p² and an element outside it then give the concrete
ambient `OddRankThreeWitness`, including the independent commuting element.
Normality of N is only relative to H. Neither centrality nor splitting of
the full extension is assumed.

This is a sufficient construction interface for the J₂ and HS branches of
the selected-conjugator step in Aschbacher–Smith, combined manuscript
(1 March 2004), 16.5.6(3), printed p.1197. The family geometry must still
construct the section from the source hypotheses. In particular H is an
ambient subgroup: the assertion is not an intrinsic rank-three assertion
about J₂ or HS. No involution-lifting claim is made, so the order-four
lifts in I.2.2(5), pp.409–412, remain available.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic.JankoTwoHigmanSims

variable {G : Type*} [Group G] [Finite G]

/-- Select a plane and an independent commuting element in an actual elementary cube. -/
theorem rankWitness_of_elementary_cube {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (Q A : Subgroup G) (hQ : Q ≠ ⊥) (hQtwo : IsPGroup 2 Q)
    (hAN : A ≤ normalizer (Q : Set G)) (hA : IsElementaryAbelian p A)
    (hcard : Nat.card A = p ^ 3) : Nonempty (OddRankThreeWitness G) := by
  let := hA
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p
    (show p ^ 2 ∣ Nat.card A from hcard ▸ pow_dvd_pow p (by decide : 2 ≤ 3))
  let E := B.map A.subtype
  have hEA : E ≤ A := map_subtype_le B
  have hEc : Nat.card E = p ^ 2 :=
    (card_map_of_injective A.subtype_injective).trans hB
  have hE : IsElementaryAbelian p E := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from
      congrArg Subtype.val (mul_comm' (⟨x, hEA x.property⟩ : A)
        (⟨y, hEA y.property⟩ : A)))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := A) x (hEA x.property))) }
  have hne : E ≠ A := by
    intro he
    have hc := congrArg (fun D : Subgroup G => Nat.card D) he
    rw [hEc, hcard] at hc
    exact (ne_of_lt ((Nat.pow_lt_pow_iff_right hp).mpr (by decide : 2 < 3))) hc
  obtain ⟨x, hxA, hxE⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hEA hne)
  have hx1 : x ≠ 1 := fun he => hxE (he ▸ E.one_mem)
  have hxorder : orderOf x = p :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxA) hx1
  refine ⟨⟨p, Fact.out, hpodd, Q, hQ, hQtwo, E, hEA.trans hAN, hE, hEc,
    x, hAN hxA, hxorder, hxE, ?_⟩⟩
  intro y hy
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm' (⟨y, hEA hy⟩ : A) (⟨x, hxA⟩ : A))

/-- Output geometry to be constructed by a family proof, never a standing source hypothesis. -/
def HasLocalSection (G : Type*) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
    ∃ (H : Subgroup G) (N : Subgroup H) (_ : N.Normal),
      H ≤ normalizer (Q : Set G) ∧ IsPGroup 2 N ∧
        ∃ A : Subgroup (H ⧸ N), IsElementaryAbelian p A ∧ Nat.card A = p ^ 3

/-- Lift the cube through its actual two-group kernel and construct every ambient witness field. -/
theorem rankWitness_of_local_section (h : HasLocalSection G) :
    Nonempty (OddRankThreeWitness G) := by
  obtain ⟨p, hp, ho, Q, hQ, hQtwo, H, N, hN, hHN, hNtwo, A, hA, hc⟩ := h
  let := hN
  let : Fact p.Prime := ⟨hp⟩
  let := hA
  have hker : Nat.Coprime p (Nat.card (QuotientGroup.mk' N).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := hNtwo.exists_card_eq
    rw [hn]
    exact ho.coprime_two_right.pow_right n
  obtain ⟨B, hB, _, hBc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hker A
  let := hB
  exact rankWitness_of_elementary_cube ho Q (B.map H.subtype) hQ hQtwo
    ((map_subtype_le B).trans hHN) (IsElementaryAbelian.map H.subtype)
    ((card_map_of_injective H.subtype_injective).trans (hBc.trans hc))

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Sporadic.JankoTwoHigmanSims
