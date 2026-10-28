module

public import Theory.GroupTheory.PCoreSurjective
public import Theory.ElementaryAbelian.GeneratorRank
import Mathlib.Tactic

/-!
# The order-2p calculation for intrinsic E1 sections

A self-centralizing normal subgroup of odd prime order in a group of order
2p is its p-core. Every nontrivial elementary two-subgroup has order two
and acts nontrivially, so its commutator with that core is the full core.
The same centralizer calculation excludes a normal two-subgroup.

The epimorphism adapter uses the literal quotient by the two-core and
transports its actor image, commutator, and rank through the first
isomorphism theorem. The symmetric and dihedral leaves supply the concrete
inputs; no local subgroup existence is asserted here.

Source: Aschbacher–Smith, E.1.2(E1) and E.1.5, printed p.210.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
/-- A self-centralizing normal odd-prime subgroup excludes a normal two-subgroup. -/
theorem twoCore_eq_bot {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (N : Subgroup Y) [N.Normal] (hN : Nat.card N = p)
    (hC : centralizer (N : Set Y) ≤ N) : pCore 2 Y = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hNp : IsPGroup p N := IsPGroup.of_card (n := 1) (by simpa using hN)
  have hd := IsPGroup.disjoint_of_ne 2 p hp2.symm (pCore 2 Y) N pCore_isPGroup hNp
  have hc : pCore 2 Y ≤ centralizer (N : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  exact disjoint_self.mp (hd.mono_right (hc.trans hC))

/-- The elementary order-2p calculation, retaining the actual actor. -/
theorem primeSection {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (N : Subgroup Y) [N.Normal] (hN : Nat.card N = p)
    (hY : Nat.card Y = 2 * p) (hC : centralizer (N : Set Y) ≤ N)
    (a : Subgroup Y) [IsElementaryAbelian 2 a] (ha : a ≠ ⊥) :
    IsPGroup 2 (Y ⧸ pCore p Y) ∧ pCore p Y ≠ ⊥ ∧
      pCore p Y = ⁅pCore p Y, a⁆ ∧ Group.rank a = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hNp : IsPGroup p N := IsPGroup.of_card (n := 1) (by simpa using hN)
  have hle : N ≤ pCore p Y := le_sSup ⟨inferInstance, hNp⟩
  have hcorecard : Nat.card (pCore p Y) ∣ p := by
    have hd := (pCore p Y).card_subgroup_dvd_card
    rw [hY] at hd
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := Y)).exists_card_eq
    have hc : Nat.Coprime (Nat.card (pCore p Y)) 2 := by
      rw [hk]
      exact (Nat.coprime_two_right.mpr ho).pow_left k
    exact hc.dvd_mul_left.mp hd
  have heq : pCore p Y = N := (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hN]; exact Nat.le_of_dvd hp.pos hcorecard)).symm
  have hq : Nat.card (Y ⧸ N) = 2 := by
    have hc := N.card_eq_card_quotient_mul_card_subgroup
    rw [hY, hN] at hc
    exact Nat.eq_of_mul_eq_mul_right hp.pos hc.symm
  have hane : 1 < Nat.card a := a.one_lt_card_iff_ne_bot.mpr ha
  have hadiv : Nat.card a ∣ 2 := by
    have hd := a.card_subgroup_dvd_card
    rw [hY] at hd
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 a).exists_card_eq
    have hc : Nat.Coprime (Nat.card a) p := by
      rw [hk]
      exact (Nat.coprime_two_left.mpr ho).pow_left k
    exact hc.dvd_mul_right.mp hd
  have hacard : Nat.card a = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hadiv).resolve_left (by omega)
  have hdis : Disjoint a N := IsPGroup.disjoint_of_ne 2 p hp2.symm a N
    (IsElementaryAbelian.isPGroup 2 a) hNp
  have hcommle : ⁅N, a⁆ ≤ N := commutator_le_left N a
  have hcommne : ⁅N, a⁆ ≠ ⊥ := by
    intro hh
    have hacent : a ≤ centralizer (N : Set Y) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    exact ha (disjoint_self.mp (hdis.mono_right (hacent.trans hC)))
  have hcommcard : Nat.card (⁅N, a⁆ : Subgroup Y) = p := by
    have hd := card_dvd_of_le hcommle
    rw [hN] at hd
    exact ((Nat.dvd_prime hp).mp hd).resolve_left
      (fun hh => hcommne (Subgroup.card_eq_one.mp hh))
  refine ⟨(IsPGroup.of_card (p := 2) (n := 1) (by simpa using hq)).of_equiv
    (QuotientGroup.quotientMulEquivOfEq heq.symm), ?_, ?_, ?_⟩
  · rw [heq]
    intro hh
    have := Subgroup.card_eq_one.mpr hh
    rw [hN] at this
    exact hp.ne_one this
  · rw [heq]
    exact (Subgroup.eq_of_le_of_card_ge hcommle (by rw [hN, hcommcard])).symm
  · let : Nontrivial a := (nontrivial_iff_ne_bot a).mpr ha
    exact Nat.le_antisymm
      (IsElementaryAbelian.rank_le_of_card_le (p := 2) a (by simpa using hacard.le))
      (Group.rank_pos (G := a))

/-- Transfer the calculation using the literal two-core quotient map. -/
theorem intrinsic_of_epimorphism {X : Type*} [Group X] [Finite X]
    {p : ℕ} (B : Subgroup X) (f : X →* Y) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 X)
    (hdata : IsPGroup 2 (Y ⧸ pCore p Y) ∧ pCore p Y ≠ ⊥ ∧
      pCore p Y = ⁅pCore p Y, B.map f⁆ ∧ Group.rank (B.map f) = 1) :
    let Q := X ⧸ pCore 2 X
    let a := B.map (QuotientGroup.mk' (pCore 2 X))
    IsPGroup 2 (Q ⧸ pCore p Q) ∧ pCore p Q ≠ ⊥ ∧
      pCore p Q = ⁅pCore p Q, a⁆ ∧ Group.rank a = 1 := by
  let Q := X ⧸ pCore 2 X
  let a := B.map (QuotientGroup.mk' (pCore 2 X))
  let e : Q ≃* Y := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hm : a.map e.toMonoidHom = B.map f := by
    rw [map_map]
    congr 1
  refine ⟨hdata.1.of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso p e)).symm,
    ?_, ?_, ?_⟩
  · intro hh
    apply hdata.2.1
    rw [← pCore_map_iso p e, hh, Subgroup.map_bot]
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_commutator, pCore_map_iso, hm]
    exact hdata.2.2.1
  · exact (Group.rank_congr (a.equivMapOfInjective e.toMonoidHom e.injective)).trans
      ((Subgroup.rank_congr hm).trans hdata.2.2.2)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
