module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.PSLTwoResidual
public import Theory.GroupAction.FixedResidualFixerTransport
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Marked rank-one residuals in the involution-centralizer calculation

The actual quotient action of an outer involution on a binary PSL₂ model
is conjugate to an entrywise field involution. Transporting its embedded
two-residual and its full automorphism fixer preserves both markings.
The field degree must be even; degree two is retained, where the fixed
group PSL₂(2) is not perfect. No fixer bound is assumed or proved here.

These reductions use only (E1), quasisimplicity, and the actual intersection
setup. In particular they keep every central covering kernel until the
proved residual projection passes to the central quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(4) and the proof of 16.4.9(1), printed pp.1171 and 1189.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
open OuterResidual BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

section Transport
variable [IsQuasisimple L] {S : Type*} [Group S] [Finite S]

/-- An actual automorphism conjugacy transports the embedded residual. -/
theorem modelResidual_eq_map_of_congr (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ center L) ≃* S) (hn : r ∈ normalizer (L : Set G))
    (a c : MulAut S)
    (hc : modelAction L e (actionElement L r hn) = MulAut.congr c a) :
    modelResidual L e r = (LiePreliminaries.fixedTwoResidual S a).map c.toMonoidHom := by
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd, hc]
  exact (MulAut.map_embeddedFixedResidual 2 c a).symm

/-- The same conjugacy preserves the full pointwise-fixer cardinality. -/
theorem modelResidual_fixer_card_of_congr (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ center L) ≃* S) (hn : r ∈ normalizer (L : Set G))
    (a c : MulAut S)
    (hc : modelAction L e (actionElement L r hn) = MulAut.congr c a) :
    Nat.card (fixingSubgroup (MulAut S) (modelResidual L e r : Set S)) =
      Nat.card (fixingSubgroup (MulAut S)
        (LiePreliminaries.fixedTwoResidual S a : Set S)) := by
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd, hc]
  exact MulAut.card_embeddedFixedResidual_fixer_congr 2 c a
end Transport

section Linear
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Normalize the actual outer action on any finite characteristic-two PSL₂ carrier. -/
theorem psl2_field_action (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e : (L ⧸ center L) ≃* PSL2MatrixGroup F) :
    ∃ (σ : F ≃+* F) (c : PSL2MatrixGroup F),
      Function.Involutive σ ∧ σ ≠ RingEquiv.refl F ∧
      modelAction L e (actionElement L r (h.sylow_normalizes (h.le_sylow hr))) =
        MulAut.congr (MulAut.conj c) (fieldAut σ) := by
  let := h.component.quasisimple
  let hn := h.sylow_normalizes (h.le_sylow hr)
  let a := modelAction L e (actionElement L r hn)
  have ha2 : a ^ 2 = 1 := by
    have ho : orderOf a = 2 := (modelAction_order L e h hr).trans hr2
    simpa only [ho] using pow_orderOf_eq_one a
  have haout : ¬ ∃ x, a = MulAut.conj x := modelAction_outer L e r hn hout
  obtain ⟨d, σ, he⟩ := semilinear_coverage a
  obtain ⟨hs, hd⟩ := semilinear_involution_data σ d (by rw [← he]; exact ha2)
  have hne : σ ≠ RingEquiv.refl F := by
    intro hh
    apply haout
    exact ⟨d, by simpa only [hh, fieldAut_refl, mul_one] using he⟩
  obtain ⟨c, hc⟩ := semilinear_coboundary σ hs hne d hd
  exact ⟨σ, c, hs, hne, he.trans (semilinear_congr_of_coboundary σ d c hc).symm⟩

/-- The residual marking and its fixer both reduce to the actual entrywise field action. -/
theorem psl2_marked_field_residual (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e : (L ⧸ center L) ≃* PSL2MatrixGroup F) :
    ∃ (σ : F ≃+* F) (c : PSL2MatrixGroup F),
      Function.Involutive σ ∧ σ ≠ RingEquiv.refl F ∧
      modelResidual L e r =
        (LiePreliminaries.fixedTwoResidual (PSL2MatrixGroup F) (fieldAut σ)).map
          (MulAut.conj c).toMonoidHom ∧
      Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
        (modelResidual L e r : Set (PSL2MatrixGroup F))) =
      Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
        (LiePreliminaries.fixedTwoResidual (PSL2MatrixGroup F) (fieldAut σ) :
          Set (PSL2MatrixGroup F))) := by
  let := h.component.quasisimple
  obtain ⟨σ, c, hs, hne, hc⟩ := psl2_field_action h hr hr2 hout e
  have hodd := component_oddCore hG h.toCentralComponentSetup
  exact ⟨σ, c, hs, hne,
    modelResidual_eq_map_of_congr hodd e _ (fieldAut σ) (MulAut.conj c) hc,
    modelResidual_fixer_card_of_congr hodd e _ (fieldAut σ) (MulAut.conj c) hc⟩
end Linear

/-- An outer involution forces even field degree, with the degree-two endpoint included. -/
theorem psl2_degree_even (hG : HasEvenTypeCentralizers G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) : Even n := by
  let := h.component.quasisimple
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let e' := (LiePreliminaries.centerQuotientEquivTwoCore
    (component_oddCore hG h.toCentralComponentSetup)).trans e
  obtain ⟨σ, _, hs, hne, _⟩ := psl2_field_action h hr hr2 hout e'
  have ho : orderOf σ = 2 := orderOf_eq_prime (by ext x; exact hs x) hne
  have hd := orderOf_dvd_natCard σ
  rw [ho, FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hcard] at hd
  exact even_iff_two_dvd.mpr hd

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.Bender
