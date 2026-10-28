module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.OddLinear
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The odd-linear residual-centralizer cases

For the full PSL₂(p) alternatives of (E2)(ii), perfection forces p ≥ 5.
Prime-field automorphism coverage represents the actual action of r by PGL₂.
An element outside C_G(L)L gives a representative outside PSL₂, so the exact
earlier exclusion 16.4.6 eliminates this branch. `ExcludesOuterPGL` states
that earlier output; it is not proved by this module.

For the full PSL₃(3) alternative, the SL₃(3) comparison proves triviality of
the center. The resulting marking of L/Z(L) transports the actual residual
O²(C_L(r)) to the fixed two-residual of the corresponding model automorphism.
The intrinsic pointwise-fixer bound then gives case (I). Simplicity and
perfectness of the model are transported from the component, so that a
model calculation may use those hypotheses without recertifying them.

The PSL₃(3) fixer calculation remains an explicit premise of the conditional
assembly below. An abstract S₄ fixed-subgroup or A₄ residual isomorphism does
not discharge it. No exhaustive odd-linear alternative is asserted yet.
`Hypothesis1611.evenType` supplies the even-type input used here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, (E2)(ii),
16.1.5(1–2), 16.4.6 and the proof of 16.4.9(1), printed pp.1170–1172,
1184–1186 and 1189.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.OddLinear
open OuterResidual GorensteinWalter
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
private theorem primeField_model {n p : ℕ} [Fact p.Prime]
    (hL : ClassicalGroup.IsPSL L n p) : Nonempty (L ≃* PSL(n, ZMod p)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F Fact.out
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans (Atlas.fieldEquivPSL n ef)⟩

/-- The exact local output of 16.4.6, retained as an earlier-source input. -/
@[expose] def ExcludesOuterPGL (h : IntersectionSetup T z L g R) : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
    ∀ (e : L ≃* PSL(2, F)) (r : G) (hr : r ∈ R), orderOf r = 2 →
      ¬ PGLShadow.InducesOuterPGL h hr e

/-- Prime-field coverage identifies the actual outer action with an outer PGL₂ matrix. -/
theorem pslTwo_inducesOuterPGL {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (e : L ≃* PSL(2, ZMod p)) : PGLShadow.InducesOuterPGL h hr e := by
  let hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  obtain ⟨A, hA⟩ := Theory.PSL2.primeField_pgl_coverage hp hlarge
    (MulAut.congr e (involutionAction h hr))
  apply (PGLShadow.inducesOuterPGL_iff h hr e hF hc).mpr
  refine ⟨A, ?_, hA.symm⟩
  rintro ⟨x, hx⟩
  have hi : ∃ x : L, involutionAction h hr = MulAut.conj x := by
    apply (MulAut.congr_inner_iff e _).mp
    refine ⟨x, ?_⟩
    rw [← hA, ← hx]
    exact pgl2InnerAutPSL2_toPGL (ZMod p) hF hc x
  exact action_not_inner L (h.sylow_normalizes (h.le_sylow hr)) hout hi

/-- The prime family is eliminated by the exact 16.4.6 output. -/
theorem pslTwo_excluded (h : IntersectionSetup T z L g R)
    (hno : ExcludesOuterPGL h) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hL : ClassicalGroup.IsPSL L 2 p) : False := by
  let := h.component.quasisimple
  have hlarge := OtherPreliminaries.OddLinear.pslTwo_parameter_ge_five hp hL
  let : Fact p.Prime := ⟨hp.1⟩
  have hodd : Odd p := hp.1.odd_of_ne_two (by omega)
  obtain ⟨e⟩ := primeField_model hL
  exact hno (ZMod p) (by simpa using hodd) e r hr hr2
    (pslTwo_inducesOuterPGL hodd (by omega) h hr hout e)

omit [Finite G] in
private theorem pslThree_center (e : L ≃* Matrix.PSL3Three.PSL) : center L = ⊥ := by
  apply (center L).eq_bot_iff_card.mpr
  calc
    Nat.card (center L) = Nat.card (center Matrix.PSL3Three.SL) :=
      Nat.card_congr (centerCongr (e.trans Matrix.PSL3Three.equiv.symm)).toEquiv
    _ = 1 := (center Matrix.PSL3Three.SL).eq_bot_iff_card.mp Matrix.PSL3Three.center_eq_bot

/-- The bound concerns the actual embedded fixed residual of the transported action.
The full-group identification supplies the quotient marking; no central cover is discarded. -/
theorem pslThree_alternative_of_fixer_bound {K : GroupClass} (hG : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hL : ClassicalGroup.IsPSL L 3 3)
    (hfix : ∀ [IsSimpleGroup Matrix.PSL3Three.PSL] [Group.IsPerfect Matrix.PSL3Three.PSL]
      (a : MulAut Matrix.PSL3Three.PSL), orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) →
      ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut Matrix.PSL3Three.PSL)
        (LiePreliminaries.fixedTwoResidual Matrix.PSL3Three.PSL a : Set Matrix.PSL3Three.PSL))) :
    ResidualCentralizerAlternative T L r := by
  let := h.component.quasisimple
  obtain ⟨e⟩ := primeField_model hL
  let q : (L ⧸ center L) ≃* Matrix.PSL3Three.PSL :=
    ((QuotientGroup.quotientMulEquivOfEq (pslThree_center e)).trans
      (QuotientGroup.quotientBot)).trans e
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup Matrix.PSL3Three.PSL := (MulEquiv.isSimpleGroup_congr q).mp inferInstance
  let : Group.IsPerfect Matrix.PSL3Three.PSL :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply alternative_of_fixer_not_four_dvd L q h hr hr2
  rw [modelResidual_eq_fixedTwoResidual L q r
    (h.sylow_normalizes (h.le_sylow hr))
    (component_oddCore hG.evenType h.toCentralComponentSetup)]
  exact hfix _ ((modelAction_order L q h hr).trans hr2)
    (modelAction_outer L q r (h.sylow_normalizes (h.le_sylow hr)) hout)

/-- Conditional assembly of the odd-linear case. The PSL₃(3) model bound must
still be proved, while `hno` is precisely the allowed earlier output 16.4.6. -/
theorem alternative_of_fixer_bound {K : GroupClass} (hG : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R) (hno : ExcludesOuterPGL h)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hfamily : ClassicalGroup.IsPSL L 3 3 ∨
      ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)
    (hfix : ∀ [IsSimpleGroup Matrix.PSL3Three.PSL] [Group.IsPerfect Matrix.PSL3Three.PSL]
      (a : MulAut Matrix.PSL3Three.PSL), orderOf a = 2 →
      (¬ ∃ x, a = MulAut.conj x) →
      ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut Matrix.PSL3Three.PSL)
        (LiePreliminaries.fixedTwoResidual Matrix.PSL3Three.PSL a : Set Matrix.PSL3Three.PSL))) :
    ResidualCentralizerAlternative T L r := by
  rcases hfamily with hL | ⟨p, hp, hL⟩
  · exact pslThree_alternative_of_fixer_bound hG h hr hr2 hout hL hfix
  · exact (pslTwo_excluded h hno hr hr2 hout hp hL).elim

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.OddLinear
