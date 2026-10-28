module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.SquareLifts.Core
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import Theory.GroupAction.PerfectCentralQuotient.ComponentResidual
public import Theory.GroupAction.PerfectCentralQuotient.ComponentImage
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Source inputs and outstanding table deductions for sporadic covers

I.2.2(5b), printed p.409 / PDF p.420, has two assertions: non-2-central
involutions lift to elements of order four, and each involutory outer
automorphism inverts some such lift. `OuterInvolutionInversion` specifies
the second assertion, including the mark on its quotient image. Its use is
restricted by the caller to the quasisimple covers listed in I.2.2(5).

`TableReduction` is an intermediate obligation, not a statement of 16.1.5.
Its two fields must be derived from the M₁₂, J₂ and HS tables with the actual
component and carrier equivalences. In particular neither the noncentral
mark nor quasisimplicity of the fixed two-residual is assumed to be a book
theorem. The final assembly owner must discharge both fields.

Source: Aschbacher–Smith, 16.1.5(4),(8),(10), pp.1171–1172, and the proof
of 16.3.11(3), p.1181, combined manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer

/-- Precisely the outer-inversion assertion of I.2.2(5b), with the quotient
involution and its non-2-central mark retained. The other assertion is
`NonTwoCentralInvolutionLifting`. -/
def OuterInvolutionInversion (K : Type*) [Group K] : Prop :=
  ∀ a : MulAut K, orderOf a = 2 → (¬ ∃ k : K, a = MulAut.conj k) →
    ∃ u : K, orderOf u = 4 ∧
      orderOf (QuotientGroup.mk' (center K) u) = 2 ∧
      ¬ TwoCentral (QuotientGroup.mk' (center K) u) ∧ a u = u⁻¹

/-- The two remaining table consequences for the actual action. These are
outputs of separate table arguments, not source hypotheses of 16.3.11. -/
structure TableReduction {K : Type*} [Group K] (a : MulAut K) : Prop where
  inner_mark : ∀ k : K, a = MulAut.conj k →
    ¬ TwoCentral (QuotientGroup.mk' (center K) k)
  outer_residual : (¬ ∃ k : K, a = MulAut.conj k) →
    IsQuasisimple (MulAut.fixedTwoResidual ((center K).quotientAut a))

open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The original involution normalizes the actual enlargement. -/
theorem original_normalizes_enlargement (h : TerminalCounterexample T z L t)
    (hK : IsCentralizerComponent t (enlargement t L)) :
    z ∈ normalizer (enlargement t L) :=
  seed_centralizer_normalizes h hK (ComponentTransfer.le_layerClosure _ _)
    ⟨(setup h).t_mem, h.localSetup.involution_mem_componentCentralizer⟩

/-- The source relative component is a component of the intrinsic fixed subgroup. -/
theorem componentInside_fixed {K : Subgroup G} (hn : z ∈ normalizer K)
    (hL : ComponentTransfer.IsComponentIn L (ComponentTransfer.centralizerIn K z)) :
    IsComponentIn (L.subgroupOf K) (action hn).fixedSubgroup := by
  refine ⟨fun x hx => (mem_fixed_action hn x).mpr (hL.1 hx).2, ?_⟩
  have hc := hL.2.map_equiv (centralizerEquivFixed hn)
  rw [map_equiv_eq_comap_symm'] at hc
  exact hc

end CFSG.Quasithin.Chapter16.EnlargementSieve.CoverExclusion
