module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.ComponentInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Assembly

/-!
# Component inputs for the exchanged source sieve

The complete exchanged output of the embedding and residual reduction supplies
its original component and moving element, including the split complement.
The actual complement quotient map recovers the plane coordinates from X/O₂(X).
Consequently the complete embedding witness feeds the established CPU and
section-kernel argument, which supplies every C.2.7 hypothesis for that same
component. In particular radical invariance is proved, rather than imposed on
an arbitrary component chosen from the weaker quotient-model statement.

Applying the full C.2.7 and C.1.34 sieve and its source endgame eliminates this
branch. The full universal earlier embedding, orbit and residual theorems then
leave precisely the binary branch in the original contrary configuration.
That last implication is conditional on the unresolved original embedding
interface. It does not replace the separate adequate intrinsic reduction
retaining Held, whose extra branch remains with the source assembly owner.
Source: Aschbacher--Smith, 15.4.20, printed p.1164; 1.3.4, 1.2.1(3),
1.2.2(a), and C.2.3--7.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {d : Source.Geometry G} {i j : Bool}
variable {H U K : Subgroup G}

/-- The intrinsic CPU/component record is exactly the complete C.2.7 input. -/
theorem componentHypotheses_of_source {A : Type u} [Group A]
    {R M L : Subgroup A} (hc : CoreElimination.ComponentInputs.Hypotheses κ R M L) :
    ComponentHypotheses κ A R M L := by
  exact ⟨hc.pushing_up.sqtk,
    ⟨hc.pushing_up.nontrivial, hc.pushing_up.radical⟩,
    hc.pushing_up.characteristic_control, hc.pushing_up.sylow_normalClosure,
    hc.component, hc.quasisimple, hc.characteristic_two, hc.outside, hc.invariant⟩

/-- Recover the complete component input from the actual exchanged embedding
output, retaining its first component and exchanger in the selected witness. -/
theorem exchanged_selected_hypotheses (hG : IsSimpleQTKE κ G)
    (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (P : Sylow 3 d.wholeX)
    (branch : EmbeddingReduction.ExchangedCase H U
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) K) :
    ∃ L r, Selected H U K L r ∧
      ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
        (d.M₁.subgroupOf H) (L.subgroupOf H) := by
  obtain ⟨L, r, hL, hq, _, hm, hr, hmove, _, hK, hprod, _, hP, hd, hcomm⟩ := branch
  let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
  have hswap : Chapter1.XiEmbedding.SwappedFactors U P₀ L :=
    ⟨fun hn => hmove (hn hr.1), r, hr, hmove, hP, hd, hcomm⟩
  obtain ⟨_, hlocal, _, _⟩ := h.placed.embedding_input hG P
  have hplane : Nonempty (P₀ ≃* Chapter1.XiEmbedding.Plane 3) := by
    exact ⟨hlocal.complementQuotientEquiv.trans (h.placed.quotient.trans
      (AddEquiv.toMultiplicative
        (LinearEquiv.finTwoArrow (ZMod 3) (ZMod 3)).toAddEquiv).symm)⟩
  have hXK : d.wholeX ≤ K := h.closure ▸
    EmbeddingReduction.le_normalClosureIn h.placed.whole_le
  have hXorbit : d.wholeX ≤ componentOrbit L U := by
    apply hXK.trans
    rw [hK]
    exact sup_le (le_componentOrbit L U)
      (le_iSup (fun s : U => L.conjBy s) ⟨r, hr.1⟩)
  let e : CoreElimination.ComponentInputs.EmbeddingWitness d H K U P := {
    seed := L
    source := ⟨hL, hq, hXorbit, hplane, Or.inl ⟨hswap, hm⟩⟩
    refinement := Or.inr ⟨r, hr.1, hmove, hK.symm⟩ }
  let c : CoreElimination.ComponentInputs.ContraryContext d i j H K U := {
    placed := h.placed
    normal_closure := h.closure
    residual := h.residual
    generation := h.generation
    omega := h.seed
    thompson := h.thompson
    unique := unique }
  have hc := CoreElimination.ComponentInputs.contrary_hypotheses hG c P e
    h.characteristic_two
  have hc' := componentHypotheses_of_source hc
  refine ⟨L, r, ⟨hL, hr.1, hmove, hK.symm, hprod, hm⟩, ?_⟩
  simpa only [e, sourceRadical, inf_subgroupOf_left] using hc'

/-- The original contrary geometry discharges the entire component input of
the source sieve; the selected block is constructed on its actual component. -/
theorem exchanged_case_contradiction
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (P : Sylow 3 d.wholeX)
    (branch : EmbeddingReduction.ExchangedCase c.H c.U
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) c.K) : False := by
  obtain ⟨L, r, hs, hc⟩ := exchanged_selected_hypotheses c.ambient h c.unique_X P branch
  exact sieve_contradiction c27 c134 c h hs hc

/-- Apply the complete universal earlier embedding, orbit and residual
statements, and eliminate the exchanged branch by the actual source sieve.
The remaining binary component retains the full automorphism quotient. This
corollary retains the unresolved original embedding implication; it makes no
exclusion of the extra Held case in the separate adequate intrinsic route. -/
theorem source_binary_case
    (c27 : UniversalC27.{u})
    (c134 : SL3Geometry.SourceCases.UniversalClassification.{u})
    (embedding : EmbeddingReduction.LocalEmbeddingTheorem κ)
    (orbits : EmbeddingReduction.ComponentOrbitTheorem κ)
    (residual : EmbeddingReduction.TwoOrbitResidualTheorem κ)
    (c : BlockEndgame.ContraryData κ d i j)
    (h : Input d i j c.H c.U c.K) (P : Sylow 3 d.wholeX) :
    EmbeddingReduction.BinaryCase c.H c.U c.K := by
  have hb := (h.placed.normalClosure_branches c.ambient embedding orbits residual P).2
  rw [← h.closure] at hb
  exact hb.resolve_right (exchanged_case_contradiction c27 c134 c h P)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
