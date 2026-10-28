module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.Preparation
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Relations
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.ReductionClassification.SimpleSupport.TraceSeries

/-!
# Trace exclusion of nonsimple point restrictions in binary degree eighteen

Two explicit elements of the actual SL₃(4) point stabilizer are conjugate
in the full Mathieu cover. On each six-dimensional binary constituent their
traces differ by one. Trace is additive for a submodule and its literal
quotient, with no invariant complement required. Consequently a twelve-
dimensional central-character module has trace difference zero.

If the point restriction in binary dimension eighteen is not simple, the
checked degree reductions provide a six-dimensional simple submodule and
an actual twelve-dimensional quotient. Their trace differences sum to one,
contradicting full-group conjugacy. Thus the point restriction must be simple.

The word matrices and their identification with the actual point stabilizer
are reused from `ExtensionExclusion.Relations`; their ATLAS attribution is
retained there. The numerical degree-window context is Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16. This argument
retains nonsplit extensions and does not assume the source's degree list.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
open Representation Representation.SL3FourLocalCatalogue
open Uniqueness Uniqueness.PointRestriction Uniqueness.PointRestriction.PointModel
open Uniqueness.PointRestriction.ExtensionExclusion Uniqueness.PointExtension
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private lemma constituent_trace_gap (a : Constituent) :
    (constituent a).character (classicalWord 1) +
      (constituent a).character (classicalWord 3) = 1 := by
  unfold Representation.character
  rw [← LinearMap.trace_conj' _ flatten, ← LinearMap.trace_conj' _ flatten]
  rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 6)),
    LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 6))]
  change (∑ i : Fin 6, flatten (constituent a (classicalWord 1)
    (flatten.symm (Pi.single i 1))) i) +
    (∑ i : Fin 6, flatten (constituent a (classicalWord 3)
    (flatten.symm (Pi.single i 1))) i) = 1
  cases a <;> decide +kernel

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  (σ : Representation (ZMod 2) Representation.SL3FourLocalCatalogue.SL U)

/-- Binary trace difference on the specified pair conjugate in the full cover. -/
def traceGap : ZMod 2 := σ.character (classicalWord 1) + σ.character (classicalWord 3)

/-- Additivity retains the actual quotient, including nonsplit extensions. -/
lemma traceGap_add (N : Subrepresentation σ) :
    traceGap σ = traceGap N.toRepresentation + traceGap N.quotientRepresentation := by
  unfold traceGap
  rw [character_eq_subrepresentation_add_quotient σ N]
  simp only [Pi.add_apply]
  ring

/-- Every six-dimensional central-character point module has trace difference one. -/
lemma traceGap_six (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U = 6) : traceGap σ = 1 := by
  let := isIrreducible_of_finrank_six σ hq hd
  obtain ⟨a, ⟨e⟩⟩ := exists_constituent_equiv σ hq (by omega)
  unfold traceGap
  rw [char_iso e]
  exact constituent_trace_gap a

/-- The two constituent contributions cancel on every twelve-dimensional quotient. -/
lemma traceGap_twelve (hq : CentralQuadratic σ)
    (hd : Module.finrank (ZMod 2) U = 12) : traceGap σ = 0 := by
  obtain ⟨N, a, b, ⟨ea⟩, ⟨eb⟩⟩ := exists_constituent_filtration σ hq hd
  rw [traceGap_add σ N]
  unfold traceGap
  rw [char_iso ea, char_iso eb, constituent_trace_gap, constituent_trace_gap]
  decide

variable (ρ : Representation (ZMod 2) M22TripleCover U)

omit [FiniteDimensional (ZMod 2) U] in
/-- Full-group conjugacy forces the trace difference of a point restriction to vanish. -/
lemma traceGap_pointAction : traceGap (pointAction ρ) = 0 := by
  have hw (j : Fin 4) : (pointAction ρ).character (classicalWord j) =
      ρ.character (localWord j) := by
    rw [← pointStabilizerEquiv_localWord]
    change LinearMap.trace (ZMod 2) U
      (ρ ((pointStabilizerEquiv.symm (pointStabilizerEquiv (localWord j)) :
        pointStabilizer) : M22TripleCover)) = _
    rw [pointStabilizerEquiv.symm_apply_apply]
    rfl
  unfold traceGap
  rw [hw, hw]
  change ρ.character wordT + ρ.character (coreGeneratorB * wordT * coreGeneratorB) = 0
  have hb : coreGeneratorB⁻¹ = coreGeneratorB := inv_eq_of_mul_eq_one_left generatorB_sq
  have ht : ρ.character (coreGeneratorB * wordT * coreGeneratorB) = ρ.character wordT := by
    simpa only [hb] using ρ.char_conj wordT coreGeneratorB
  rw [ht]
  exact CharTwo.add_self_eq_zero _

/-- In binary degree eighteen the entire actual point restriction is simple. -/
theorem pointAction_isIrreducible_of_finrank_eighteen [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) U = 18) :
    (pointAction ρ).IsIrreducible := by
  let : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) U)
  obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (pointAction ρ)
  let := hN
  rcases point_simple_submodule_finrank ρ hf (by omega) N with hn | hn
  · have hq := pointAction_centralQuadratic ρ hf
    have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
    have hquot : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = 12 := by omega
    have ht := traceGap_add (pointAction ρ) N
    rw [traceGap_pointAction, traceGap_six N.toRepresentation
      (centralQuadratic_subrepresentation _ hq N) hn,
      traceGap_twelve N.quotientRepresentation (centralQuadratic_quotient _ hq N) hquot] at ht
    norm_num at ht
  · have htop : N = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.eq_top_of_finrank_eq (hn.trans hd.symm)
    have ha := (Subrepresentation.irreducible_iff_isAtom N).mp hN
    rw [htop] at ha
    exact isSimpleOrder_iff_isAtom_top.mpr ha

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
