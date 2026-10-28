module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.DualExtensions.G2Cocycles

/-!
# A root-pair reduction for the nonbinary G₂ trace obstruction

An octonion fixed modulo scalars by the long root A(1) has seventh
coordinate zero. Fixation modulo scalars by the short root C(1) then
forces its trace to vanish. Conjugation transports this calculation to
the actual full octonion automorphism group.

Every offender contains a best offender. Thus the concrete placement
`G2BestOffenderRootPair` suffices for `G2TraceDetection`, and the last
theorem applies this reduction to the original moved section, with its
literal action, offender generation, ranks and ratio. The coordinate
argument works over every field of characteristic two, including F₂.

The placement premise remains unproved here. The source supplies it by
identifying best offenders with conjugates of A₁ = Z₁ × R in B.4.6(13),
where Z₁ and R are the specified long-root plane and short-root group.
The separate B.4.6 owner must identify those groups in these coordinates.
Consequently this module does not yet establish `nonbinary_traceDetection`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.6(3),
(6), (13), printed pp.88–90; I.1.7(b), pp.408–409; B.5.1(5), pp.102–103.
The root coordinates are the existing licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
namespace NonbinaryTrace

variable {k : Type*} [Field k] [CharP k 2]

/-- The literal long and short root pair detects trace on the eight-dimensional
octonion space modulo its scalar identity line. -/
theorem trace_eq_zero_of_rootPair (x : Carrier k)
    (hA : ∃ c : k, c • unit = (rootA 1).val x - x)
    (hC : ∃ c : k, c • unit = (rootC 1).val x - x) : trace x = 0 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨c, hc⟩ := hC
  have h7 : x 7 = 0 := by
    have h := congrFun ha 1
    simpa [unit, rootA, rootAEquiv, rootALinear, rootAApply] using h.symm
  have h := congrFun hc 0
  simp [unit, rootC, rootCEquiv, rootCLinear, rootCApply, h7] at h
  simp only [trace, ← CharTwo.sub_eq_add]
  linear_combination h

omit [CharP k 2] in
private theorem scalarDisplacement_of_conjugate (g a : Model k) (x : Carrier k)
    (h : ∃ c : k, c • unit = (g * a * g⁻¹).val x - x) :
    ∃ c : k, c • unit = a.val (g.val.symm x) - g.val.symm x := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have he := congrArg (fun y => (g⁻¹).val y) hc
  simp only [map_sub, automorphism_scalar] at he
  change c • unit = g.val.symm (g.val (a.val (g.val.symm x))) - g.val.symm x at he
  simpa only [LinearEquiv.symm_apply_apply] using he

/-- Trace detection is transported through the actual octonion action, with
the same conjugator on the two specified root elements. -/
theorem trace_eq_zero_of_conjugate_rootPair (g : Model k) (x : Carrier k)
    (hA : ∃ c : k, c • unit = (g * rootA 1 * g⁻¹).val x - x)
    (hC : ∃ c : k, c • unit = (g * rootC 1 * g⁻¹).val x - x) : trace x = 0 := by
  have ht := trace_eq_zero_of_rootPair (g.val.symm x)
    (scalarDisplacement_of_conjugate g (rootA 1) x hA)
    (scalarDisplacement_of_conjugate g (rootC 1) x hC)
  exact (automorphism_trace (g⁻¹) x).symm.trans ht

end NonbinaryTrace

/-- The concrete fragment of B.4.6(13) needed for the trace argument.
This is an explicit outstanding placement premise, not a proved classification:
every best offender contains the specified pair with a common conjugator. -/
def G2BestOffenderRootPair (F : BinaryField) : Prop :=
  ∀ A : Subgroup (Model F.Carrier), IsBestOffender (binaryG2 F) A →
    ∃ g : Model F.Carrier,
      g * rootA 1 * g⁻¹ ∈ A ∧ g * rootC 1 * g⁻¹ ∈ A

/-- The root placement for best offenders implies the exact geometric
contract of `G2Cocycles`, also for offenders that were not assumed best. -/
theorem g2_traceDetection_of_bestOffender_rootPair (F : BinaryField)
    (hplace : G2BestOffenderRootPair F) : G2TraceDetection F := by
  let : FiniteDimensional F.Carrier (Atlas.G2.Natural.Space F.Carrier) :=
    FiniteDimensional.of_finrank_pos (by rw [Atlas.G2.Natural.finrank_space]; decide)
  intro A hA _hr x hx
  obtain ⟨B, hBA, hB⟩ := hA.exists_bestOffender (binaryG2 F)
  obtain ⟨g, hgA, hgC⟩ := hplace B hB
  exact NonbinaryTrace.trace_eq_zero_of_conjugate_rootPair g x
    (hx _ (hBA hgA)) (hx _ (hBA hgC))

universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Application to the original B.5.1 moved section. The sole new model
premise is the displayed root placement, whose producer is B.4.6(13).
This conditional result does not discharge that outstanding source clause. -/
theorem g2_supplement_of_bestOffender_rootPair [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (F : BinaryField) (hg : offenderSubgroup s.action = L)
    (e : ActionEquiv (s.action.comp L.subtype) (binaryG2 F))
    (hoff : ∀ A, IsBestOffender s.action A → rank A = 3 * F.degree)
    (hq : quadraticRatio s.action = 1) (hplace : G2BestOffenderRootPair F) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ :=
  g2_supplement_of_trace h s F hg e hoff hq
    (g2_traceDetection_of_bestOffender_rootPair F hplace)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.DualExtensions
