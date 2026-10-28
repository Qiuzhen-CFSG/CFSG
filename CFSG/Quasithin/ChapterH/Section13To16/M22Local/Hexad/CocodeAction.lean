module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.CocodeAction.SixPointModel
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.CocodeAction.Transvections
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Conditional M22 hexad cocode action clauses

For native M22 and for the literal setwise pair stabilizer, pair classes on
the compatible source hexad detect its intrinsic kernel. Exact fixed-vector
lifting then excludes shears into the removed pair line and descends the M24
pointwise-centralizer theorem. Group conjugacy transports the calculation to
source two-central involutions, defined by an actual Sylow-center witness.

The final inner and outer action theorems combine this calculation with the
actual A6 and S6 deleted-module identifications, the noncyclic fixed-space
clause, and the full prescribed transvection image. Their kernel isomorphism
with the literal quotient W/U respects the induced stabilizer/kernel action.
The six-point API also supplies the equivariant dual identification with the
orthogonal pair perpendicular; it does not descend a quadratic form through
the nonsingular pair line.

Only the earlier M24 cocode statements and H.14 kernel, displacement and
conjugacy facts remain inputs. This completes the conditional action transfer;
the chapter parent owns discharge of those earlier inputs and final assembly
with the independently developed code flag.

Source: Aschbacher--Smith, H.15.2(2),(5),(6), printed pp.398--399,
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open MathieuCode MathieuCode.Hexad MathieuCode.Hexad.CocodeAction
open Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad

/-- The common fixed space detects the actual outer hexad kernel. -/
theorem outer_commonFixed_pointwiseCentralizer
    (h : OuterRestrictionInput m22SourceOctad) :
    subspaceKernel m22OuterCocodeRepresentation
      (fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) ⊤ =
        m22OuterHexadKernel m22SourceOctad := by
  simpa only [quotientRepresentation, MonoidHom.comp_id] using
    fixedSpace_pointwiseKernel (f := MonoidHom.id m22PairStabilizer)
      (K := m22OuterHexadKernel m22SourceOctad) (O := m22SourceOctad)
      h.injective h.kernel_image m22Pair_le_sourceOctad

/-- The same statement for the original native M22 representation. -/
theorem inner_commonFixed_pointwiseCentralizer
    (h : InnerRestrictionInput m22SourceOctad) :
    subspaceKernel m22CocodeRepresentation
      (fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) ⊤ =
        m22InnerHexadKernel m22SourceOctad :=
  fixedSpace_pointwiseKernel (f := m22ToPairStabilizer)
    (K := m22InnerHexadKernel m22SourceOctad) (O := m22SourceOctad)
    h.injective h.kernel_image m22Pair_le_sourceOctad

/-- H.15.2(5) for M=L, conditional on the specified earlier M24 theorem and
genuine H.14 class coverage in native M22. -/
theorem inner_twoCentral_pointwiseCentralizer
    (h : InnerRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hc : AmbientCentralizerInput m22SourceOctad)
    (hfusion : ∀ z : Sporadic.Mathieu.M22, IsSylowCentralInvolution z →
      ∃ a ∈ m22InnerHexadKernel m22SourceOctad, a ≠ 1 ∧ IsConj a z)
    (z : Sporadic.Mathieu.M22) (hz : IsSylowCentralInvolution z) :
    subspaceKernel m22CocodeRepresentation
      (fixedSpace m22CocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z :=
  pointwiseCentralizer_of_conjugate_kernel h m22Pair_le_sourceOctad
    h24.displacement hc z (hfusion z hz)

/-- H.15.2(5) for the literal setwise pair group. In particular, the pointwise
centralizer is taken in the full outer ambient group, not its inner subgroup. -/
theorem outer_twoCentral_pointwiseCentralizer
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hc : AmbientCentralizerInput m22SourceOctad)
    (hfusion : ∀ z : m22PairStabilizer, IsSylowCentralInvolution z →
      ∃ a ∈ m22OuterHexadKernel m22SourceOctad, a ≠ 1 ∧ IsConj a z)
    (z : m22PairStabilizer) (hz : IsSylowCentralInvolution z) :
    subspaceKernel m22OuterCocodeRepresentation
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  simpa only [quotientRepresentation, MonoidHom.comp_id] using
    pointwiseCentralizer_of_conjugate_kernel h m22Pair_le_sourceOctad
      h24.displacement hc z (hfusion z hz)

open MathieuCode.Hexad.CocodeAction.Transvections
open CocodeAction.SixPointModel

/-- Complete conditional cocode action transfer for native M22. The earlier
M24 and H.14 inputs give the actual A6 module, both centralizer clauses,
and every transvection with axis W/U, including its conjugation identification. -/
theorem inner_cocode_action_clauses
    (h : InnerRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hc : AmbientCentralizerInput m22SourceOctad)
    (ht : AmbientTransvectionInput m22SourceOctad)
    (hfusion : ∀ z : Sporadic.Mathieu.M22, IsSylowCentralInvolution z →
      ∃ a ∈ m22InnerHexadKernel m22SourceOctad, a ≠ 1 ∧ IsConj a z) :
    Nonempty ((innerQuotientRepresentation h h24).Equiv
      ((BinaryPermutation.deletedRepresentation Model).comp
        ((alternatingGroup Model).subtype.comp (innerGroupEquiv h).toMonoidHom))) ∧
    Module.finrank (ZMod 2) InnerFixed = 5 ∧
    (∀ z : Sporadic.Mathieu.M22, IsSylowCentralInvolution z →
      subspaceKernel m22CocodeRepresentation
        (fixedSpace m22CocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z) ∧
    (∀ A ≤ m22InnerHexadKernel m22SourceOctad, ¬ IsCyclic A →
      fixedSpace m22CocodeRepresentation A =
        fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) ∧
    (parity h h24.displacement ht).ker =
      axis m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad) ∧
    (∀ T : Module.End (ZMod 2) (M22Cocode ⧸
        fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)),
      (∃ a : m22InnerHexadKernel m22SourceOctad,
        quotientAction h ⟨a.val, kernel_le h a.property⟩ = T) ↔
      ∃ b : axis m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad),
        ∀ x, T x = x + parity h h24.displacement ht x • b.val) ∧
    ∃ e : m22InnerHexadKernel m22SourceOctad ≃* Multiplicative
        ((span m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)) ⧸
          (fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)).comap
            (span m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)).subtype),
      (∀ (a : m22InnerHexadKernel m22SourceOctad)
          (x : M22Cocode ⧸
            fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad)),
        quotientAction h ⟨a.val, kernel_le h a.property⟩ x =
          x + parity h h24.displacement ht x • (spanQuotientEquivAxis (e a).toAdd).val) ∧
      (∀ (g : m22InnerHexadStabilizer m22SourceOctad) (a : m22InnerHexadKernel m22SourceOctad),
        (e (kernelConj _ _ (normalizes h) g a)).toAdd =
          literalAxisQuotientAction h h24.displacement ht (QuotientGroup.mk g) (e a).toAdd) := by
  refine ⟨⟨innerModuleEquiv h h24⟩, (inner_dimensions h h24).2,
    inner_twoCentral_pointwiseCentralizer h h24 hc hfusion, ?_,
    parity_ker h h24.displacement ht, full_image h h24.displacement ht,
    literalTransvectionEquiv h h24.displacement ht,
    literal_kernel_action h h24.displacement ht,
    literalTransvectionEquiv_conjugation h h24.displacement ht⟩
  exact fun A hA hnc => h.noncyclic_fixedSpace h24.displacement h24.noncyclic_fixed A hA hnc

/-- Complete conditional cocode action transfer for the literal setwise pair group.
The earlier M24 and H.14 inputs give the actual S6 module, both centralizer clauses,
and every transvection with axis W/U, including its conjugation identification. -/
theorem outer_cocode_action_clauses
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hc : AmbientCentralizerInput m22SourceOctad)
    (ht : AmbientTransvectionInput m22SourceOctad)
    (hfusion : ∀ z : m22PairStabilizer, IsSylowCentralInvolution z →
      ∃ a ∈ m22OuterHexadKernel m22SourceOctad, a ≠ 1 ∧ IsConj a z) :
    Nonempty ((outerQuotientRepresentation h h24).Equiv
      ((BinaryPermutation.deletedRepresentation Model).comp (outerGroupEquiv h).toMonoidHom)) ∧
    Module.finrank (ZMod 2) OuterFixed = 5 ∧
    (∀ z : m22PairStabilizer, IsSylowCentralInvolution z →
      subspaceKernel m22OuterCocodeRepresentation
        (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z) ∧
    (∀ A ≤ m22OuterHexadKernel m22SourceOctad, ¬ IsCyclic A →
      fixedSpace m22OuterCocodeRepresentation A =
        fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) ∧
    (parity h h24.displacement ht).ker =
      axis (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad) ∧
    (∀ T : Module.End (ZMod 2) (M22Cocode ⧸
        fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)),
      (∃ a : m22OuterHexadKernel m22SourceOctad,
        quotientAction h ⟨a.val, kernel_le h a.property⟩ = T) ↔
      ∃ b : axis (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad),
        ∀ x, T x = x + parity h h24.displacement ht x • b.val) ∧
    ∃ e : m22OuterHexadKernel m22SourceOctad ≃* Multiplicative
        ((span (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)) ⧸
          (fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)).comap
            (span (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)).subtype),
      (∀ (a : m22OuterHexadKernel m22SourceOctad)
          (x : M22Cocode ⧸
            fixed (MonoidHom.id m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad)),
        quotientAction h ⟨a.val, kernel_le h a.property⟩ x =
          x + parity h h24.displacement ht x • (spanQuotientEquivAxis (e a).toAdd).val) ∧
      (∀ (g : m22OuterHexadStabilizer m22SourceOctad) (a : m22OuterHexadKernel m22SourceOctad),
        (e (kernelConj _ _ (normalizes h) g a)).toAdd =
          literalAxisQuotientAction h h24.displacement ht (QuotientGroup.mk g) (e a).toAdd) := by
  refine ⟨⟨outerModuleEquiv h h24⟩, (outer_dimensions h h24).2,
    outer_twoCentral_pointwiseCentralizer h h24 hc hfusion, ?_,
    parity_ker h h24.displacement ht, full_image h h24.displacement ht,
    literalTransvectionEquiv h h24.displacement ht,
    literal_kernel_action h h24.displacement ht,
    literalTransvectionEquiv_conjugation h h24.displacement ht⟩
  exact fun A hA hnc => h.noncyclic_fixedSpace h24.displacement h24.noncyclic_fixed A hA hnc

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad
