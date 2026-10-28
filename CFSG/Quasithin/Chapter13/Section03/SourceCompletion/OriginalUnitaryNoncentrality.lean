module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Applicability
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ReductionA
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ResidualControl
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.SourceEscape
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FullActionReduction
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.OffenderImages
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.BaumannCore
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.PushingUp
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.InitialModule
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ConjugateGeometry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.CoreProduct
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.BaumannEndpoint

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.Complete
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.FixedModuleRowsG2Source

/-!
# Original-source unitary reductions through Baumann escape

The genuine Hypothesis 13.3.1, selected component, original chosen module
and natural action establish the fixed-point condition of 13.3.13 and
reduction (a). A cubic lift in the literal plane residual makes the
conjugate centralizing-residual intersection a two-group, proving the
solvability and odd-rank conclusions of (b).

The correct derived second parabolic supplies the point residual's cubic
core quotient and nontrivial two-core action on the seed. These discharge
(c), feed the source Fitting argument (d), and construct the actual moved
component. Its faithful-local and maximal-normalizer geometry gives
(e)--(f), including escape of the literal plane residual. The actual
Chapter 3 theorem also gives generation by the Thompson commutator.

Seed generation and the original fixed-module clause now prove reduction
(g). The diagonal rank sieve selects the A₅ quotient, and an original
chosen module gives the literal Baumann identity and normalizer escape.
The earlier universal 12.2 and 13.3.2 statements and the original
plane-centralizer statement remain explicit. In the branch where LT has
the same natural action image as L, the no-offender calculation proves
the Baumann upper bound, plane noncentrality, and its exclusion application.
The full G₂(2)-image branch is now complete as well. Normalizer escape
forces the marked root-eight Thompson and Baumann images. Baumann's
argument identifies the product two-core with the Baumann centralizer of
V. The literal exceptional MS2(b) pair satisfies the whole-core Frattini
bound by the completed critical-pair argument, so L is a genuine G₂ block.
The page-888 conjugate and core-product calculation makes that core
elementary; root-eight lifting and Sylow containment then prove the original
Baumann-normalizer bound without assuming plane centrality.

That earlier bound contradicts the original diagonal-A₅ escape and proves
the exact plane noncentrality premise. Both original parabolic control and
the unitary exclusion consumer now receive this proved premise. The earlier
universal 12.2/13.3.2 statements and independent plane-centralizer and
odd-normalizer statements retain their final discharge in qt-d-13316-source.
Source: Aschbacher--Smith, 13.3.13--14, printed pp.890--893.

The guarded 13.3.2 row sieve is also re-exported here. The completed
moved-family argument and the original seven-dimensional hyperplane-centralizer
theorem 12.4.8 discharge both G₂ inputs. Earlier structural and module
inputs and rank-one exits remain explicit in that source application.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source inputs discharge both fixed-point applicability and
reduction (a), without added flag positions or local normalizer hypotheses. -/
theorem unitary_original_noncentrality_reduction_a
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (hc : ⁅D.QH,B⁆ = ⊥) :
    D.V ⊓ centralizer (D.L : Set G) = ⊥ ∧
      D.UH = conjugateSpanBy B D.H ∧
      D.UH ≤ Stellmacher.omegaOneCenterAmbient D.QH := by
  obtain ⟨hTN,hNL⟩ := unitary_original_module_normalizers h hmax eL chosen structural
  exact ⟨unitary_component_fixed_points_eq_bot D.L e E0 he0,
    unitary_flag_reduction_a D h chosen hTN hNL e E0 he0 hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull hc⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
