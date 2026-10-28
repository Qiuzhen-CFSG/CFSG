module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Marked
/-!
# Original inputs for the marked geometry construction

This packet contains preceding local conclusions on the original groups only.
The marked decomposition is the original `G_E/Q_E` decomposition, with its
actual centralizer image. The source choice of τ is retained in `P_c` outside
`S_E=C_T(E)`. For the source application, `P_c=O₂(M_c)∩G_E`; only its
containment in `T_E` and normalization by `C_G(E)` are needed here.

No temporary quotient decomposition, fixed-space decomposition, lifting result,
operator identity on U, or transvection conclusion occurs in these inputs.
The short inheritance adapters reuse the original-action kernel proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66 and
proof of 15.3.67, printed pp.1152–1154, PDF pp.1169–1171.
-/

@[expose] public section
open Subgroup Stellmacher OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G]

/-- Genuine original local inputs, with the same marked τ throughout. -/
structure OriginalData (Y T V M E Pc : Subgroup G) where
  action : NaturalAction V M
  Y_le : Y ≤ M
  line_le : E ≤ V
  line_card : Nat.card E = 4
  singular : ∀ e : E, action.singular ⟨e, line_le e.property⟩
  residual_image : actionImage action Y = pResidual 2 IsometryGroup
  residual_kernel : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G)
  residual_normal : lineNormalizer E ≤ normalizer (lineY Y E : Set G)
  module_le_sylow : V ≤ lineT T E
  sylow_le_M : lineT T E ≤ M
  sylow : Sylow 2 (lineNormalizer E)
  sylow_image : (sylow : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E
  core_le_kernel : lineQ E ≤ Descent.sectionKernel V E
  local_core : (lineY Y E ⊔ lineT T E).pCoreIn 2 ≤ T ⊓ centralizer (E : Set G)
  seed_commutator : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E
  span_elementary : IsElementaryAbelian 2 (lineV V E)
  span_le_sylow : lineV V E ≤ lineT T E
  residual_span : lineV V E = ⁅lineV V E, lineY Y E⁆
  sylow_action_elementary : IsElementaryAbelian 2
    (V.normalizerMonoidHom.comp (inclusion (sylow_le_M.trans action.normalizes))).range
  marked : Descent.QuotientIdentification.MarkedDecomposition Y T E
  product : (lineNormalizer E : Set G) =
    ((lineY Y E ⊔ zpowers marked.tau : Subgroup G) : Set G) * (centralizer (E : Set G) : Set G)
  Pc_le_sylow : Pc ≤ lineT T E
  Pc_normalized : centralizer (E : Set G) ≤ normalizer (Pc : Set G)
  tau_mem_Pc : marked.tau ∈ Pc
  tau_outside : marked.tau ∉ T ⊓ centralizer (E : Set G)

namespace OriginalData
variable [Finite G] {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

/-- The marked elements, product and span inherit to the temporary normalizer. -/
theorem inherited (d : OriginalData Y T V M E Pc) :
    d.marked.tau ∈ temporaryLineNormalizer T V E ∧
      lineY Y E ≤ temporaryLineNormalizer T V E ∧
      (temporaryLineNormalizer T V E : Set G) =
        ((lineY Y E ⊔ zpowers d.marked.tau : Subgroup G) : Set G) *
          (temporaryCentralizer T V E : Set G) ∧
      lineV V E = conjugateSpanBy V (temporaryCentralizer T V E) :=
  marked_group_inheritance d.action Y T E d.Y_le d.line_le d.line_card d.singular
    d.residual_image d.residual_kernel d.residual_normal d.sylow d.sylow_image
    d.core_le_kernel d.marked.tau d.marked.tau_mem (d.sylow_le_M d.marked.tau_mem) d.product

/-- The original marked τ, regarded as an element of H. -/
abbrev tau (d : OriginalData Y T V M E Pc) : temporaryLineNormalizer T V E :=
  ⟨d.marked.tau, d.inherited.1⟩

/-- An original residual element, regarded as an element of H. -/
abbrev residualElement (d : OriginalData Y T V M E Pc) (y : G) (hy : y ∈ lineY Y E) :
    temporaryLineNormalizer T V E := ⟨y, d.inherited.2.1 hy⟩

omit [Finite G] in
/-- The original module lies in the temporary normalizer. -/
theorem span_le_temporary (d : OriginalData Y T V M E Pc) :
    lineV V E ≤ temporaryLineNormalizer T V E :=
  d.span_le_sylow.trans (lineT_le_temporary T V E d.line_le)


omit [Finite G] [IsMulCommutative V] in
/-- Normality of the original module in the temporary group. -/
theorem module_normal (d : OriginalData Y T V M E Pc) :
    ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal := by
  let := d.span_elementary
  exact lineV_normal_in_temporary T V E d.span_le_sylow

omit [Finite G] in
/-- Elementary abelianness passes to the intrinsic module in H. -/
theorem module_elementary (d : OriginalData Y T V M E Pc) :
    IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) := by
  let := d.span_elementary
  exact IsElementaryAbelian.subgroupOf d.span_le_temporary

omit [Finite G] in
/-- The actual denominator E is normal in H. -/
theorem line_normal (d : OriginalData Y T V M E Pc) :
    (E.subgroupOf (temporaryLineNormalizer T V E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    (d.line_le.trans (d.module_le_sylow.trans (lineT_le_temporary T V E d.line_le)))).mpr
      inf_le_left

end OriginalData
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry
