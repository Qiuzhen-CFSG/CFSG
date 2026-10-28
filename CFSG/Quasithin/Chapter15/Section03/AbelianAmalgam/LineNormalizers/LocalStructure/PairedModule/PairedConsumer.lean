module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Decomposition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Relative
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.PairedSection

/-!
# The paired section in the relative line normalizer

Set `H = G_E`, and view the original `U` and `E` as subgroups of `H`.
Elementary abelianness of `U` and `E ≤ V ≤ U` place `U` inside `H`;
its conjugate-span definition proves normality there. The actual subgroup
equivalence transports the paired projection to `Additive U_H`.

For any surjective map from `H` with kernel `C_H(U_H)`, the resulting
`Offenders.PairedSection` has exactly `E_H` as kernel and the specified
diagonal `C_E` action. Thus the offender consumer can use the genuine
faithful conjugation quotient when the source assembly supplies it.
No ambient normality of `E` or recognition of the centralizer-image factor
is assumed. The marked decomposition and `ActionData` remain explicit inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1153,
PDF p.1170, proof of 15.3.67 before the temporary replacement.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
open Descent.QuotientIdentification
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]
variable (hEV : E ≤ V)

include hEV in
/-- The elementary span lies in the line normalizer because it centralizes the line. -/
lemma elementary_span_le_normalizer : lineV V E ≤ lineNormalizer E := by
  have hEU : E ≤ lineV V E := hEV.trans (le_conjugateSpanBy V (lineNormalizer E))
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    ((centralizer_le hEU).trans (centralizer_le_normalizer (E : Set G)))

include hEV in
/-- Normality is relative to the original line normalizer. -/
lemma relativeSpan_normal : ((lineV V E).subgroupOf (lineNormalizer E)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (elementary_span_le_normalizer V E hEV)).mpr
    (le_normalizer_conjugateSpanBy V (lineNormalizer E))

include hEV in
/-- The actual relative subgroup inherits elementary abelianness. -/
lemma relativeSpan_elementary :
    IsElementaryAbelian 2 ((lineV V E).subgroupOf (lineNormalizer E)) :=
  IsElementaryAbelian.subgroupOf (elementary_span_le_normalizer V E hEV)

section Transport
variable [IsElementaryAbelian 2 ((lineV V E).subgroupOf (lineNormalizer E))]

/-- The binary form of the actual subgroup equivalence `U_H ≃ U`. -/
noncomputable def relativeSpanEquiv :
    Additive ((lineV V E).subgroupOf (lineNormalizer E)) ≃ₗ[ZMod 2] Additive (lineV V E) :=
  LinearEquiv.ofBijective
    ((subgroupOfEquivOfLe (elementary_span_le_normalizer V E hEV)).toMonoidHom.toAdditive.toZModLinearMap 2)
    (subgroupOfEquivOfLe (elementary_span_le_normalizer V E hEV)).bijective

lemma relativeSpanEquiv_apply (v : Additive ((lineV V E).subgroupOf (lineNormalizer E))) :
    ((relativeSpanEquiv V E hEV v).toMul : G) = ((v.toMul : lineNormalizer E) : G) := rfl

variable {Y T : Subgroup G} (d : MarkedDecomposition Y T E)
variable (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) (a : ActionData V E d)

/-- Transport of the original paired projection to the relative subgroup. -/
noncomputable def relativePairedProjection :
    Additive ((lineV V E).subgroupOf (lineNormalizer E)) →ₗ[ZMod 2]
      fixedImage V E d.tau × fixedImage V E d.tau :=
  (pairedProjection V E d hcomm a).comp (relativeSpanEquiv V E hEV).toLinearMap

lemma relativePairedProjection_surjective :
    Function.Surjective (relativePairedProjection V E hEV d hcomm a) :=
  (pairedProjection_surjective V E d hcomm a).comp (relativeSpanEquiv V E hEV).surjective

/-- The transported projection kills precisely `E_H` inside `U_H`. -/
lemma relativePairedProjection_ker :
    (relativePairedProjection V E hEV d hcomm a).ker =
      Representation.NormalElementaryQuotient.subspace
        ((lineV V E).subgroupOf (lineNormalizer E))
        ((E.subgroupOf (lineNormalizer E)).subgroupOf
          ((lineV V E).subgroupOf (lineNormalizer E))) := by
  ext v
  rw [LinearMap.mem_ker]
  change pairedProjection V E d hcomm a (relativeSpanEquiv V E hEV v) = 0 ↔ _
  rw [← LinearMap.mem_ker, pairedProjection_ker]
  rfl

variable [((lineV V E).subgroupOf (lineNormalizer E)).Normal]
variable {K : Type*} [Group K]
variable (f : lineNormalizer E →* K) (hf : Function.Surjective f)
variable (hker : f.ker = centralizer (((lineV V E).subgroupOf (lineNormalizer E)) : Set (lineNormalizer E)))

/-- The subgroup equivalence preserves the faithful conjugation action. -/
lemma relativeSpanEquiv_action (g : lineNormalizer E)
    (v : Additive ((lineV V E).subgroupOf (lineNormalizer E))) :
    relativeSpanEquiv V E hEV
      (Representation.NormalElementaryQuotient.representation
        ((lineV V E).subgroupOf (lineNormalizer E)) f hf hker (f g) v) =
      spanRepresentation V E g (relativeSpanEquiv V E hEV v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [relativeSpanEquiv_apply, spanRepresentation_apply, relativeSpanEquiv_apply,
    Representation.NormalElementaryQuotient.representation_apply]
  rfl

/-- The transported map has the diagonal centralizer action required by the offender API. -/
lemma relativePairedProjection_equivariant (g : lineNormalizer E)
    (hg : g ∈ (lineC E).subgroupOf (lineNormalizer E))
    (v : Additive ((lineV V E).subgroupOf (lineNormalizer E))) :
    relativePairedProjection V E hEV d hcomm a
      (Representation.NormalElementaryQuotient.representation
        ((lineV V E).subgroupOf (lineNormalizer E)) f hf hker (f g) v) =
      (sigma V E d hcomm a (QuotientGroup.mk' (pCore 2 (lineNormalizer E)) g)
        (relativePairedProjection V E hEV d hcomm a v).1,
       sigma V E d hcomm a (QuotientGroup.mk' (pCore 2 (lineNormalizer E)) g)
        (relativePairedProjection V E hEV d hcomm a v).2) := by
  let c : centralizer (E : Set G) := ⟨g, hg⟩
  have hc : inclusion (centralizer_le_normalizer (E : Set G)) c = g := Subtype.ext rfl
  change pairedProjection V E d hcomm a (relativeSpanEquiv V E hEV
    (Representation.NormalElementaryQuotient.representation
      ((lineV V E).subgroupOf (lineNormalizer E)) f hf hker (f g) v)) = _
  rw [relativeSpanEquiv_action V E hEV f hf hker]
  have he := pairedProjection_centralizer V E d hcomm a c (relativeSpanEquiv V E hEV v)
  rw [hc] at he
  exact he
end Transport

variable {Y T : Subgroup G} (d : MarkedDecomposition Y T E)
variable (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E) (a : ActionData V E d)
variable {K : Type*} [Group K]
variable (f : lineNormalizer E →* K) (hf : Function.Surjective f)
variable (hker : f.ker = centralizer (((lineV V E).subgroupOf (lineNormalizer E)) : Set (lineNormalizer E)))

/-- The paired offender section, constructed from the original marked action. -/
noncomputable def pairedSection :
    letI := relativeSpan_normal V E hEV
    letI := relativeSpan_elementary V E hEV
    Offenders.PairedSection
      ((lineV V E).subgroupOf (lineNormalizer E)) (E.subgroupOf (lineNormalizer E))
      ((lineC E).subgroupOf (lineNormalizer E)) (pCore 2 (lineNormalizer E))
      f hf hker (sigma V E d hcomm a) := by
  letI := relativeSpan_normal V E hEV
  letI := relativeSpan_elementary V E hEV
  exact {
    line_le := subgroupOf_mono _ (hEV.trans (le_conjugateSpanBy V (lineNormalizer E)))
    projection := relativePairedProjection V E hEV d hcomm a
    surjective := relativePairedProjection_surjective V E hEV d hcomm a
    kernel_eq := relativePairedProjection_ker V E hEV d hcomm a
    equivariant := relativePairedProjection_equivariant V E hEV d hcomm a f hf hker }
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
