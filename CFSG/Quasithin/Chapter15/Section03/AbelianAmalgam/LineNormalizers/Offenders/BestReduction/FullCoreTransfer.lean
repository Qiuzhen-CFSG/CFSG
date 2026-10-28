module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Generation
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Transvections.Action

/-!
# Full-core structure of the temporary Thompson image

In the temporary group H, the marked line E is normal and its centralizer C
is normal. Conjugation preserves the maximum elementary family of C, so its
Thompson subgroup and its image I in H/Q are normal. Here Q is the FULL
relative two-core: `localCore_eq_pCore` proves the equality on the literal
subgroup of H. Pulling back normal two-subgroups proves O₂(H/Q) = 1, and
characteristicity of O₂(I) then gives O₂(I) = 1. The original local data also
identify O₂(C), mapped into H, with this same Q.

For the faithful action on the original U, core doubling excludes every
nontrivial best offender contained in the core action image. This does not
exclude intersections of best offenders with that image.

These structural results do not yet transfer best-offender generation from U
to the marked first summand of U/E. In particular, no splitting of the
central extension, full-centralizer containment in Q, or replacement of I by
a proper normal offender subgroup is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154; Definitions B.1.2–3, printed p.68, and the
hypotheses of B.5.1, printed p.99.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
open Replacement.Transvections
variable {G : Type*} [Group G]

/-- The literal temporary centralizer, considered as a subgroup of H. -/
abbrev localCentralizer (T V E : Subgroup G) :=
  (temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E)

/-- Restricting the ambient temporary core to H recovers its entire two-core. -/
theorem localCore_eq_pCore (T V E : Subgroup G) :
    localCore T V E = pCore 2 (temporaryLineNormalizer T V E) := by
  exact comap_map_eq_self_of_injective (temporaryLineNormalizer T V E).subtype_injective _

/-- Normality uses the relative temporary core, not the original `lineQ`. -/
instance localCore_normal (T V E : Subgroup G) : (localCore T V E).Normal :=
  temporaryCore_normal T V E

/-- The same actor I required by the first-summand generation problem. -/
noncomputable abbrev thompsonImage (T V E : Subgroup G) :=
  (Stellmacher.elementaryAbelianMaxJ (localCentralizer T V E)).map
    (QuotientGroup.mk' (localCore T V E))

/-- H normalizes the marked line even before its containment in H is supplied. -/
theorem localLine_normal (T V E : Subgroup G) : (localLine T V E).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_left

/-- Under the actual line containment this is exactly C_H(E_H). -/
theorem localCentralizer_eq (T V E : Subgroup G)
    (hEH : E ≤ temporaryLineNormalizer T V E) :
    localCentralizer T V E = centralizer (localLine T V E : Set (temporaryLineNormalizer T V E)) := by
  ext x
  constructor
  · intro hx y hy
    exact Subtype.ext (hx.2 y hy)
  · intro hx
    refine ⟨x.property, fun e he => ?_⟩
    exact congrArg Subtype.val (hx ⟨e, hEH he⟩ he)

/-- The line centralizer is normal in the temporary group. -/
theorem localCentralizer_normal (T V E : Subgroup G)
    (hEH : E ≤ temporaryLineNormalizer T V E) : (localCentralizer T V E).Normal := by
  let _ := localLine_normal T V E
  rw [localCentralizer_eq T V E hEH]
  infer_instance

private theorem thompson_normal (C : Subgroup G) [C.Normal] :
    (Stellmacher.elementaryAbelianMaxJ C).Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  exact (Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj g) C).symm.trans
    (congrArg Stellmacher.elementaryAbelianMaxJ
      (normal_iff_map_conj_eq.mp (inferInstance : C.Normal) g))

/-- Maximum-family invariance makes the actual Thompson image normal in H/Q. -/
theorem thompsonImage_normal (T V E : Subgroup G)
    (hEH : E ≤ temporaryLineNormalizer T V E) : (thompsonImage T V E).Normal := by
  let _ := localCentralizer_normal T V E hEH
  let _ := thompson_normal (localCentralizer T V E)
  exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

/-- Factoring out the full temporary core leaves no normal two-subgroup. -/
theorem quotient_twoCore_eq_bot (T V E : Subgroup G) :
    pCore 2 ((temporaryLineNormalizer T V E) ⧸ localCore T V E) = ⊥ := by
  let q := QuotientGroup.mk' (localCore T V E)
  have hp : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk', localCore_eq_pCore]
    exact pCore_isPGroup
  have hle : (pCore 2 ((temporaryLineNormalizer T V E) ⧸ localCore T V E)).comap q ≤ q.ker := by
    have h : (pCore 2 ((temporaryLineNormalizer T V E) ⧸ localCore T V E)).comap q ≤
        pCore 2 (temporaryLineNormalizer T V E) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_ker_isPGroup q hp⟩
    exact h.trans_eq ((localCore_eq_pCore T V E).symm.trans (QuotientGroup.ker_mk' _).symm)
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (localCore T V E) x
  exact hle hx

private theorem normal_twoCore_eq_bot (C : Subgroup G) [C.Normal]
    (hG : pCore 2 G = ⊥) : pCore 2 C = ⊥ := by
  have hn : ((pCore 2 C).map C.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hle : (pCore 2 C).map C.subtype ≤ pCore 2 G :=
    le_sSup ⟨hn, pCore_isPGroup.map C.subtype⟩
  have he : (pCore 2 C).map C.subtype = ⊥ := bot_unique (hG ▸ hle)
  exact ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp he

/-- The same Thompson image has trivial intrinsic two-core. -/
theorem thompsonImage_twoCore_eq_bot (T V E : Subgroup G)
    (hEH : E ≤ temporaryLineNormalizer T V E) : pCore 2 (thompsonImage T V E) = ⊥ := by
  let _ := thompsonImage_normal T V E hEH
  exact normal_twoCore_eq_bot _ (quotient_twoCore_eq_bot T V E)
/-- The source line and span containments supply the line inside H. -/
theorem line_le_temporary (T V E : Subgroup G) [IsMulCommutative V] (hEV : E ≤ V)
    (hUT : lineV V E ≤ lineT T E) : E ≤ temporaryLineNormalizer T V E :=
  hEV.trans ((le_conjugateSpanBy V (lineNormalizer E)).trans
    (hUT.trans (Replacement.lineT_le_temporary T V E hEV)))

variable [Finite G]

/-- The core-centralization proved from the original local data identifies O₂(C) with Q. -/
theorem localCentralizer_twoCore_eq (Y T V E : Subgroup G) [IsMulCommutative V]
    (d : TemporaryData Y T V E) :
    (pCore 2 (localCentralizer T V E)).map (localCentralizer T V E).subtype =
      localCore T V E := by
  let C := localCentralizer T V E
  let Q := localCore T V E
  let _ : C.Normal := localCentralizer_normal T V E
    (line_le_temporary T V E d.line_le d.span_le_sylow)
  have hQC : Q ≤ C := fun q hq =>
    ⟨q.property, d.core_centralizes_line Y T V E hq⟩
  have hn : ((pCore 2 C).map C.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (pCore 2 C).map C.subtype ≤ pCore 2 (temporaryLineNormalizer T V E) :=
    le_sSup ⟨hn, pCore_isPGroup.map C.subtype⟩
  apply le_antisymm (hle.trans_eq (localCore_eq_pCore T V E).symm)
  have hp : IsPGroup 2 Q := by
    change IsPGroup 2 (localCore T V E)
    rw [localCore_eq_pCore]
    exact pCore_isPGroup
  have hlocal : Q.subgroupOf C ≤ pCore 2 C :=
    le_sSup ⟨inferInstance, hp.comap_subtype⟩
  exact (map_subgroupOf_eq_of_le hQC).symm.le.trans (map_mono hlocal)

open Representation.BinaryOffender

/-- The all-subgroups doubling identity excludes best offenders wholly in the faithful core image. -/
theorem no_bestOffender_in_core_image
    {K : Type*} [Group K] (Y T V E : Subgroup G) [IsMulCommutative V]
    [(Replacement.Transvections.localSpan T V E).Normal] [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
    (f : temporaryLineNormalizer T V E →* K) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
    (d : TemporaryData Y T V E)
    (geom : FixedGeometry (localRepresentation T V E f hf hker)
      (f d.tau) (f d.conjugator) (localLineSpace T V E))
    (A : Subgroup K) (hAQ : A ≤ (localCore T V E).map f) :
    ¬ IsBestOffender (localRepresentation T V E f hf hker) A := by
  let _ : Finite K := Finite.of_surjective f hf
  intro hA
  have ho := hA.isOffender (localRepresentation T V E f hf hker)
  have hr := temporary_core_fixedCodim Y T V E f hf hker d geom A hAQ
  have hp := hA.1.rank_pos
  have hle := ho.2
  rw [hr] at hle
  omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
