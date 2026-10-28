module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking.Action
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking.Node
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking.ComponentImages
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.SelectedSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Local
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MarkedExtension
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
/-!
# The original graph branch and its marked symmetric-eight quotient

The original inner linear exclusions force a noninner Sylow actor on the
intrinsic component quotient. Its image lies outside the component in the
actual local two-core quotient. Conjugation on the self-centralizing A₈
component extends the supplied SL₄(2) marking to the whole S₈ quotient.
Both intrinsic quotient maps and the exceptional linear/alternating marking
remain explicit in the component formula.

Source: Aschbacher–Smith 14.7.48 and 14.7.51, printed pp.1064–1065.
The comparison import retains its ATLAS attribution and license.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open BinaryLinear.InvariantNodeActions
variable {X : Type*} [Group X] [Finite X]

/-- A proper self-centralizing SL₄(2) component image constructs the literal
symmetric-eight quotient, compatibly with every original representative. -/
theorem component_symmetric_eight_marking (C : Subgroup X) (hC : C.IsCComponent) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hc : centralizer (C.map (QuotientGroup.mk' (pCore 2 X)) : Set (X ⧸ pCore 2 X)) = ⊥)
    (hp : C.map (QuotientGroup.mk' (pCore 2 X)) ≠ ⊤) :
    ∃ b : (X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 8),
      (∀ c : C, b (QuotientGroup.mk' (pCore 2 X) c.val) =
        (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
          (Atlas.Order20160A8.sl4TwoEquivPSL (e (QuotientGroup.mk' (pCore 2 C) c)))).val) ∧
      (C.map (QuotientGroup.mk' (pCore 2 X))).map b.toMonoidHom = alternatingGroup (Fin 8) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := C.map q
  let : B.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let eB := (cComponentTwoCoreQuotientEquiv hC).symm.trans
    (e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8))
  let b := symmetricExtension B eB hc hp
  refine ⟨b,?_,symmetricExtension_map B eB hc hp⟩
  intro c
  have hh := symmetricExtension_on_subgroup B eB hc hp (q.subgroupMap C c)
  change symmetricExtension B eB hc hp (q.subgroupMap C c).val = _
  rw [hh]
  change (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
      (Atlas.Order20160A8.sl4TwoEquivPSL (e ((cComponentTwoCoreQuotientEquiv hC).symm
        (q.subgroupMap C c))))).val = _
  exact congrArg (fun x => (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    (Atlas.Order20160A8.sl4TwoEquivPSL (e x))).val)
    ((cComponentTwoCoreQuotientEquiv hC).symm_apply_apply (QuotientGroup.mk' _ c))

open scoped IsMulCommutative
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open GraphMarking
open BinaryLinear BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original local with an SL₄(2) component has its actual marked S₈
quotient. The genuine earlier core-commutator identity supplies the inner
exclusion; neither a graph-action premise nor a quotient marking is assumed. -/
theorem local_four_symmetric_marking_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ b : (I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 8),
      (∀ c : C, b (QuotientGroup.mk' (pCore 2 I) c.val) =
        (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
          (Atlas.Order20160A8.sl4TwoEquivPSL (e (QuotientGroup.mk' (pCore 2 C) c)))).val) ∧
      (C.map (QuotientGroup.mk' (pCore 2 I))).map b.toMonoidHom = alternatingGroup (Fin 8) := by
  obtain ⟨hres,hgen,_⟩ := local_component_eq_residual_at
    d h hab structural previous faithful earlier source47 I hI C hC
  let : C.Normal := hres ▸ inferInstance
  obtain ⟨_,_,hn,hout⟩ := InnerLinearExclusion.Guarded.local_relative_component_small_inner_rows
    h hab structural previous faithful source47 core_commutator I hI C hC
    (source47 I hI C hC).1 hgen.symm
  have hp := ambient_core_image_ne_top_of_noninner I (C.map I.subtype) (map_subtype_le C)
    (show ((C.map I.subtype).subgroupOf I).Normal by
      simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
        (inferInstance : C.Normal)) hn (F.sylow_le_of_mem_Hz hI)
    (hout 4 (Or.inl rfl) ⟨e⟩)
  have hp' : C.map (QuotientGroup.mk' (pCore 2 I)) ≠ ⊤ := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hp
  exact component_symmetric_eight_marking C hC e
    (local_unique_component_and_fitting_at d h hab structural previous faithful earlier
      source47 I hI C hC).2.2 hp'

/-- The original invariant point parabolic forces degree four in the graph
branch. In degree five no node is fixed by the actual outer Sylow actor. -/
theorem local_linear_graph_degree_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) : m = 3 := by
  obtain ⟨_,hgen,_⟩ := local_component_eq_residual_at
    d h hab structural previous faithful earlier source47 I hI C hC
  obtain ⟨_,_,hn,hout⟩ := InnerLinearExclusion.Guarded.local_relative_component_small_inner_rows
    h hab structural previous faithful source47 core_commutator I hI C hC
    (source47 I hI C hC).1 hgen.symm
  let c := C.equivMapOfInjective I.subtype I.subtype_injective
  let q := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let eK := q.symm.trans (e.trans (slEquivLinear (m + 1)))
  exact (local_graph_node_at h structural I (C.map I.subtype) hI (map_subtype_le C)
    hn hgen.symm (source47 I hI C hC).1 hm eK
    (hout (m+1) (by omega) ⟨e⟩)).1

/-- The original SL₅(2) row is impossible: the inner row is already excluded,
and its graph automorphism fixes no marked minimal parabolic. -/
theorem local_five_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : False := by
  have hh := local_linear_graph_degree_at d h hab structural previous faithful earlier source47
    core_commutator I hI C hC (m := 4) (Or.inr rfl) e
  omega

/-- The original point parabolic in the four-dimensional graph branch is
the point-hyperplane flag stabilizer inside the actual component image.
Its two source containments are retained for the quotient seed action. -/
theorem local_four_middle_parabolic_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ (eK : C.map (QuotientGroup.mk' (pCore 2 I)) ≃* LinearGroup 4)
      (P : Subgroup (C.map (QuotientGroup.mk' (pCore 2 I))))
      (A B : Submodule (ZMod 2) (Space 4)),
      A ≤ B ∧ Module.finrank (ZMod 2) A = 1 ∧ Module.finrank (ZMod 2) B = 3 ∧
      P.map eK.toMonoidHom = parabolic A ⊓ parabolic B ∧
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≤
        P.map (C.map (QuotientGroup.mk' (pCore 2 I))).subtype ∧
      P.map (C.map (QuotientGroup.mk' (pCore 2 I))).subtype ≤
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
          (QuotientGroup.mk' (pCore 2 I)) := by
  obtain ⟨_,hgen,_⟩ := local_component_eq_residual_at
    d h hab structural previous faithful earlier source47 I hI C hC
  have hLC := (source47 I hI C hC).1
  obtain ⟨_,_,hn,hout⟩ := InnerLinearExclusion.Guarded.local_relative_component_small_inner_rows
    h hab structural previous faithful source47 core_commutator I hI C hC hLC hgen.symm
  let eLin := e.trans (slEquivLinear 4)
  let eAmbient := ambientComponentEquiv I C eLin
  obtain ⟨_,b,i,hi,_,hnode,_⟩ := local_graph_node_at h structural I (C.map I.subtype) hI
    (map_subtype_le C) hn hgen.symm hLC (m := 3) (Or.inl rfl) eAmbient
    (hout 4 (Or.inl rfl) ⟨e⟩)
  have hi' : i = (1 : Fin 3) := Fin.ext hi
  subst i
  let q := QuotientGroup.mk' (pCore 2 I)
  let K := C.map q
  let P₀ := F.Li L 1 ⊔ ((T : Subgroup G) ⊓ C.map I.subtype)
  have hPK : P₀ ≤ C.map I.subtype := sup_le hLC inf_le_right
  let P := ((P₀.subgroupOf I).map q).subgroupOf K
  let eStar := componentImageEquiv I C hC eLin
  have hPmap : P.map K.subtype = (P₀.subgroupOf I).map q :=
    component_subgroup_image_map_subtype I C P₀ hPK
  refine ⟨eStar,P,cutSpace b (0 : Fin 3),cutSpace b (2 : Fin 3),
    cutSpace_mono b (by decide),?_,?_,?_,?_,?_⟩
  · simpa using cutSpace_finrank b (0 : Fin 3)
  · simpa using cutSpace_finrank b (2 : Fin 3)
  · rw [ambient_component_subgroup_image I C hC eLin P₀ hPK]
    exact hnode.trans (middle_node_eq_point_hyperplane b)
  · rw [hPmap]
    exact map_mono (subgroupOf_mono I le_sup_left)
  · rw [hPmap]
    exact map_mono (subgroupOf_mono I
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
