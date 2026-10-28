module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.Representation.HigherFieldBorelFixedSpaces

/-!
# A nonzero quotient seed fixed by the actual component Borel residual

The original Sylow intersection with the component maps to an actual Sylow
in its image modulo O₂(I). Its normalizer residual is the image of the
original Borel residual, which fixes V. Seed separation keeps a nonzero
fixed vector in every proper quotient of the original local module.
No component model or Borel coordinates are required.

Source: Aschbacher–Smith 14.7.41–42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam AlternatingSevenSource OutsideProjectiveAt
open Representation.HigherFieldBorelFixedSpaces

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem normalizer_image_eq (I : Subgroup G) (C : Subgroup I)
    (P : Sylow 2 C)
    (hP : (P : Subgroup C) = ((T : Subgroup G).subgroupOf I).subgroupOf C) :
    (normalizer (P : Set C)).map (I.subtype.comp C.subtype) =
      componentSylowNormalizer T I C := by
  have he : (normalizer (P : Set C)).map C.subtype =
      C ⊓ normalizer ((T : Subgroup G).subgroupOf I ⊓ C : Set I) := by
    change (normalizer (↑(P : Subgroup C) : Set C)).map C.subtype = _
    have hi : ((T : Subgroup G).subgroupOf I ⊓ C).subgroupOf C =
        ((T : Subgroup G).subgroupOf I).subgroupOf C := by
      ext x
      exact and_iff_left x.property
    rw [hP,←hi,←subgroupOf_normalizer_eq (show
      (T : Subgroup G).subgroupOf I ⊓ C ≤ C from inf_le_right),
      subgroupOf_map_subtype,inf_comm]
    rfl
  rw [←Subgroup.map_map,he]
  rfl

/-- A proper original quotient has a nonzero seed fixed by the residual of
an actual Sylow normalizer in the component image. -/
theorem local_borel_residual_fixed_seed_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤) :
    let K := C.map (QuotientGroup.mk' (pCore 2 I))
    ∃ S : Sylow 2 K,
      ∃ v : (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) ⧸ N.toSubmodule,
        v ≠ 0 ∧ ∀ b : twoResidualImage (normalizer (S : Set K)),
          N.quotientRepresentation b.val.val v = v := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let K := C.map q
  let r : C →* K := q.subgroupMap C
  let f := I.subtype.comp C.subtype
  let B₀ := componentSylowNormalizer T I C
  let B₁ := (pResidual 2 B₀).map B₀.subtype
  obtain ⟨P,hP⟩ := (T.subtype (F.sylow_le_of_mem_Hz hI)).exists_subgroupOf_eq_of_normal C
  let S := P.mapSurjective (f := r) (q.subgroupMap_surjective C)
  let R := (pResidual 2 (normalizer (P : Set C))).map (normalizer (P : Set C)).subtype
  have hR : R.map f = B₁ := by
    change ((pResidual 2 (normalizer (P : Set C))).map _).map f = _
    rw [map_embedded_pResidual,normalizer_image_eq I C P hP]
  have hmap : R.map r = twoResidualImage (normalizer (S : Set K)) := by
    change ((pResidual 2 (normalizer (P : Set C))).map _).map r = _
    rw [map_embedded_pResidual,P.normalizer_map_surjective r (q.subgroupMap_surjective C)]
    rfl
  have hcentral : B₁ ≤ centralizer (V : Set G) :=
    (component_borel_fixed_actions_at d h hab structural previous faithful earlier
      I hI C hout).1
  let c := localQuotientSection a
  let p := localQuotientProjection a N
  let W := (c.imageSpace V).map p.toLinearMap
  have hdim : Module.finrank (ZMod 2) W = 2 :=
    local_quotient_seed_finrank h hI c p (localQuotientProjection_ker_ne_top a N hN)
  have hW : W ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdim
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨S,v,hv0,?_⟩
  intro b
  have hb : b.val ∈ R.map r := hmap.symm ▸ b.property
  obtain ⟨z,hz,hzb⟩ := hb
  have hzB : f z ∈ B₁ := hR ▸ mem_map_of_mem f hz
  have hcomm : ⁅B₁,V⁆ ≤ F.Vi 1 :=
    (commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le
  obtain ⟨w,hw,hww⟩ := hv
  have hfix : a.representation (q z.val) w = w :=
    c.fixed_on_imageSpace_of_commutator_le B₁ V hcomm z.val hzB w hw
  have hfixN := congrArg p hfix
  have hbq : q z.val = b.val.val := congrArg Subtype.val hzb
  change N.quotientRepresentation (q z.val) (p w) = p w at hfixN
  change p w = v at hww
  rwa [hbq,hww] at hfixN

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
