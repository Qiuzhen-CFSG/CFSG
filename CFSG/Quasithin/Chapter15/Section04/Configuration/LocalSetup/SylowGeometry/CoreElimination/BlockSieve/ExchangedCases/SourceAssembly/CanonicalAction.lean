module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.CanonicalModule
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NormalElementaryEmbedding
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFNatural

/-!
# The original natural section on the canonical module

The constructed canonical Sylow-center span has the original omega-module
kernel. Characteristic-normalizer control therefore proves its FF property.
The full B.5 theorem on its actual offender subgroup is compared with the
original B.5 section through the literal module inclusion and component
marking. This constructs the same-field natural section needed by the
canonical-module block theorem; naturality is not re-assumed on the new span.
Source: Aschbacher–Smith C.2.7(3)(a), pp.146–147; 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_canonical_natural_section
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    [IsSimpleGroup (starComponent L ((sourceRadical d U).subgroupOf H))]
    [IsQuasisimple (starComponent L ((sourceRadical d U).subgroupOf H))]
    (P : Sylow 2 (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    (hP : (P : Subgroup _) = ((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H))
    (W : Subgroup (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H))
    [W.Normal] [IsElementaryAbelian 2 W]
    (hW : W = normalClosure (omegaOneCenterAmbient
      (P : Subgroup (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H)) :
        Set (L ⊔ (sourceRadical d U).subgroupOf H : Subgroup H)))
    (c : StarSourceConclusion L ((sourceRadical d U).subgroupOf H))
    (hi : IsIrrPlus
      ((starRepresentation L ((sourceRadical d U).subgroupOf H)).comp
        (offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H))).subtype)
      ((starComponent L ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H))))
      c.sectionData.space.toSubmodule)
    (F : BinaryField)
    (hnatural : ActionEquiv (c.sectionData.action.comp
      ((starComponent L ((sourceRadical d U).subgroupOf H)).subgroupOf
        (offenderSubgroup (starRepresentation L ((sourceRadical d U).subgroupOf H)))).subtype)
      (linearNatural F 2)) :
    ∃ hker : (starProjection L ((sourceRadical d U).subgroupOf H)).ker = centralizer (W : Set _),
      let σ := NormalElementaryQuotient.representation W
        (starProjection L ((sourceRadical d U).subgroupOf H))
        (QuotientGroup.mk'_surjective _) hker
      let C := starComponent L ((sourceRadical d U).subgroupOf H)
      C ≤ offenderSubgroup σ ∧
      ∃ cW : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (σ.comp (offenderSubgroup σ).subtype) (C.subgroupOf (offenderSubgroup σ)),
        IsLinearNatural (cW.sectionData.action.comp (C.subgroupOf (offenderSubgroup σ)).subtype) F 2 := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let C := starComponent L R
  let V := omegaCoreModule D
  let M := d.M₁.subgroupOf H
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hgeom := source_canonical_module_kernel h L hc hr P hP
  have hWV : W ≤ V := by rw [hW]; exact hgeom.1
  have hCW : centralizer (W : Set D) = pCore 2 D := by rw [hW]; exact hgeom.2
  have hker : (starProjection L R).ker = centralizer (W : Set D) :=
    ((QuotientGroup.ker_mk' _).trans hk).trans hCW.symm
  let σ := NormalElementaryQuotient.representation W (starProjection L R)
    (QuotientGroup.mk'_surjective _) hker
  have hVQ : V ≤ pCore 2 D := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hQR : pCore 2 D ≤ R.subgroupOf D :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hcontrol : (R.subgroupOf D).characteristicNormalizerClosure ≤ M.subgroupOf D :=
    characteristicNormalizerClosure_subgroupOf_le le_sup_right hc.characteristic_control
  have hproper : M.subgroupOf D ≠ ⊤ := by
    intro he
    exact hc.outside (le_sup_left.trans (subgroupOf_eq_top.mp he))
  have hff := (ChapterC.offender_of_characteristic_control W (R.subgroupOf D)
    (M.subgroupOf D) hr.isPGroup hr.1 hQR (hWV.trans hVQ) hCW hcontrol hproper
    (starProjection L R) (QuotientGroup.mk'_surjective _) hker).2.1
  let : (L.subgroupOf D).Normal := hc.local_normal
  let : C.Normal := (inferInstance : (L.subgroupOf D).Normal).map
    (starProjection L R) (QuotientGroup.mk'_surjective _)
  have hgen : C ⊔ starRadical L R = ⊤ := by
    change (L.subgroupOf D).map (starProjection L R) ⊔
      (R.subgroupOf D).map (starProjection L R) = ⊤
    rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 (Star L R ⧸ C) :=
    isPGroup_quotient_of_sup_eq_top C (starRadical L R)
      (hr.isPGroup.map (starProjection L R)) hgen
  have hco := source_component_core_offenders_of_local_radical h L KnownSimple.IsKnownSimple hc hr
  have hC : centralizer (C : Set (Star L R)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C (Group.IsPerfect.not_isMulCommutative C)
      hquot hco.1.2.2.2
  have hsD : IsSQTK KnownSimple.IsKnownSimple D := hc.sqtk.subgroup _
  have hsQ : IsSQTK KnownSimple.IsKnownSimple (D ⧸ pCore 2 D) := by
    refine ⟨?_, hsD.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsD.stronglyQuasithin p hp ho)
  have hs : IsSQTK KnownSimple.IsKnownSimple (Star L R) :=
    (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq hk)).mpr hsQ
  refine ⟨hker,?_⟩
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_natural_of_normal_elementary_inclusion
    W V hWV (starProjection L R) (QuotientGroup.mk'_surjective _) hker
    (QuotientGroup.ker_mk' _) C hC (hs.subgroup _) hff
    (source_star_ff_classification h L hc hr).1 c hi F hnatural

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
