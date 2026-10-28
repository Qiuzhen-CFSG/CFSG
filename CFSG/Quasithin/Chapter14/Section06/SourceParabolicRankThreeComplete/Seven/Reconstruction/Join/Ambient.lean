module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.JoinSelection
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ResidualCore

/-!
# The ambient normal moved subgroup

Equality of the residual-join and ambient two-cores identifies the literal
star commutator with the ambient omega-center commutator. Both factors
are normal in H, giving the ambient action used by Join.Source.
Source: Aschbacher–Smith, C.2.7 and original14.6.10(5), pp.145–147 and1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- The residual's literal moved subgroup is normal in the original ambient group. -/
theorem moved_normal (h : Input KnownSimple.IsKnownSimple H R M K)
    (hK : K = (pResidual 2 H).map H.subtype)
    (hr : MSOddIndexRadical (R.subgroupOf H)) :
    ((⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map (inclusion h.join_le)).Normal := by
  let W := ⁅Stellmacher.omegaOneCenterAmbient (pCore 2 H),pResidual 2 H⁆
  have hW : (Stellmacher.omegaOneCenterAmbient (pCore 2 H)).Normal := by
    apply normal_iff_map_conj_eq.mpr
    intro g
    rw [←Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
      Subgroup.Normal.map_conj_eq]
  let := hW
  have he : (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map (inclusion h.join_le) = W := by
    apply map_injective H.subtype_injective
    rw [map_map]
    change (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map (K ⊔ R : Subgroup G).subtype = W.map H.subtype
    rw [hK,C27Source.residual_star_moved_eq_omegaCore_commutator H R h.setup.radical_le hr]
    dsimp [W]
    rw [map_commutator,←Stellmacher.omegaOneCenterAmbient_map_injective _ H.subtype_injective]
    rfl
  rw [he]
  infer_instance

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction.Join
