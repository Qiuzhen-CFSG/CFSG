module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.MixedCentralizer
public import Stellmacher.FullBaumannLocalResidual

/-!
# The original vertex residual in the normalized mixed centralizer

The normalized second extraction retains a residual conjugator x whose
conjugated actor module lies in the original common Sylow. Its full
Baumann commutator therefore supplements that Sylow in the next vertex.
The large-center cubic hypothesis puts B(T) outside the next two-core.
The local normalizer theorem now identifies the extracted full commutator
with the entire original next-vertex two-residual.

Consequently the actual nontrivial mixed subgroup centralizes that
original residual. The source application preserves the graph, critical
path, both extractions and their simultaneous normalization. For a
commuting critical path, the next vertex is the central orientation;
the initial vertex is centerless by (7.5). No orientation is silently
reversed, and subnormality in the mixed centralizer remains unasserted.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, the mixed
centralizer step; Aschbacher--Smith F.1.12 and F.6's cubic specialization.
-/
open Subgroup Stellmacher Stellmacher.SectionsFiveToSeven
open Stellmacher.Later Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix
namespace Stellmacher.SectionNine.LocalLonger
universe u
variable {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}

public theorem extracted_full_commutator_eq_original_residual
    (ctx : SectionNineLocalContext G T A B)
    (first : FirstConfigurationData ctx) (second : SecondConfigurationData ctx first)
    (config : NormalizedGeometry ctx first second)
    (S : Sylow 2 G) (hS : T = (S : Subgroup G))
    (hedge : GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ ctx.criticalPath.a = T)
    (hi : (QAt ctx.Γ ctx.criticalPath.firstStep).relIndex T = 2)
    (hnot : ¬ baumannIn T ≤ QAt ctx.Γ ctx.criticalPath.firstStep) :
    extractedFullCommutator ctx first second config =
      twoResidualIn (GAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let E := second.E.map (MulAut.conj config.g⁻¹).toMonoidHom
  let R := twoResidualIn E
  let F := extractedFullCommutator ctx first second config
  let V := VAt Γ (Γ.act config.g cp.a')
  let x := config.second_geometry.x
  have hRP : R ≤ P := (map_subtype_le _).trans config.second_geometry.group_le
  have hTP : T ≤ P := hedge ▸ inf_le_left
  have hFP : F ≤ P := (Subgroup.commutator_le_sup _ _).trans
    (sup_le hRP (inf_le_left.trans hTP))
  have hRF : R ≤ F := config.residual_baumann
  have hfull : F = ⁅F,baumannIn T⁆ :=
    le_antisymm (commutator_mono hRF le_rfl)
      (le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right R (baumannIn T)))
  have hxF : x ∈ F := hRF config.second_geometry.residual_mem
  have hconjT : V.conjBy x ≤ T := by
    have hcore := config.second_geometry.conjugate_core_le
    rw [config.second_new_vertex] at hcore
    exact hcore.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hET : E ≤ F ⊔ T := by
    have he : E = V ⊔ V.conjBy x := config.second_geometry.generated
    rw [he]
    refine sup_le ?_ (hconjT.trans le_sup_right)
    intro v hv
    have hc : x * v * x⁻¹ ∈ F ⊔ T :=
      mem_sup_right (hconjT (mem_map_of_mem (MulAut.conj x).toMonoidHom hv))
    have hh := (F ⊔ T).mul_mem ((F ⊔ T).mul_mem
      (mem_sup_left (F.inv_mem hxF)) hc) (mem_sup_left hxF)
    simpa [mul_assoc] using hh
  have hgen : F ⊔ T = P := by
    apply le_antisymm (sup_le hFP hTP)
    have hh := config.second_geometry.edge_generated
    rw [config.second_new_vertex, hedge] at hh
    change E ⊔ T = P at hh
    rw [← hh]
    exact sup_le hET le_sup_right
  have hQ : twoCoreIn P = QAt Γ cp.firstStep := (Γ.twoCoreAt_def _).symm
  have hi' : (twoCoreIn P).relIndex (S : Subgroup G) = 2 := by rwa [hQ,← hS]
  have hn' : ¬ baumannIn (S : Subgroup G) ≤ twoCoreIn P := by rwa [hQ,← hS]
  have hlow := residual_le_full_baumann_of_index_two S F P (hS ▸ hTP) hFP
    (hS ▸ hfull) (hS ▸ hgen) hi' hn'
  have hresT : twoResidualIn P ⊔ T = P :=
    twoResidualIn_sup_sylow (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hnorm : ((twoResidualIn P).subgroupOf (twoResidualIn P ⊔ T)).Normal := by
    rw [hresT]
    exact twoResidualIn_normal P
  have hRres : R ≤ twoResidualIn P :=
    Stellmacher.SectionThree.twoResidualAmbient_le_left_of_le_sup (twoResidualIn P) T E
      hnorm (hS ▸ S.isPGroup') (config.second_geometry.group_le.trans hresT.ge)
  have hPN : P ≤ normalizer (twoResidualIn P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoResidualIn_le P)).mp (twoResidualIn_normal P)
  apply le_antisymm ?_ hlow.2
  exact (commutator_mono hRres le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp ((inf_le_left.trans hTP).trans hPN))
end Stellmacher.SectionNine.LocalLonger

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory Stellmacher.SectionNine
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

public theorem IsGoldschmidtTriple.exists_original_residual_mixed_centralizer
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
      ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
    ∃ first : LocalLonger.FirstConfigurationData ctx,
      ∃ second : LocalLonger.SecondConfigurationData ctx first,
        ∃ config : LocalLonger.NormalizedGeometry ctx first second,
          LocalLonger.MixedCentralizerData ctx first second config ∧
          LocalLonger.extractedFullCommutator ctx first second config =
            twoResidualIn (GAt Γ cp.firstStep) ∧
          twoResidualIn (GAt Γ cp.firstStep) ≤
            centralizer (LocalLonger.mixedSubgroup ctx first second config : Set G) := by
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  obtain ⟨first,second,config,data⟩ := h.exists_nontrivial_mixed_centralizer_data
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  have hedge : GAt Γ cp.firstStep ⊓ GAt Γ cp.a = G₁ ⊓ G₂ := by
    rcases cp.edge_stabilizers_are_P with he | he
    · change Γ.stabilizer cp.firstStep ⊓ Γ.stabilizer cp.a = _
      rw [he.1,he.2,inf_comm]
    · change Γ.stabilizer cp.firstStep ⊓ Γ.stabilizer cp.a = _
      rw [he.1,he.2]
  have hi : (QAt Γ cp.firstStep).relIndex (G₁ ⊓ G₂) = 2 := by
    change (Γ.twoCoreAt cp.firstStep).relIndex _ = _
    rw [Γ.twoCoreAt_def]
    change (twoCoreIn (Γ.stabilizer cp.firstStep)).relIndex (G₁ ⊓ G₂) = 2
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [he.2]
      simpa only [Stellmacher.SectionsFiveToSeven.twoCoreIn, inf_comm G₂ G₁] using h.symm.left_core_index
    · rw [he.2]
      simpa only [Stellmacher.SectionsFiveToSeven.twoCoreIn] using h.left_core_index
  have hnot := h.critical_baumann_not_le_next_core_of_large_center
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge
  obtain ⟨S,hS⟩ := h.intersection_sylow
  have heq := LocalLonger.extracted_full_commutator_eq_original_residual
    ctx first second config S hS hedge hi hnot
  refine ⟨first,second,config,data,heq,?_⟩
  rw [← heq]
  exact le_sup_right.trans data.centralizer_contains
end CFSG.Quasithin.ChapterF
