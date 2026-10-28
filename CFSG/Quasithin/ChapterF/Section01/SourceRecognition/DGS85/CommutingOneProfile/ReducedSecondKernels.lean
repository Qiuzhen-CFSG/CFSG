module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.AlphaSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedBetaCoreSpecial

/-!
# The original second and third graph kernels

The literal reduced-to-original inclusion transports the full alpha second
kernel and beta third kernel, both trivial. It also transports the actual
two-core of the full beta second kernel to the original beta-center image.
The beta second kernel is nontrivial because that center is nontrivial.

These conclusions retain the original local quotient catalogue and the
same escaping source path. The unitary full-Borel consumer in
UnitaryCoreProfile uses its original S/Q_beta branch hypothesis and retains
both unitary covers and every positive field degree.
Source: DGS85, Groups and Graphs (1985), reduction pp.95--96 and the
(11.6)--(11.8) consequences proved in AlphaSecondKernel.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The full original kernel images and the literal second-kernel radical. -/
theorem original_reduced_second_kernels_on_escaping_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b)
    (hesc : ¬ (Z F₀ b).map (G₀).subtype ≤ (Q F₀ (g • b)).map (G₀).subtype)
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hbp : b ∈ p.vertices) (hcp : c ∈ p.vertices)
    (hgbp : g • b ∈ p.vertices) (hgcp : g • c ∈ p.vertices) :
    (ballKernel F₀ a 2).map (G₀).subtype = ⊥ ∧
      (ballKernel F₀ b 3).map (G₀).subtype = ⊥ ∧
      ((ballKernel F₀ b 2).map (G₀).subtype).pCoreIn 2 = (Z F₀ b).map (G₀).subtype ∧
      (ballKernel F₀ b 2).map (G₀).subtype ≠ ⊥ := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  obtain ⟨hα,hβ,hR⟩ := source_full_second_kernels_on_escaping_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) d hc hb hcomm
    hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb) g hga hgb
    (fun hh => hesc (map_mono hh)) ht p hp ha hbp hcp hgbp hgcp
  change ballKernel F₀ a 2 = ⊥ at hα
  change ballKernel F₀ b 3 = ⊥ at hβ
  change (ballKernel F₀ b 2).pCoreIn 2 = Z F₀ b at hR
  have hR' : ((ballKernel F₀ b 2).map (G₀).subtype).pCoreIn 2 = (Z F₀ b).map (G₀).subtype := by
    rw [Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (G₀).subtype (G₀).subtype_injective,hR]
  refine ⟨by rw [hα,Subgroup.map_bot],by rw [hβ,Subgroup.map_bot],hR',?_⟩
  have hZ := (original_reduced_beta_core_special_on_escaping_path h d hc hb hcomm hbc hac
    Ma Mb g hga hgb hesc ht p hp ha hbp hcp hgbp hgcp).2.2.2.1
  intro hz
  apply hZ
  apply bot_unique
  rw [←hR']
  exact (pCoreIn_le 2 _).trans hz.le

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
