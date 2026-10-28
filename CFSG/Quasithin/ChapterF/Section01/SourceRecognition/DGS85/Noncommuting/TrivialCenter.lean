module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterProduct

/-!
# Trivial local center in the epsilon-two case

The central omega of L_alpha lies in the omega-center of the common edge
Sylow. Under the exact epsilon-two equality this is Z_beta, which is central
in L_beta by (6.2)(c). It is therefore normalized by both local actors.
Their edge supplements and faithfulness force it to be trivial. The local
center lies in the actual vertex two-core, so a nontrivial center would
contain an involution. This proves the full center is trivial.

Source: DGS, *Groups and Graphs* (1985), (7.4)(b), p.128. The earlier
local actor and centralizer dichotomy inputs remain explicit; neither the
natural-module conclusion nor the distance bound is assumed.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- The characteristic-two local actor has trivial center once its central omega vanishes. -/
theorem local_center_eq_bot_of_omega_eq_bot {P E : Subgroup G}
    (c : LocalRankOneData P E)
    (hω : Stellmacher.omegaOneCenterAmbient c.Pstar = ⊥) : center c.Pstar = ⊥ := by
  let := c.finite_P
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  have hCQ : center c.Pstar ≤ (P.pCoreIn 2).subgroupOf c.Pstar := by
    intro z hz
    have hc : (⟨(z : G),c.Pstar_le z.property⟩ : P) ∈ centralizer (pCore 2 P : Set P) := by
      intro q hq
      apply Subtype.ext
      exact congrArg c.Pstar.subtype ((mem_center_iff.mp hz)
        ⟨(q : G),source_core_le_star c (mem_map_of_mem P.subtype hq)⟩)
    exact mem_map_of_mem P.subtype (source_core_selfCentralizing c hc)
  have hpQ : IsPGroup 2 ((P.pCoreIn 2).subgroupOf c.Pstar) :=
    (isPGroup_pCoreIn 2 P).comap_subtype
  have hpC : IsPGroup 2 (center c.Pstar) :=
    hpQ.of_injective (inclusion hCQ) (inclusion_injective _)
  by_contra hne
  have hnon : Nontrivial (center c.Pstar) := (nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n,hn,hcard⟩ := hpC.nontrivial_iff_card.mp hnon
  have hωne := omega₁_map_subtype_ne_bot (center c.Pstar) 2
    (by rw [hcard]; exact dvd_pow_self 2 (Nat.ne_of_gt hn))
  apply hωne
  exact (map_eq_bot_iff_of_injective _ c.Pstar.subtype_injective).mp hω

/-- DGS (7.4)(b), from the exact edge-Sylow epsilon-two hypothesis. -/
theorem graph_epsilonTwo_center_trivial_of_localData
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v u : Vertex (family P)} (he : (graph (family P)).Adj v u)
    (c₀ : LocalRankOneData (stabilizer (family P) v)
      (stabilizer (family P) v ⊓ stabilizer (family P) u))
    (c₁ : LocalRankOneData (stabilizer (family P) u)
      (stabilizer (family P) u ⊓ stabilizer (family P) v))
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer (family P) v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer (family P) u))
    (hdich : Stellmacher.IsSylowSubgroupIn (Q (family P) u)
      (c₁.Pstar ⊓ centralizer (Z (family P) u : Set G)) ∨
      Z (family P) u = Stellmacher.omegaOneCenterAmbient c₁.Pstar)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    center c₀.Pstar = ⊥ := by
  have hcentral : Z (family P) u = Stellmacher.omegaOneCenterAmbient c₁.Pstar := by
    apply hdich.resolve_left
    intro hCS
    exact graph_seed_ne_of_centralizerSylow h hB he.symm c₁ ho₁ hCS
      (by simpa only [inf_comm] using hepsilon)
  have hΩ := local_omega_le_edgeSeed c₀ ho₀ (source_edge_core_sylow h hB he)
  have hΩZ : Stellmacher.omegaOneCenterAmbient c₀.Pstar ≤ Z (family P) u :=
    hΩ.trans_eq hepsilon.symm
  apply local_center_eq_bot_of_omega_eq_bot c₀
  apply graph_local_common_normal_eq_bot h he c₀.Pstar c₁.Pstar
    (Stellmacher.omegaOneCenterAmbient c₀.Pstar)
  · exact local_star_factor c₀
  · intro a ha
    simpa only [inf_comm] using local_star_factor c₁ a ha
  · intro x hx
    exact pCoreIn_le 2 _ ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hΩ hx)).1
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro z hz l hl
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2 l hl
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro z hz l hl
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hcentral ▸ hΩZ hz) |>.2.2 l hl

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The full local-center conclusion on the original reduced F1.11 graph. -/
theorem reduced_epsilonTwo_center_trivial (h : HypothesisF11 L₀ S₀)
    {v u : Vertex F} (he : (graph F).Adj v u)
    (c₀ : LocalRankOneData (stabilizer F v) (stabilizer F v ⊓ stabilizer F u))
    (c₁ : LocalRankOneData (stabilizer F u) (stabilizer F u ⊓ stabilizer F v))
    (ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v))
    (ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F u))
    (hdich : Stellmacher.IsSylowSubgroupIn (Q F u)
      (c₁.Pstar ⊓ centralizer (Z F u : Set (G₀ L₀ S₀))) ∨
      Z F u = Stellmacher.omegaOneCenterAmbient c₁.Pstar)
    (hepsilon : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2)) : center c₀.Pstar = ⊥ :=
  graph_epsilonTwo_center_trivial_of_localData (reduced_triple h) (reduced_borel_core_sylow h)
    he c₀ c₁ ho₀ ho₁ hdich hepsilon

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
