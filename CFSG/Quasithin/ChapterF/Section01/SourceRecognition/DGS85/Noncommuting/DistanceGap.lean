module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EpsilonTwoCenters

/-!
# The epsilon-two distance-four exclusion

Faithfulness and maximal edge stabilizers make the center spans of distinct
neighbors distinct. The two critical-end identities of (7.4)(c) therefore
exclude b=4: the first and last interior vertices of a four-step critical path
are distinct neighbors of its midpoint. Parity and positivity leave b=2 or
b at least six. The path is constructed inside the connected graph; no tree
hypothesis or finite ambient completion is used.

The reduced-source application discharges the full-Borel and kernel-Sylow
premises. Natural endpoints and the earlier local statements remain explicit.
This is only (7.5)(3)'s distance-four exclusion: the b at least six branch,
including the path-stabilizer argument and final module comparison, remains open.

Source: DGS, *Groups and Graphs* (1985), (7.5)(3), pp.129--130.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G]

/-- The actual center span is nontrivial at every vertex, not only the base pair. -/
theorem graph_Z_ne_bot {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) (v : Vertex (family P)) : Z (family P) v ≠ ⊥ := by
  let := finite_endpoints h
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) v
  rw [←hg,Z_translate]
  exact fun he => base_Z_ne_bot h v.type
    ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp he)

/-- Distinct neighbors have distinct center spans. Local primitivity and the
faithful common-normal obstruction suffice; no finite completion is imposed. -/
theorem graph_neighbor_centers_ne {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B) {v u t : Vertex (family P)}
    (hvu : (graph (family P)).Adj v u) (hvt : (graph (family P)).Adj v t)
    (hut : u ≠ t) : Z (family P) u ≠ Z (family P) t := by
  let := finite_endpoints h
  intro he
  have hnU : stabilizer (family P) u ≤ normalizer (Z (family P) u : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer _ _)).mp (Z_normal _ _)
  obtain ⟨g,hg,hgt⟩ := locally_transitive (family P) hvu hvt
  have hgN : g ∈ normalizer (Z (family P) u : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (Z (family P) u).map (MulAut.conj g).toMonoidHom = _
    rw [←Z_translate,hgt,←he]
  let M := stabilizer (family P) v ⊓ normalizer (Z (family P) u : Set G)
  have hEM : stabilizer (family P) v ⊓ stabilizer (family P) u ≤ M :=
    le_inf inf_le_left (inf_le_right.trans hnU)
  have hfull : M = stabilizer (family P) v := by
    rcases source_edge_maximal h hvu M hEM inf_le_left with hm | hm
    · have hgm : g ∈ M := ⟨hg,hgN⟩
      rw [hm] at hgm
      have hgu : g • u = u := hgm.2
      exact (hut (hgu.symm.trans hgt)).elim
    · exact hm
  have hnV : stabilizer (family P) v ≤ normalizer (Z (family P) u : Set G) :=
    hfull.symm.le.trans inf_le_right
  apply graph_Z_ne_bot h u
  apply graph_local_common_normal_eq_bot h hvu (stabilizer (family P) v)
    (stabilizer (family P) u) (Z (family P) u)
    (fun a ha => ⟨a,ha,1,one_mem _,(mul_one _).symm⟩)
    (fun a ha => ⟨a,ha,1,one_mem _,(mul_one _).symm⟩) ?_ hnV hnU
  apply le_inf ?_ (Z_le_stabilizer _ _)
  exact ((source_Z_Q_U h u).1.trans (map_subtype_le _)).trans
    ((source_Z_Q_U h u).2.trans ((ballKernel_one_le_edge (family P) hvu.symm).trans inf_le_right))

/-- The common critical-center identity excludes b=4. This proves the first
long-distance exclusion in DGS (7.5)(3) on the literal connected source graph. -/
theorem graph_epsilonTwo_not_four
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w)) :
    b (family P) ≠ 4 := by
  intro hb
  have huw : u ≠ w := by
    intro he
    rw [he,SimpleGraph.dist_self] at hdu
    omega
  obtain ⟨t,hwt,hut⟩ := exists_predecessor (family P) h.generate u w huw
  have hutdist : (graph (family P)).dist u t = 2 := by omega
  have hutne : u ≠ t := by
    intro he
    rw [he,SimpleGraph.dist_self] at hutdist
    omega
  obtain ⟨m,htm,hum⟩ := exists_predecessor (family P) h.generate u t hutne
  have humadj : (graph (family P)).Adj u m := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hdt : (graph (family P)).dist v t + 1 = b (family P) := by
    have h₁ := (connected_graph h).dist_triangle (u := v) (v := u) (w := t)
    have h₂ := (connected_graph h).dist_triangle (u := v) (v := t) (w := w)
    have hvud : (graph (family P)).dist v u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hvu
    have htwd : (graph (family P)).dist t w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hwt.symm
    have hvw := hc.1
    omega
  have hid := graph_epsilonTwo_critical_centers h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hwt hdu hdt hepsilon hnat₀ hnat₁
  exact graph_neighbor_centers_ne h humadj.symm htm.symm hutne (hid.1.symm.trans hid.2.1)


/-- In epsilon two, the only remaining contrary branch has b at least six. -/
theorem graph_epsilonTwo_distance_gap
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w)) :
    b (family P) = 2 ∨ 6 ≤ b (family P) := by
  have hn := graph_epsilonTwo_not_four h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁
  obtain ⟨n,hn'⟩ := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).2
  have hp := source_b_positive h
  omega

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F" => reducedFamily L₀ S₀

/-- The actual reduced F1.11 distance gap; the earlier kernel-Sylow and full-Borel
premises are discharged on the same graph. The b at least six branch is still open. -/
theorem reduced_epsilonTwo_distance_gap
    (h : HypothesisF11 L₀ S₀)
    (L : Vertex F → Subgroup (G₀ L₀ S₀))
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph F).Adj x y →
      LocalRankOneData (stabilizer F x)
        (stabilizer F x ⊓ stabilizer F y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer F x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x)
      (L x ⊓ centralizer (Z F x : Set (G₀ L₀ S₀))) ∨
      Z F x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph F).Adj x y → ¬ stabilizer F y ≤ normalizer
      ((Q F x ⊓ Q F y : Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    {v w u : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hvu : (graph F).Adj v u)
    (hdu : (graph F).dist u w + 1 = b F)
    (hepsilon : Z F u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer F v ⊓ stabilizer F u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z F v) (Q F v))
    (hnat₁ : HasNaturalCenter (L w) (Z F w) (Q F w)) : b F = 2 ∨ 6 ≤ b F := by
  exact graph_epsilonTwo_distance_gap (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_kernel_sylow h) L hcov d hstar hodd hdich hob hc hne hvu hdu hepsilon hnat₀ hnat₁

end Reduction

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
