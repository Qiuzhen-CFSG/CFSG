module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RadiusOneBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.CenterProduct

/-!
# Source application of the epsilon-one distance exclusion

The actual marked local quotients and odd-index actors supply both local
rank-one generation steps. The two-closed full Borel supplies the edge cores.
Thus the distance bound is proved from the prior local data, the (7.1) Sylow
products and (6.6), with no local-generation or distance callback. The final
application uses the genuine reduced F1.11 graph and discharges its full
kernel-Sylow and Borel two-closedness premises.

The (7.1) recognition/Sylow family remains with this noncommuting owner.
The (6.1), (6.2)(c) and (6.6) inputs retain the setup owner and final source
assembly. The exact epsilon-two choice also gives conjugate endpoints and
even b; its long-distance exclusion and all of Theorem B remain unproved.
Source: DGS, *Groups and Graphs* (1985), (7.3), printed pp.127--128.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- The literal graph bound, with generation and faithful local cover proved
from the preceding marked source local data. -/
theorem graph_radiusOne_bound_of_localData
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (L : Vertex (family P) → Subgroup G)
    (hL : ∀ v, L v ≤ stabilizer (family P) v)
    (d : ∀ v w, (graph (family P)).Adj v w →
      LocalRankOneData (stabilizer (family P) v)
        (stabilizer (family P) v ⊓ stabilizer (family P) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (family P) v))
    (hprod : ∀ v w, IsCriticalPair (family P) v w → ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hobs : ∀ v u, (graph (family P)).Adj v u → ¬ stabilizer (family P) v ≤
      normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G))
    (hCS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v)
      (L v ⊓ centralizer (Z (family P) v : Set G)))
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥) : b (family P) ≤ 2 := by
  apply graph_radiusOne_distance_bound h hS L hL ?_ ?_ ?_ hprod hobs hCS hc hne
  · intro x y he a ha
    simpa only [hstar] using local_star_factor (d x y he) a ha
  · intro x y he
    rw [← hstar x y he,← local_sylow_eq_edgeCore (d x y he)
      (by rw [hstar]; exact hodd x) (source_edge_core_sylow h hB he)]
    exact map_subtype_le _
  · intro x y he A hp hA hesc
    have hAE : ¬ A ≤ stabilizer (family P) x ⊓ stabilizer (family P) y :=
      fun hle => hesc (hle.trans inf_le_right)
    simpa only [hstar] using local_escaping_twoGroup_generates (d x y he)
      (by rw [hstar]; exact hodd x) (source_edge_core_sylow h hB he) A hp hA hAE

/-- DGS (7.3), with epsilon one imposed at one actual neighbor. The remaining
centralizer-Sylow alternatives are discharged using the orbit transports. -/
theorem graph_epsilonOne_bound_of_localData
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (family P) v) (U (family P) v))
    (L : Vertex (family P) → Subgroup G)
    (hL : ∀ v, L v ≤ stabilizer (family P) v)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ v w, (graph (family P)).Adj v w →
      LocalRankOneData (stabilizer (family P) v)
        (stabilizer (family P) v ⊓ stabilizer (family P) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (family P) v))
    (hprod : ∀ v w, IsCriticalPair (family P) v w → ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (h66 : ∀ v u, (graph (family P)).Adj v u →
      stabilizer (family P) v ≤
        normalizer ((Z (family P) u ⊔ Z (family P) v : Subgroup G) : Set G) →
      Z (family P) v = Stellmacher.omegaOneCenterAmbient
        ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hepsilon : Z (family P) u ≠ Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    b (family P) ≤ 2 := by
  let := finite_endpoints h
  let := graph_Z_elementary h w
  have hother : Z (family P) w ≤ L v := by
    rw [← hstar v u hvu]
    exact local_twoGroup_le_star (d v u hvu) (by rw [hstar]; exact hodd v)
      _ (IsElementaryAbelian.isPGroup 2 _) (criticalPair_centers (family P) h.generate hc).1
  have hnoncentral : Z (family P) u ≠ Stellmacher.omegaOneCenterAmbient (L u) := by
    rw [← hstar u v hvu.symm]
    apply graph_noncentral_of_edgeSeed_ne h hB hvu.symm (d u v hvu.symm)
      (by rw [hstar]; exact hodd u)
    simpa only [inf_comm] using hepsilon
  have hCS := graph_sylow_centralizers_of_epsilonOne h L hcov hdich hvu hnoncentral hother hne
  have hobs : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) x ≤
      normalizer ((Z (family P) y ⊔ Z (family P) x : Subgroup G) : Set G) := by
    intro x y he
    apply graph_center_product_obstruction h hB he (d x y he)
      (by rw [hstar]; exact hodd x) ?_ (h66 x y he)
    rw [hstar]
    exact hCS x
  exact graph_radiusOne_bound_of_localData h hB hS L hL d hstar hodd hprod hobs hCS hc hne

/-- The exact epsilon-two choice forces the conjugacy and parity conclusion
of (7.4)(a). The (6.2)(c) Sylow branch is excluded on the same edge seed. -/
theorem graph_epsilonTwo_even_of_localData
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ v w, (graph (family P)).Adj v w →
      LocalRankOneData (stabilizer (family P) v)
        (stabilizer (family P) v ⊓ stabilizer (family P) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (family P) v))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    (∃ g : G, g • v = w) ∧ Even (b (family P)) := by
  let := finite_endpoints h
  have hcentral : Z (family P) u = Stellmacher.omegaOneCenterAmbient (L u) := by
    apply (hdich u).resolve_left
    intro hCS
    have hh := graph_seed_ne_of_centralizerSylow h hB hvu.symm (d u v hvu.symm)
      (by rw [hstar]; exact hodd u) (by rw [hstar]; exact hCS)
    exact hh (by simpa only [inf_comm] using hepsilon)
  have hvw : v ≠ w := by
    intro he
    have hd := hc.1
    have hp := source_b_positive h
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨t,hwt,_⟩ := exists_predecessor (family P) h.generate v w hvw
  let := graph_Z_elementary h v
  have hother : Z (family P) v ≤ L w := by
    rw [← hstar w t hwt]
    exact local_twoGroup_le_star (d w t hwt) (by rw [hstar]; exact hodd w)
      _ (IsElementaryAbelian.isPGroup 2 _)
      (Z_le_stabilizer_of_dist_le_b (family P) h.generate v w hc.1.le)
  exact graph_even_of_epsilonTwo h L hcov hc hvu hcentral hother hne

namespace Reduction
open DGS85.Reduction
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Actual F1.11 reduced-graph application. The full Borel and kernel Sylow
premises are discharged by the published setup proofs on this same carrier. -/
theorem reduced_radiusOne_bound_of_localData (h : HypothesisF11 L₀ S₀)
    (L : Vertex (reducedFamily L₀ S₀) → Subgroup (G₀ L₀ S₀))
    (hL : ∀ v, L v ≤ stabilizer (reducedFamily L₀ S₀) v)
    (d : ∀ v w, (graph (reducedFamily L₀ S₀)).Adj v w →
      LocalRankOneData (stabilizer (reducedFamily L₀ S₀) v)
        (stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (reducedFamily L₀ S₀) v))
    (hprod : ∀ v w, IsCriticalPair (reducedFamily L₀ S₀) v w →
      ⁅Z (reducedFamily L₀ S₀) v,Z (reducedFamily L₀ S₀) w⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z (reducedFamily L₀ S₀) v ⊔ Q (reducedFamily L₀ S₀) w)
        (stabilizer (reducedFamily L₀ S₀) w))
    (hobs : ∀ v u, (graph (reducedFamily L₀ S₀)).Adj v u →
      ¬ stabilizer (reducedFamily L₀ S₀) v ≤
        normalizer ((Z (reducedFamily L₀ S₀) u ⊔ Z (reducedFamily L₀ S₀) v :
          Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)))
    (hCS : ∀ v, Stellmacher.IsSylowSubgroupIn (Q (reducedFamily L₀ S₀) v)
      (L v ⊓ centralizer (Z (reducedFamily L₀ S₀) v : Set (G₀ L₀ S₀))))
    {v w : Vertex (reducedFamily L₀ S₀)} (hc : IsCriticalPair (reducedFamily L₀ S₀) v w)
    (hne : ⁅Z (reducedFamily L₀ S₀) v,Z (reducedFamily L₀ S₀) w⁆ ≠ ⊥) :
    b (reducedFamily L₀ S₀) = 1 ∨ b (reducedFamily L₀ S₀) = 2 := by
  have hle := graph_radiusOne_bound_of_localData (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_kernel_sylow h) L hL d hstar hodd hprod hobs hCS hc hne
  have hpos := source_b_positive (reduced_triple h)
  change b (reducedFamily L₀ S₀) ≤ 2 at hle
  change 0 < b (reducedFamily L₀ S₀) at hpos
  omega

/-- The exact epsilon-one branch on the original reduced F1.11 carrier,
with its full Borel and both vertex orbits. The (7.1) Sylow products remain
an explicit Chapter 7 input, not an assumed distance conclusion. -/
theorem reduced_epsilonOne_bound_of_localData (h : HypothesisF11 L₀ S₀)
    (L : Vertex (reducedFamily L₀ S₀) → Subgroup (G₀ L₀ S₀))
    (hL : ∀ v, L v ≤ stabilizer (reducedFamily L₀ S₀) v)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ v w, (graph (reducedFamily L₀ S₀)).Adj v w →
      LocalRankOneData (stabilizer (reducedFamily L₀ S₀) v)
        (stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (reducedFamily L₀ S₀) v))
    (hprod : ∀ v w, IsCriticalPair (reducedFamily L₀ S₀) v w →
      ⁅Z (reducedFamily L₀ S₀) v,Z (reducedFamily L₀ S₀) w⁆ ≠ ⊥ →
      Stellmacher.IsSylowSubgroupIn (Z (reducedFamily L₀ S₀) v ⊔ Q (reducedFamily L₀ S₀) w)
        (stabilizer (reducedFamily L₀ S₀) w))
    (h66 : ∀ v u, (graph (reducedFamily L₀ S₀)).Adj v u →
      stabilizer (reducedFamily L₀ S₀) v ≤
        normalizer ((Z (reducedFamily L₀ S₀) u ⊔ Z (reducedFamily L₀ S₀) v :
          Subgroup (G₀ L₀ S₀)) : Set (G₀ L₀ S₀)) →
      Z (reducedFamily L₀ S₀) v = Stellmacher.omegaOneCenterAmbient
        ((stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) u).pCoreIn 2))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (reducedFamily L₀ S₀) x)
      (L x ⊓ centralizer (Z (reducedFamily L₀ S₀) x : Set (G₀ L₀ S₀))) ∨
      Z (reducedFamily L₀ S₀) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u : Vertex (reducedFamily L₀ S₀)} (hc : IsCriticalPair (reducedFamily L₀ S₀) v w)
    (hne : ⁅Z (reducedFamily L₀ S₀) v,Z (reducedFamily L₀ S₀) w⁆ ≠ ⊥)
    (hvu : (graph (reducedFamily L₀ S₀)).Adj v u)
    (hepsilon : Z (reducedFamily L₀ S₀) u ≠ Stellmacher.omegaOneCenterAmbient
      ((stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) u).pCoreIn 2)) :
    b (reducedFamily L₀ S₀) = 1 ∨ b (reducedFamily L₀ S₀) = 2 := by
  have hle := graph_epsilonOne_bound_of_localData (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_kernel_sylow h) L hL hcov d hstar hodd hprod h66
    hdich hc hne hvu hepsilon
  have hpos := source_b_positive (reduced_triple h)
  change b (reducedFamily L₀ S₀) ≤ 2 at hle
  change 0 < b (reducedFamily L₀ S₀) at hpos
  omega

/-- The epsilon-two orbit and parity conclusion on the same original reduced
source graph. No bound for this branch is inferred from evenness. -/
theorem reduced_epsilonTwo_even_of_localData (h : HypothesisF11 L₀ S₀)
    (L : Vertex (reducedFamily L₀ S₀) → Subgroup (G₀ L₀ S₀))
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ v w, (graph (reducedFamily L₀ S₀)).Adj v w →
      LocalRankOneData (stabilizer (reducedFamily L₀ S₀) v)
        (stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) w))
    (hstar : ∀ v w he, (d v w he).Pstar = L v)
    (hodd : ∀ v, ¬ 2 ∣ (L v).relIndex (stabilizer (reducedFamily L₀ S₀) v))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (reducedFamily L₀ S₀) x)
      (L x ⊓ centralizer (Z (reducedFamily L₀ S₀) x : Set (G₀ L₀ S₀))) ∨
      Z (reducedFamily L₀ S₀) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u : Vertex (reducedFamily L₀ S₀)} (hc : IsCriticalPair (reducedFamily L₀ S₀) v w)
    (hne : ⁅Z (reducedFamily L₀ S₀) v,Z (reducedFamily L₀ S₀) w⁆ ≠ ⊥)
    (hvu : (graph (reducedFamily L₀ S₀)).Adj v u)
    (hepsilon : Z (reducedFamily L₀ S₀) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (reducedFamily L₀ S₀) v ⊓ stabilizer (reducedFamily L₀ S₀) u).pCoreIn 2)) :
    (∃ g : G₀ L₀ S₀, g • v = w) ∧ Even (b (reducedFamily L₀ S₀)) :=
  graph_epsilonTwo_even_of_localData (reduced_triple h) (reduced_borel_core_sylow h)
    L hcov d hstar hodd hdich hc hne hvu hepsilon

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
