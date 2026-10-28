module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanSymmetric
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LinearPathAction

/-!
# Reverse strict six-path regularity

The symmetric Cartan residual gives the reverse orientation of the strict
DGS six-path.  This module packages the path and its right-regularity proof;
the source-specific residual containments and edge supplement remain explicit
for the strict assembly owner.

Source: DGS, *Groups and Graphs* (1985), (10.10), printed p.164.
-/
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The translated reverse six-walk used by the strict residual argument.

This is public because the source assembly must provide the Cartan
edge-supplement identity for this exact walk when invoking the regularity
theorem below.
-/
@[expose] public def reversePath
    {u t y : Vertex F} (g : G₀ L S) (hgt : g • β = y)
    (hβu : (graph F).Adj β u) (ht : (graph F).Adj α t)
    (hy : (graph F).Adj u y) : BasedWalk (graph F) 6 (g • t) :=
  ⟨⟨g • α, (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr ht.symm⟩,
    ⟨⟨y, by
      have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr
        (show (graph F).Adj α β from
          ⟨by change false ≠ true; decide,
            Subgroup.CosetGeometry.incident_base _ _ _⟩)
      change (graph F).Adj (g • α) (g • β) at hh
      rwa [hgt] at hh⟩,
      ⟨⟨u, hy.symm⟩,
        ⟨⟨β, hβu.symm⟩,
          ⟨⟨α, ⟨by change true ≠ false; decide,
              Subgroup.CosetGeometry.incident_base _ _ _⟩⟩,
            ⟨⟨t, ht⟩, PUnit.unit⟩⟩⟩⟩⟩⟩

public theorem reversePath_vertices
    {u t y : Vertex F} (g : G₀ L S) (hgt : g • β = y)
    (hβu : (graph F).Adj β u) (ht : (graph F).Adj α t)
    (hy : (graph F).Adj u y) :
    (reversePath g hgt hβu ht hy).vertices =
      [g • t, g • α, y, u, β, α, t] := by rfl

public theorem reversePath_endpoint
    {u t y : Vertex F} (g : G₀ L S) (hgt : g • β = y)
    (hβu : (graph F).Adj β u) (ht : (graph F).Adj α t)
    (hy : (graph F).Adj u y) :
    (reversePath g hgt hβu ht hy).endpoint = t := by rfl

public theorem reversePath_penultimate
    {u t y : Vertex F} (g : G₀ L S) (hgt : g • β = y)
    (hβu : (graph F).Adj β u) (ht : (graph F).Adj α t)
    (hy : (graph F).Adj u y) :
    (reversePath g hgt hβu ht hy).penultimate = α := by rfl

/-- Reverse six-path geometry, conditional on the Cartan edge-supplement identity.
The residual orientation is the one supplied by `original_bTwo_reverse_residual_trivial`.
-/
public theorem reverse_six_path_rightRegular_of_residual
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (c : LocalRankOneData (stabilizer F t)
      (stabilizer F t ⊓ stabilizer F α))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F t))
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q F t).subgroupOf c.Pstar)
    {g : G₀ L S} (hg : g ∈ graphLocalGroup F u) (hgt : g • β = y)
    {R : Subgroup (G₀ L S)} (hR : R = bTwoResidual F β y α (g • α))
    (hRne : R ≠ ⊥) (hRzero : R ⊓ Q F t = ⊥)
    (hRbeta : R ≤ Q F β) (hRy : R ≤ Q F y)
    (hRalpha : R ≤ Q F α) (hRga : R ≤ Q F (g • α))
    (hRtwo : IsPGroup 2 R)
    (hgen : pathStabilizer F (reversePath g hgt hβu ht hy) ⊔
        (stabilizer F (reversePath g hgt hβu ht hy).endpoint ⊓
          stabilizer F (reversePath g hgt hβu ht hy).penultimate).pCoreIn 2 =
        stabilizer F (reversePath g hgt hβu ht hy).endpoint ⊓
          stabilizer F (reversePath g hgt hβu ht hy).penultimate) :
    ∃ p : BasedWalk (graph F) 6 (g • t), p.Nonbacktracking ∧
      RightRegular (A := G₀ L S) p := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  have hgu : (g : G₀ L S) • u = u := sylowGenerated_le _ hg
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hga_gt : (graph F).Adj (g • α) (g • t) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr ht
  have hga_y : (graph F).Adj (g • α) y := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hab
    change (graph F).Adj (g • α) (g • β) at hh
    rwa [hgt] at hh
  let p : BasedWalk (graph F) 6 (g • t) := reversePath g hgt hβu ht hy
  have hαu : α ≠ u := by
    intro he
    have hh := hc.1
    rw [he, SimpleGraph.dist_self] at hh
    omega
  have hβy : β ≠ y := hyne.symm
  have hα_gu : g • α ≠ u := by
    intro he
    apply hαu
    apply MulAction.injective (g : G₀ L S)
    exact he.trans hgu.symm
  have hy_gt : y ≠ g • t := by
    intro he
    apply htne
    apply MulAction.injective (g : G₀ L S)
    exact he.symm.trans hgt.symm
  have hnb : p.Nonbacktracking := by
    have hh : y ≠ g • t ∧ u ≠ g • α ∧ β ≠ y ∧ α ≠ u ∧ t ≠ β ∧ True :=
      ⟨hy_gt, hα_gu.symm, hβy, hαu, htne, True.intro⟩
    simpa only [p, reversePath, BasedWalk.Nonbacktracking] using hh
  have hRp : R ≤ pathStabilizer F p := by
    intro r hr z hz
    dsimp [p, reversePath] at hz
    change z ∈ [g • t,g • α,y,u,β,α,t] at hz
    simp at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((source_Z_Q_U H (g • α)).2.trans
        (ballKernel_one_le_edge F hga_gt)).trans inf_le_right (hRga hr)
    · exact Q_le_stabilizer _ _ (hRga hr)
    · exact Q_le_stabilizer _ _ (hRy hr)
    · exact ((source_Z_Q_U H y).2.trans
        (ballKernel_one_le_edge F hy.symm)).trans inf_le_right (hRy hr)
    · exact Q_le_stabilizer _ _ (hRbeta hr)
    · exact Q_le_stabilizer _ _ (hRalpha hr)
    · exact ((source_Z_Q_U H α).2.trans
        (ballKernel_one_le_edge F ht)).trans inf_le_right (hRalpha hr)
  have hnotQt : ¬ R ≤ Q F t := by
    intro hh
    apply hRne
    have hle : R ≤ R ⊓ Q F t := le_inf le_rfl hh
    rw [hRzero] at hle
    exact bot_unique hle
  have hr := graph_linear_path_rightRegular H (reduced_borel_core_sylow h)
    (reversePath g hgt hβu ht hy) c ho π hπ hk hgen R hRtwo
    (by simpa only [p] using hRp) hnotQt
  exact ⟨p, hnb, by simpa only [p] using hr⟩


/-- Reverse strict six-path regularity with its endpoint linear quotient
constructed from the source actor catalogue. Residual containments and the
edge-supplement identity remain explicit source premises. -/
public theorem reverse_six_path_rightRegular_of_source_linear
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    {g : G₀ L S} (hg : g ∈ graphLocalGroup F u) (hgt : g • β = y)
    {R : Subgroup (G₀ L S)} (hR : R = bTwoResidual F β y α (g • α))
    (hRne : R ≠ ⊥) (hRzero : R ⊓ Q F t = ⊥)
    (hRbeta : R ≤ Q F β) (hRy : R ≤ Q F y)
    (hRalpha : R ≤ Q F α) (hRga : R ≤ Q F (g • α))
    (hRtwo : IsPGroup 2 R)
    (hgen : pathStabilizer F (reversePath g hgt hβu ht hy) ⊔
        (stabilizer F (reversePath g hgt hβu ht hy).endpoint ⊓
          stabilizer F (reversePath g hgt hβu ht hy).penultimate).pCoreIn 2 =
        stabilizer F (reversePath g hgt hβu ht hy).endpoint ⊓
          stabilizer F (reversePath g hgt hβu ht hy).penultimate) :
    ∃ p : BasedWalk (graph F) 6 (g • t), p.Nonbacktracking ∧
      RightRegular (A := G₀ L S) p := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨n, hn, hm⟩ := reduced_noncommuting_actor_quotients_linear h hc hne t
  rcases hm with ⟨K, hK, hfin, hcard, ⟨e⟩⟩
  let := hK
  let := hfin
  let := Fintype.ofFinite K
  let := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let eSL : (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) ≃* SL(2,K) :=
    e.trans (Theory.PSL2.sl2QuotientEquiv K).symm
  let hm_t : IsRankOneModel
      (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) :=
    .linear n hn ⟨K, inferInstance, inferInstance, hcard, ⟨e⟩⟩
  obtain ⟨c, hcstar⟩ := graph_actor_localData_exists H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) ht.symm hm_t
  let := graph_local_core_normal t c
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F t) := by
    rw [hcstar]
    exact graph_actor_odd_index H t
  let f : (c.Pstar ⧸ (Q F t).subgroupOf c.Pstar) ≃*
      (graphLocalGroup F t ⧸ pCore 2 (graphLocalGroup F t)) := by
    have hcore : (Q F t).subgroupOf c.Pstar = pCore 2 c.Pstar := by
      rw [show Q F t = c.Pstar.pCoreIn 2 from c.same_core.symm]
      exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
    exact QuotientGroup.quotientMulEquivOfEq hcore
      |>.trans (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hcstar)
        (pCore_map_iso 2 (MulEquiv.subgroupCongr hcstar)))
  let π : c.Pstar →* SL(2,K) :=
    eSL.toMonoidHom.comp (f.toMonoidHom.comp
      (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar)))
  have hπ : Function.Surjective π :=
    eSL.surjective.comp (f.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : π.ker = (Q F t).subgroupOf c.Pstar := by
    ext a
    change eSL (f (QuotientGroup.mk' ((Q F t).subgroupOf c.Pstar) a)) = 1 ↔ _
    rw [eSL.map_eq_one_iff, f.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  exact reverse_six_path_rightRegular_of_residual h hc hne hb hβu ht htne hy hyne
    c ho π hπ hk hg hgt hR hRne hRzero hRbeta hRy hRalpha hRga hRtwo hgen

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
