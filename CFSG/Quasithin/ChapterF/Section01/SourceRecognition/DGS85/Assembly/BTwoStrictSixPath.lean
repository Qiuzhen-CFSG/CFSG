module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoCartanResidualOrderPathConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LinearPathAction
open Subgroup SimpleGraph SimpleGraph.BasedWalk
open Theory.GroupAction.CubicTree
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Reduction Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

/-- The Cartan residual furnishes a six-path whose endpoint action is right-regular.
The linear local quotient and odd-index marking are explicit because they are
source inputs at the terminal endpoint. -/
public theorem original_bTwo_six_path_rightRegular_of_linear
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (c : LocalRankOneData (stabilizer F y)
      (stabilizer F y ⊓ stabilizer F u))
    (ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F y))
    (π : c.Pstar →* SL(2,k)) (hπ : Function.Surjective π)
    (hk : π.ker = (Q F y).subgroupOf c.Pstar) :
    ∃ g : G₀ L S, g ∈ graphLocalGroup F α ∧ g • β = t ∧
      ∃ p : BasedWalk (graph F) 6 (g • y),
        p.vertices = [g • y, g • u, t, α, β, u, y] ∧
        p.Nonbacktracking ∧ RightRegular (A := G₀ L S) p := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨K,hfix,hd,hgen,hoK,hcomm,hprod,g,hg,hgK,hgt,a,ha,haK,hau,
    hW,hR,hdec,hdis,hdisu,hKn,hRC,hJC,hthree,hconj,hRne,hzero⟩ :=
      original_bTwo_path_cartan_residual_trivial h hc hne hb hβu ht htne hy hyne hns
  let R := bTwoResidual F β t u (g • u)
  have hgygu : (graph F).Adj (g • y) (g • u) :=
    (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hy.symm
  have hgu_t : (graph F).Adj (g • u) t := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hβu
    change (graph F).Adj (g • β) (g • u) at hh
    rw [hgt] at hh
    exact hh.symm
  have hab : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide, Subgroup.CosetGeometry.incident_base _ _ _⟩
  let p : BasedWalk (graph F) 6 (g • y) :=
    ⟨⟨g • u,hgygu⟩,⟨⟨t,hgu_t⟩,⟨⟨α,ht.symm⟩,⟨⟨β,hab⟩,⟨⟨u,hβu⟩,⟨⟨y,hy⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
  have hαu : α ≠ u := by
    intro he
    have hd0 := hc.1
    rw [he, SimpleGraph.dist_self] at hd0
    omega
  have hguα : g • u ≠ α := by
    intro he
    apply hαu
    apply MulAction.injective g
    exact (he.trans (sylowGenerated_le _ hg).symm).symm
  have hgyt : g • y ≠ t := by
    intro he
    apply hyne
    apply (MulAction.injective g)
    calc
      g • y = t := he
      _ = g • β := hgt.symm
  have hnb : p.Nonbacktracking := by
    have hnb' : t ≠ g • y ∧ α ≠ g • u ∧ β ≠ t ∧ u ≠ α ∧ y ≠ β ∧ True :=
      ⟨hgyt.symm, hguα.symm, htne.symm, hαu.symm, hyne, True.intro⟩
    simpa only [p, BasedWalk.Nonbacktracking] using hnb'
  have hRdecomp : R = (D F β t ⊓ Q F u) ⊓ Q F (g • u) := hR
  have hRbeta : R ≤ Q F β := by rw [hRdecomp]; exact (inf_le_left.trans inf_le_left).trans inf_le_left
  have hRt : R ≤ Q F t := by rw [hRdecomp]; exact (inf_le_left.trans inf_le_left).trans inf_le_right
  have hRu : R ≤ Q F u := by rw [hRdecomp]; exact inf_le_left.trans inf_le_right
  have hRgu : R ≤ Q F (g • u) := by rw [hRdecomp]; exact inf_le_right
  have hRp : R ≤ pathStabilizer F p := by
    intro r hr z hz
    change z ∈ [g • y,g • u,t,α,β,u,y] at hz
    simp at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ((source_Z_Q_U H (g • u)).2.trans (ballKernel_one_le_edge F hgygu.symm)).trans inf_le_right (hRgu hr)
    · exact Q_le_stabilizer _ _ (hRgu hr)
    · exact Q_le_stabilizer _ _ (hRt hr)
    · exact ((source_Z_Q_U H β).2.trans (ballKernel_one_le_edge F hab.symm)).trans inf_le_right (hRbeta hr)
    · exact Q_le_stabilizer _ _ (hRbeta hr)
    · exact Q_le_stabilizer _ _ (hRu hr)
    · exact ((source_Z_Q_U H u).2.trans (ballKernel_one_le_edge F hy)).trans inf_le_right (hRu hr)
  have hKt : K ≤ stabilizer F t := fun z hz => (hfix hz).1.1.1.1
  have hKα : K ≤ stabilizer F α := fun z hz => (hfix hz).1.1.1.2
  have hKβ : K ≤ stabilizer F β := fun z hz => (hfix hz).1.1.2
  have hKu : K ≤ stabilizer F u := fun z hz => (hfix hz).1.2
  have hKy : K ≤ stabilizer F y := fun z hz => (hfix hz).2
  have hKuy : K ≤ stabilizer F u ⊓ stabilizer F y := le_inf hKu hKy
  have hKE : K ≤ stabilizer F α ⊓ stabilizer F β :=
    le_inf (fun z hz => (hfix hz).1.1.1.2) (fun z hz => (hfix hz).1.1.2)
  obtain ⟨hdy,hgeny⟩ := CommutingTrivial.path_cartan_complement_at_edge H hab hy.symm K
    hKE (by simpa only [inf_comm] using hKuy) hoK hd hgen
  have htransport (v : Vertex F) (hv : K ≤ stabilizer F v) (z : G₀ L S) (hz : z ∈ K) :
      z • (g • v) = g • v := by
    have hz' : (g⁻¹ * z * g : G₀ L S) ∈ K := by
      have hginv : g⁻¹ ∈ normalizer (K : Set (G₀ L S)) := (normalizer (K : Set (G₀ L S))).inv_mem hgK
      have hi := mem_normalizer_iff_map_conj_eq.mp hginv
      have hzconj : (MulAut.conj g⁻¹) z ∈ K := by
        rw [← hi]
        exact mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hz
      simpa only [MulAut.conj_apply, inv_inv] using hzconj
    calc
      z • (g • v) = (z * g) • v := by rw [← mul_smul]
      _ = (g * (g⁻¹ * z * g)) • v := by congr 1; group
      _ = g • ((g⁻¹ * z * g) • v) := by rw [mul_smul]
      _ = g • v := by rw [show (g⁻¹ * z * g) • v = v from hv hz']
  have hKp : K ≤ pathStabilizer F p := by
    intro z hz w hw
    change w ∈ [g • y,g • u,t,α,β,u,y] at hw
    simp at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact htransport y hKy z hz
    · exact htransport u hKu z hz
    · exact hKt hz
    · exact hKα hz
    · exact hKβ hz
    · exact hKu hz
    · exact hKy hz
  have hgenp : pathStabilizer F p ⊔
      (stabilizer F p.endpoint ⊓ stabilizer F p.penultimate).pCoreIn 2 =
      stabilizer F p.endpoint ⊓ stabilizer F p.penultimate := by
    have hpE : p.endpoint = y := rfl
    have hpP : p.penultimate = u := rfl
    rw [hpE, hpP]
    have hYmem : y ∈ p.vertices := by change y ∈ [g • y,g • u,t,α,β,u,y]; simp
    have hUmem : u ∈ p.vertices := by change u ∈ [g • y,g • u,t,α,β,u,y]; simp
    apply le_antisymm (sup_le (pathStabilizer_le_edge F p hYmem hUmem) (pCoreIn_le _ _))
    exact hgeny.symm.le.trans (sup_le_sup_right hKp _)
  have hnotQ : ¬ R ≤ Q F y := by
    intro hh
    apply hRne
    have hle : R ≤ R ⊓ Q F y := le_inf le_rfl hh
    rw [hzero] at hle
    exact bot_unique hle
  have hr := graph_linear_path_rightRegular H (reduced_borel_core_sylow h) p c ho π hπ hk hgenp R
    ((isPGroup_pCoreIn 2 (stabilizer F β)).to_le hRbeta)
    hRp hnotQ
  exact ⟨g,hg,hgt,p,rfl,hnb,hr⟩

/-- The strict six-path regularity with the endpoint linear model selected from
`HypothesisF11`; this is the source-facing wrapper around the explicit quotient
marking theorem above. -/
public theorem original_bTwo_six_path_rightRegular_of_source_linear
    (h : HypothesisF11 L S) {u t y : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (hy : (graph F).Adj u y) (hyne : y ≠ β)
    (hns : ¬ Group.IsSolvable (parabolic L S 0)) :
    ∃ g : G₀ L S, g ∈ graphLocalGroup F α ∧ g • β = t ∧
      ∃ p : BasedWalk (graph F) 6 (g • y),
        p.vertices = [g • y, g • u, t, α, β, u, y] ∧
        p.Nonbacktracking ∧ RightRegular (A := G₀ L S) p := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F i) := finite_endpoints H
  obtain ⟨n, hn, hm⟩ := reduced_noncommuting_actor_quotients_linear h hc hne y
  rcases hm with ⟨K, hK, hfin, hcard, ⟨e⟩⟩
  let := hK
  let := hfin
  let := Fintype.ofFinite K
  let := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let eSL : (graphLocalGroup F y ⧸ pCore 2 (graphLocalGroup F y)) ≃* SL(2,K) :=
    e.trans (Theory.PSL2.sl2QuotientEquiv K).symm
  let hm_y : IsRankOneModel
      (graphLocalGroup F y ⧸ pCore 2 (graphLocalGroup F y)) :=
    .linear n hn ⟨K, inferInstance, inferInstance, hcard, ⟨e⟩⟩
  obtain ⟨c, hcstar⟩ := graph_actor_localData_exists H
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hy.symm hm_y
  let := graph_local_core_normal y c
  have ho : ¬ 2 ∣ c.Pstar.relIndex (stabilizer F y) := by
    rw [hcstar]
    exact graph_actor_odd_index H y
  let f : (c.Pstar ⧸ (Q F y).subgroupOf c.Pstar) ≃*
      (graphLocalGroup F y ⧸ pCore 2 (graphLocalGroup F y)) := by
    have hcore : (Q F y).subgroupOf c.Pstar = pCore 2 c.Pstar := by
      rw [show Q F y = c.Pstar.pCoreIn 2 from c.same_core.symm]
      exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
    exact QuotientGroup.quotientMulEquivOfEq hcore
      |>.trans (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hcstar)
        (pCore_map_iso 2 (MulEquiv.subgroupCongr hcstar)))
  let π : c.Pstar →* SL(2,K) :=
    eSL.toMonoidHom.comp (f.toMonoidHom.comp
      (QuotientGroup.mk' ((Q F y).subgroupOf c.Pstar)))
  have hπ : Function.Surjective π :=
    eSL.surjective.comp (f.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : π.ker = (Q F y).subgroupOf c.Pstar := by
    ext a
    change eSL (f (QuotientGroup.mk' ((Q F y).subgroupOf c.Pstar) a)) = 1 ↔ _
    rw [eSL.map_eq_one_iff, f.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff a
  exact original_bTwo_six_path_rightRegular_of_linear h hc hne hb hβu ht htne hy hyne hns
    c ho π hπ hk

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
