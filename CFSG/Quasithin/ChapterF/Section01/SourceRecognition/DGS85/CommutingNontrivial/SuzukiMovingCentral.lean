module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborOmegaFixed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralEquivalencesSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import Theory.SpecificGroups.Suzuki.DistinctOmegaGeneration
public import Theory.SpecificGroups.Suzuki.SmallOmegaResidual
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiOddFixedSpaces

/-!
# Moving Suzuki neighbors in the commuting critical case

At a middle neighbor, the source commutator and its reverse centralize the
full omega preimages of two distinct edge Sylows. The join of those omega
subgroups contains the odd residual, including at the binary parameter.
Their intersection commutator lies in a Sylow two-subgroup and centralizes
the local residual, hence is trivial because the middle local group is
centerless. The source equivalences (8.6) identify the original commutator
with the terminal center.

This supplies every Suzuki moving row of DGS85, *Groups and Graphs*,
(8.7), printed pp.139--140, using the original critical configuration.
-/

@[expose] public noncomputable section
open Subgroup Representation BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G]

private theorem suzuki_omega_preimages_cover_residual (M : Subgroup G) [Finite M]
    {m : ℕ} (e : (M ⧸ pCore 2 M) ≃* SuzukiMatrixGroup m)
    (R T : Sylow 2 M) (hne : R ≠ T) :
    (pResidual 2 M).map M.subtype ≤
      quotientSylowOmegaPreimage M R ⊔ quotientSylowOmegaPreimage M T := by
  let q := QuotientGroup.mk' (pCore 2 M)
  let Rq := R.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
  let Tq := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 M))
  have hneQ : Rq ≠ Tq := by
    intro he
    have hh := congrArg (fun S : Sylow 2 (M ⧸ pCore 2 M) => (S : Subgroup _).comap q) he
    change ((R : Subgroup M).map q).comap q = ((T : Subgroup M).map q).comap q at hh
    rw [comap_map_eq_self,comap_map_eq_self] at hh
    · exact hne (Sylow.ext hh)
    · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal T
    · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal R
  let R' := Rq.mapSurjective (f := e.toMonoidHom) e.surjective
  let T' := Tq.mapSurjective (f := e.toMonoidHom) e.surjective
  have hne' : R' ≠ T' := by
    intro he
    apply hneQ
    apply Sylow.ext
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact congrArg (fun S : Sylow 2 (SuzukiMatrixGroup m) => (S : Subgroup (SuzukiMatrixGroup m))) he
  have ho : pResidual 2 (M ⧸ pCore 2 M) ≤
      omegaCenterIn (Rq : Subgroup (M ⧸ pCore 2 M)) ⊔
      omegaCenterIn (Tq : Subgroup (M ⧸ pCore 2 M)) := by
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [Subgroup.map_sup,Subgroup.map_pResidual,
      NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective,
      NilesRankOneKernel.omegaCenterIn_map_injective _ e.injective]
    change pResidual 2 (SuzukiMatrixGroup m) ≤
      omegaCenterIn (R' : Subgroup (SuzukiMatrixGroup m)) ⊔
      omegaCenterIn (T' : Subgroup (SuzukiMatrixGroup m))
    rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
      Representation.RankOne.QuadraticRecognition.suzuki_omega_center_eq,
      Representation.RankOne.QuadraticRecognition.suzuki_omega_center_eq]
    rcases Nat.eq_zero_or_pos m with rfl|hm
    · exact suzukiZero_twoResidual_le_distinct_omega_sup R' T' hne'
    · rw [suzukiSylow_distinct_omega_sup_eq_top hm R' T' hne']
      exact le_top
  unfold quotientSylowOmegaPreimage
  rw [←Subgroup.map_sup]
  apply map_mono
  change pResidual 2 M ≤
    (omegaCenterIn (Rq : Subgroup (M ⧸ pCore 2 M))).comap q ⊔
    (omegaCenterIn (Tq : Subgroup (M ⧸ pCore 2 M))).comap q
  rw [comap_sup_eq q _ _ (QuotientGroup.mk'_surjective _)]
  exact map_le_iff_le_comap.mp ((map_pResidual_le 2 q).trans ho)

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The literal intersection condition (8.6)(c) holds when the middle
quotient is any Suzuki model, including Sz(2). -/
theorem reduced_suzuki_all_middle_intersection_commutes
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' mid : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hbm : (graph (Reduction.reducedFamily J S₀)).Adj beta mid)
    (ham : (graph (Reduction.reducedFamily J S₀)).Adj a' mid)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) mid ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) mid)) ≃* SuzukiMatrixGroup m) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥ := by
  let ht := Reduction.reduced_triple h
  let hB := Reduction.reduced_borel_core_sylow h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  let A := V F beta 1 ⊓ Q F a'
  let B' := V F a' 1 ⊓ Q F beta
  let H := ⁅A,V F a' 1⁆
  let H' := ⁅B',V F beta 1⁆
  let M := d.localGroup mid
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite M := Finite.of_injective (inclusion (d.local_le mid)) (inclusion_injective _)
  change ⁅A,B'⁆ = ⊥
  by_contra hI
  have hrev : H' ≠ ⊥ := by
    intro he
    apply hI
    rw [commutator_comm]
    exact bot_unique ((commutator_mono le_rfl inf_le_left).trans he.le)
  obtain ⟨_,z,hza,hcz,hdrev,hzc,_⟩ := reduced_reciprocal_critical_configuration h
    (Reduction.reduced_graph_core_obstruction h) models hc hab hd hb hcomm hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht hB d ham.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht hB d hbm.symm
  have hHR := source_critical_neighbor_omega_fixed ht hB d models hc hab hd hb hcomm hne ⟨mid,ham⟩ R hR
  have hHT := source_critical_neighbor_omega_fixed ht hB d models hcz hza hdrev hb hzc hrev ⟨mid,hbm⟩ T hT
  have hba : beta ≠ a' := by
    intro he
    have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
    rw [he,SimpleGraph.dist_self,hb3] at hd
    omega
  have hRT : R ≠ T := by
    intro he
    apply hba
    apply source_edge_sylow_unique_neighbor ht d ham.symm hbm.symm (models mid) R hR
    rw [he,hT]
    exact (pCoreIn_le 2 _).trans inf_le_right
  have hcover := suzuki_omega_preimages_cover_residual M e R T hRT
  have hcen : ⁅A,B'⁆ ≤ centralizer
      ((pResidual 2 M).map M.subtype : Set (Reduction.G₀ J S₀)) := by
    apply le_centralizer_iff.mp
    apply hcover.trans
    apply sup_le
    · exact le_centralizer_iff.mp ((commutator_mono le_rfl inf_le_left).trans (hHR.trans inf_le_right))
    · rw [commutator_comm A B']
      exact le_centralizer_iff.mp ((commutator_mono le_rfl inf_le_left).trans (hHT.trans inf_le_right))
  have hZ : ⁅A,B'⁆ ≤ Z F mid :=
    (commutator_mono le_rfl inf_le_left).trans (hHR.trans inf_le_left)
  have hz : center M = ⊥ := local_center_eq_bot_of_neighbor_central ht d ham.symm
    (critical_end_center_of_commuting F ht.generate (fun v => (source_Z_Q_U ht v).1)
      (fun v => (source_Z_Q_U ht v).2) hc hcomm (d.localGroup a') (d.sylow_or_center a'))
  have hZL : Z F mid ≤ M := by
    let : IsElementaryAbelian 2 (Z F mid) := CommutingOneProfile.source_center_elementary ht mid
    exact pGroup_le_localGroup F d mid _ (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F mid)
  let : IsElementaryAbelian 2 (Z F mid) := CommutingOneProfile.source_center_elementary ht mid
  have hp : IsPGroup 2 ((Z F mid).subgroupOf M) :=
    (IsElementaryAbelian.isPGroup 2 (Z F mid)).comap_subtype
  obtain ⟨U,hU⟩ := hp.exists_le_sylow
  have hbot := sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot U hz
  apply hI
  apply bot_unique
  intro x hx
  have hxm : (⟨x,hZL (hZ hx)⟩ : M) ∈ (U : Subgroup M) ⊓
      centralizer (pResidual 2 M : Set M) := by
    refine ⟨hU (hZ hx),?_⟩
    intro y hy
    exact Subtype.ext ((hcen hx) y.val (mem_map_of_mem M.subtype hy))
  rw [hbot,mem_bot] at hxm
  exact congrArg Subtype.val hxm

/-- Every Suzuki moving neighbor forces the actual source
commutator to be the terminal center. -/
theorem reduced_suzuki_all_moving_commutator_central
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hmove : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* SuzukiMatrixGroup m) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedFullEarlierLocalTheorems h
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro he
    exact hmove (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans he.le))
  have hb3 := reduced_distance_three_of_catalogue h models hc hab hd hb hcomm hne
  have hba : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self,hb3] at hd
    omega
  obtain ⟨mid,ham,hdm⟩ := exists_predecessor F ht.generate beta a' hba
  have hbm : (graph F).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by
    have hh : (graph F).dist beta a'+1=3 := hd.trans hb3
    omega)
  obtain ⟨g,hg,hgm⟩ := d.transitive a' w ⟨mid,ham⟩
  obtain ⟨_,f,_,_,_⟩ := CommutingTrivial.local_quotient_parameter_transport ht g hgm
  have hI := reduced_suzuki_all_middle_intersection_commutes h models hc hab hd hb hcomm hne hbm ham m (f.symm.trans e)
  exact (reduced_terminal_intersection_natural h models hc hab hd hb hcomm hne hI).2.1



/-- Positive-parameter specialization of the all-parameter Suzuki result. -/
theorem reduced_suzuki_middle_intersection_commutes
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' mid : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hbm : (graph (Reduction.reducedFamily J S₀)).Adj beta mid)
    (ham : (graph (Reduction.reducedFamily J S₀)).Adj a' mid)
    {m : ℕ} (_hm : 0 < m)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) mid ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) mid)) ≃* SuzukiMatrixGroup m) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥ := by
  exact reduced_suzuki_all_middle_intersection_commutes h models hc hab hd hb hcomm hne hbm ham m e

/-- Positive-parameter specialization of the all-parameter Suzuki result. -/
theorem reduced_suzuki_moving_commutator_central
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hmove : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    {m : ℕ} (_hm : 0 < m)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) ≃* SuzukiMatrixGroup m) :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ = Z F a' := by
  exact reduced_suzuki_all_moving_commutator_central h models hc hab hd hb hcomm w hmove m e

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
