module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelDihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelSylow

/-!
# Full-catalogue Borel and Sylow images on the critical path

The dihedral fourth-power argument completes the existing marked
transitive-model proof. Every retained middle model therefore gives the
full beta Borel on the literal path beta, alpha+2, alpha-prime. At critical
distance three the opposite neighborhood has a nonzero Borel-invariant
image in that root group, so its image is the entire Sylow and its core
index equals the beta field order.

This discharges the dihedral disjunct of the earlier conditional consumers.
Source: DGS, *Groups and Graphs* (1985), 8.5--8.7, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Every retained middle model gives the full beta Borel on the literal two-edge path. -/
theorem source_linear_path_borel_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid) (hne : beta ≠ a')
    (hescape : ¬ Q (family P) mid ≤ Q (family P) beta)
    (M : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃*
      SL(2,k)) :
    let F := family P
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
        normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : G) • mid = mid := by
  by_cases hnd : Nonempty ((d.localGroup mid ⧸ pCore 2 (d.localGroup mid)) ≃* DihedralGroup 5)
  · obtain ⟨em⟩ := hnd
    exact source_linear_path_borel_image_of_dihedral h hB hS d hbm ham hescape em e
  · exact source_linear_path_borel_image_of_not_dihedral h hB hS d hbm ham hne hescape M hnd e

/-- The original reduced path has its full Borel image, including the dihedral middle model. -/
theorem reduced_linear_path_borel_image
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓
          Q (Reduction.reducedFamily J S₀) v : Subgroup (Reduction.G₀ J S₀)) :
          Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {beta mid a' : Vertex (Reduction.reducedFamily J S₀)}
    (hbm : (graph (Reduction.reducedFamily J S₀)).Adj beta mid)
    (ham : (graph (Reduction.reducedFamily J S₀)).Adj a' mid)
    (hne : beta ≠ a')
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
        normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : Reduction.G₀ J S₀) • mid = mid := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hescape : ¬ Q F mid ≤ Q F beta := by
    exact core_escape_of_intersection_obstruction
      (F₀ := F) (v := beta) (w := mid) (hob mid beta hbm.symm)
  exact source_linear_path_borel_image ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    d hbm ham hne hescape (models mid) e


variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The chosen critical-distance-three path has full Borel image with no exceptional disjunct. -/
theorem reduced_critical_path_borel
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓
          Q (Reduction.reducedFamily J S₀) v : Subgroup (Reduction.G₀ J S₀)) :
          Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily J S₀))
    (hb : b (Reduction.reducedFamily J S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,
      Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
      V F beta 1 ≤ Q F mid ∧ ¬ Q F mid ≤ Q F a' ∧
      ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
        ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
          normalizer (T : Set SL(2,k)) ∧
        ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔
          (l : Reduction.G₀ J S₀) • mid = mid := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have hb1 : 1 < b F := by change 1 < b (Reduction.reducedFamily J S₀); omega
  obtain ⟨_,_,_,_,mid,ham,hdm,hVm,hescape⟩ :=
    source_critical_geometry ht d hc hab hd hb1 hcomm
  change (graph F).dist beta mid + 1 = (graph F).dist beta a' at hdm
  have hdist : (graph F).dist beta a' = 2 := by
    change (graph (Reduction.reducedFamily J S₀)).dist beta a' = 2
    omega
  have hbm : (graph F).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by
    omega)
  have hne : beta ≠ a' := by
    intro he
    simp only [he,SimpleGraph.dist_self] at hdist
    omega
  refine ⟨mid,hbm,ham,hVm,hescape,?_⟩
  exact reduced_linear_path_borel_image h hob models hbm ham hne e


/-- The terminal neighborhood fills the actual beta Sylow at critical distance three. -/
theorem reduced_critical_opposite_sylow
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : b (Reduction.reducedFamily J S₀) = 3)
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) beta)) ≃* SL(2,k)) :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
      (∃ T : Sylow 2 SL(2,k), ((V F a' 1).subgroupOf L).map q = T) ∧
        (Q F beta).relIndex (V F a' 1) = Nat.card k := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let L := graphLocalGroup F beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hb1 : 1 < b F := by change 1 < b (Reduction.reducedFamily J S₀); omega
  obtain ⟨mid,hbm,ham,_,_,hpath⟩ :=
    reduced_critical_path_borel h hob models hc hab hd hb hcomm e
  refine ⟨mid,hbm,ham,?_⟩
  obtain ⟨T,hT,hK,_⟩ := hpath
  have hAQ : V F a' 1 ≤ Q F mid := V_le_Q_of_dist_add_lt_b F ht.generate
    (fun v => (source_Z_Q_U ht v).1) a' mid 1
    (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr ham]; change 1+1 < b (Reduction.reducedFamily J S₀); omega)
    (Reduction.reduced_kernel_sylow h mid)
  have hAL : V F a' 1 ≤ L := hAQ.trans
    (neighbor_core_le_localGroup ht (Reduction.reduced_borel_core_sylow h)
      (Reduction.reduced_vertex_sylow h) hbm)
  have hesc := reduced_reciprocal_escape h hob models hc hab hd hb1 hcomm hne
  have he := source_path_normalized_sylow_image ht (V F a' 1) hAL hAQ hesc
    (stabilizer_normalizes_V F a' 1) e T hT hK
  change ((V F a' 1).subgroupOf L).map q = T at he
  refine ⟨⟨T,he⟩,?_⟩
  have hcard := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex
    L (Q F beta) (V F a' 1) q ?_ hAL
  · rw [he] at hcard
    exact hcard.symm.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 T).symm.toEquiv)
  · change q.ker = (Q F beta).subgroupOf L
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    have hcore : (pCore 2 L).map L.subtype = Q F beta := graphLocalGroup_core ht beta
    rw [←hcore]
    exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
