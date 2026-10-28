module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorelApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication

/-!
# The opposite neighborhood fills the path Sylow

At critical distance three, the terminal neighborhood lies in the middle
core and escapes the beta core by 8.2. The path stabilizer normalizes that
neighborhood and maps onto the beta Borel. Borel invariance therefore makes
its nonzero image the full Sylow subgroup, giving its exact core index.
The dihedral middle exception is retained explicitly.

Source: DGS, *Groups and Graphs* (1985), 8.5--8.7, printed pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A terminal-normalized subgroup filling a nonzero part of the path root
fills the entire root. The hypotheses use the literal beta quotient. -/
theorem source_path_normalized_sylow_image
    (h : LocallyRankOneTriple P B) {beta mid a' : Vertex (family P)}
    (A : Subgroup G) (hAL : A ≤ graphLocalGroup (family P) beta)
    (hAQ : A ≤ Q (family P) mid) (hescape : ¬ A ≤ Q (family P) beta)
    (hn : stabilizer (family P) a' ≤ normalizer (A : Set G))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,k))
    (T : Sylow 2 SL(2,k))
    (hT : ((Q (family P) mid).subgroupOf (graphLocalGroup (family P) beta)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))) = T)
    (hK : ((stabilizer (family P) mid ⊓ stabilizer (family P) a').subgroupOf
      (graphLocalGroup (family P) beta)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))) =
      normalizer (T : Set SL(2,k))) :
    (A.subgroupOf (graphLocalGroup (family P) beta)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))) = T := by
  let L := graphLocalGroup (family P) beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let I := (A.subgroupOf L).map q
  apply Matrix.SpecialLinearGroup.sylow_eq_of_normalized T I
  · exact hT ▸ map_mono (comap_mono hAQ)
  · intro hbot
    apply hescape
    intro x hx
    have hm := mem_map_of_mem q (show (⟨x,hAL hx⟩ : L) ∈ A.subgroupOf L from hx)
    have h1 : q ⟨x,hAL hx⟩ = 1 := (show q ⟨x,hAL hx⟩ ∈ (⊥ : Subgroup SL(2,k)) from hbot ▸ hm)
    have hk : (⟨x,hAL hx⟩ : L) ∈ pCore 2 L :=
      (QuotientGroup.eq_one_iff _).mp (e.injective (h1.trans e.map_one.symm))
    exact (graphLocalGroup_core h beta) ▸ mem_map_of_mem L.subtype hk
  · intro x hx
    rw [←hK] at hx
    obtain ⟨l,hl,rfl⟩ := hx
    have hln : l ∈ normalizer (A.subgroupOf L : Set L) := by
      rw [←subgroupOf_normalizer_eq hAL]
      exact hn hl.2
    exact le_normalizer_map q (mem_map_of_mem q hln)

/-- The whole opposite neighborhood, rather than merely a moving center,
is the full beta Sylow. Thus its core index is exactly the beta field size. -/
theorem reduced_critical_opposite_sylow_or_dihedral
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
      (Nonempty ((graphLocalGroup F mid ⧸ pCore 2 (graphLocalGroup F mid)) ≃* DihedralGroup 5) ∨
      (∃ T : Sylow 2 SL(2,k), ((V F a' 1).subgroupOf L).map q = T) ∧
        (Q F beta).relIndex (V F a' 1) = Nat.card k) := by
  let F := Reduction.reducedFamily J S₀
  let ht := Reduction.reduced_triple h
  let L := graphLocalGroup F beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hb1 : 1 < b F := by change 1 < b (Reduction.reducedFamily J S₀); omega
  obtain ⟨mid,hbm,ham,_,_,hpath⟩ :=
    reduced_critical_path_borel_or_dihedral h hob models hc hab hd hb hcomm e
  refine ⟨mid,hbm,ham,?_⟩
  rcases hpath with hdi | ⟨T,hT,hK,_⟩
  · exact Or.inl hdi
  · have hAQ : V F a' 1 ≤ Q F mid := V_le_Q_of_dist_add_lt_b F ht.generate
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
    refine Or.inr ⟨⟨T,he⟩,?_⟩
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
