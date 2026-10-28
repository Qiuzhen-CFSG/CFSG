module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CenterDisjointness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NeighborActions
public import Theory.SpecificGroups.Dihedral.SylowCosetExchange

/-!
# The disjoint-conjugate implication in DGS 8.6

Every local model exchanges two actual graph neighbors. The linear,
Suzuki and unitary cases use the marked edge transitivity already proved;
D₁₀ uses an involution in the literal Sylow-normalizer coset and lifts it
through the original local two-core quotient.

The exchange puts the commutator of the two opposite core intersections
in both H and its specified conjugate. Disjointness gives 8.6(b) implies
8.6(c). Together with central disjointness, this proves the (a)--(c) chain
at distance three across the full catalogue. The reduced F1.11 consumer
retains arbitrary orientation and the actual quotient and conjugation maps.
Distance three and central containment remain premises here; their general
proofs, the converse implication and equal fields stay in source assembly.

Source: DGS, *Groups and Graphs* (1985), 8.6, printed p.139.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem source_dihedral_neighbor_exchange
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5) :
    ∃ t ∈ d.localGroup v, t • x = y ∧ t • y = x := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hx
  let T := R.mapSurjective hq
  have hk : q.ker = pCore 2 L := by
    ext t
    change e (QuotientGroup.mk' (pCore 2 L) t) = 1 ↔ t ∈ pCore 2 L
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff t
  have hpre : (T : Subgroup (DihedralGroup 5)).comap q = R :=
    comap_map_eq_self (hk ▸ pCore_isPGroup.le_sylow_of_normal R)
  have hstab (l : L) : q l ∈ normalizer (T : Set (DihedralGroup 5)) ↔ (l : G) • x = x := by
    change l ∈ (normalizer ((T : Subgroup (DihedralGroup 5)) : Set _)).comap q ↔ _
    rw [comap_normalizer_eq_of_surjective _ hq,hpre,Sylow.coe_coe,
      ← (source_edge_local_normalizer h d hx (.dihedral ⟨e⟩) R hR).2]
    rfl
  obtain ⟨g,hg,hgx⟩ := d.transitive v ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨u,hu,hug⟩ := DihedralGroup.five_sylow_coset_exchange T (q ⟨g,hg⟩)
  obtain ⟨t,ht⟩ := hq u
  have hty : (t : G) • y = x := by
    have hh : q (t * ⟨g,hg⟩) ∈ normalizer (T : Set (DihedralGroup 5)) := by
      rw [q.map_mul,ht]
      exact hug
    have hh' := (hstab (t * ⟨g,hg⟩)).mp hh
    change ((t : G) * g) • x = x at hh'
    rwa [mul_smul,hgx] at hh'
  have htt : q (t * t) = 1 := by rw [q.map_mul,ht,hu]
  have httfix : ((t : G) * t) • x = x := (hstab (t*t)).mp (htt ▸ one_mem _)
  refine ⟨t,t.property,?_,hty⟩
  apply (MulAction.injective (t : G))
  change (t : G) • ((t : G) • x) = (t : G) • y
  rw [←mul_smul,httfix,hty]

theorem source_rank_one_neighbor_exchange
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v x y : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hy : (graph (family P)).Adj v y)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v))) :
    ∃ t ∈ d.localGroup v, t • x = y ∧ t • y = x := by
  by_cases he : x = y
  · exact ⟨1,one_mem _,by simp [he],by simp [he]⟩
  rcases source_edge_transitive_or_dihedral h hB d hy M with ht | hi
  · obtain ⟨g,hg,hgx⟩ := d.transitive v ⟨x,hx⟩ ⟨y,hy⟩
    have hgy : (graph (family P)).Adj v (g • y) := by
      have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hy
      change (graph (family P)).Adj (g • v) (g • y) at hh
      rwa [show g • v = v from d.local_le v hg] at hh
    have hne : g • y ≠ y := fun hh => he ((MulAction.injective g) (hgx.trans hh.symm))
    obtain ⟨k,hk,hky⟩ := ht (g • y) x hgy hx hne he
    exact ⟨k*g,(d.localGroup v).mul_mem hk.1 hg,
      by rw [mul_smul,hgx]; exact hk.2,by rw [mul_smul,hky]⟩
  · obtain ⟨e⟩ := hi
    exact source_dihedral_neighbor_exchange h hB d hx hy e

/-- DGS 8.6(b) implies 8.6(c), using an exchange of the two literal
neighbors. The displacement groups and conjugation maps are unchanged. -/
theorem source_disjoint_conjugates_intersection_commutes
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {beta a' mid : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid) (hne : beta ≠ a')
    (M : IsRankOneModel (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)))
    (hdis : ∀ g : G, g ∈ stabilizer (family P) mid →
      g ∉ stabilizer (family P) a' →
      Disjoint ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆
        ((⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆).map
          (MulAut.conj g).toMonoidHom)) :
    ⁅V (family P) beta 1 ⊓ Q (family P) a',
      V (family P) a' 1 ⊓ Q (family P) beta⁆ = ⊥ := by
  let := finite_endpoints h
  let F := family P
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  obtain ⟨t,ht,htb,hta⟩ := source_rank_one_neighbor_exchange h hB d hbm.symm ham.symm M
  have htescape : t ∉ stabilizer F a' := by
    intro hfix
    exact hne (hta.symm.trans hfix)
  have hdis' := hdis t (d.local_le mid ht) htescape
  have he : H.map (MulAut.conj t).toMonoidHom = ⁅V F a' 1 ⊓ Q F beta,V F beta 1⁆ := by
    rw [←displacement_translate,htb,hta]
  have h₁ : ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ ≤ H :=
    commutator_mono le_rfl inf_le_left
  have h₂ : ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ ≤
      H.map (MulAut.conj t).toMonoidHom := by
    rw [he,commutator_comm (V F a' 1 ⊓ Q F beta)]
    exact commutator_mono inf_le_left le_rfl
  exact bot_unique (hdis' h₁ h₂)

/-- At distance three, source 8.6(a) gives 8.6(c) for every local model.
No linear quotient or natural representation is assumed. -/
theorem source_distance_three_central_intersection_commutes
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : b (family P) = 3) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hH : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≤ Z (family P) a') :
    ⁅V (family P) beta 1 ⊓ Q (family P) a',
      V (family P) a' 1 ⊓ Q (family P) beta⁆ = ⊥ := by
  obtain ⟨mid,hbm,ham,hdis⟩ := source_distance_three_central_implies_disjoint
    h hB d models hc hab hd hb hcomm hH
  have hne : beta ≠ a' := by
    intro he
    rw [he,SimpleGraph.dist_self,hb] at hd
    omega
  exact source_disjoint_conjugates_intersection_commutes h hB d hbm ham hne (models mid) hdis

/-- The (a)--(c) chain of 8.6 on the original reduced F1.11 graph, in either
orientation and with the complete source local catalogue. Distance three and
the central-containment clause remain explicit pending 8.4 and 8.7. -/
theorem reduced_distance_three_central_intersection_commutes
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
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
    (hH : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≤ Z (Reduction.reducedFamily J S₀) a') :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1 ⊓ Q F beta⁆ = ⊥ := by
  exact source_distance_three_central_intersection_commutes (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    models hc hab hd hb hcomm hH

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
