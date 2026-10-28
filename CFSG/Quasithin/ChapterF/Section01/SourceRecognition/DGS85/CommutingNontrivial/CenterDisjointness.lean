module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalEscape
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Central intersections in DGS 8.5 and 8.6

Two distinct edges at a vertex give distinct Sylow two-subgroups of its
local actor. The rank-one normalizer property makes them generate that
actor. A common element of the central neighboring center spans therefore
centralizes the actor; its center is trivial. This proves the implication
8.6(a) to 8.6(b), with the original graph action and conjugation map.

The nonzero critical commutator is a normal elementary abelian subgroup
of the terminal local actor. Inside a full edge Sylow it meets the center
nontrivially. The central edge seed identifies this intersection with the
terminal center span, giving the opening step of 8.5 on the reduced F1.11
graph. The nonnaturality conclusion of 8.5 and the other implications of
8.6 are separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 8.5 and 8.6(a)--(b), printed p.139.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem distinct_edge_sylows_generate
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (S T : Sylow 2 (d.localGroup v))
    (hS : (S : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (hT : (T : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) z).pCoreIn 2) :
    (S : Subgroup (d.localGroup v)) ⊔ T = ⊤ := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  by_contra he
  have hn := (rankOneSylowFacts_of_quotient S (M.rankOneSylowFacts _)).unique_maximal
    ((S : Subgroup L) ⊔ T) le_sup_left (lt_top_iff_ne_top.mpr he)
  have hTN : (T : Subgroup L) ≤ normalizer (S : Set L) := le_sup_right.trans hn
  have hTS : (T : Subgroup L) ≤ S := by
    have hi := T.isPGroup'.inf_normalizer_sylow S
    rw [inf_eq_left.mpr hTN] at hi
    exact inf_eq_left.mp hi.symm
  have hST : T = S := Sylow.ext (T.is_maximal' S.isPGroup' hTS).symm
  apply hne
  exact (source_edge_sylow_unique_neighbor h d hw hz M S hS (by
    rw [←hST,hT]
    exact (pCoreIn_le 2 _).trans inf_le_right)).symm

/-- Distinct neighbors in the central orbit have disjoint center spans. -/
theorem source_central_neighbor_centers_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (hz : (graph (family P)).Adj v z) (hne : w ≠ z)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w)) :
    Disjoint (Z (family P) w) (Z (family P) z) := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  obtain ⟨g,hg,hgz⟩ := d.transitive v ⟨w,hw⟩ ⟨z,hz⟩
  change g • w = z at hgz
  have hcentralz : Z F z = omegaCenterIn (d.localGroup z) := by
    rw [←hgz,Z_translate,d.conjugate,
      ←NilesRankOneKernel.omegaCenterIn_map_injective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hcentral]
  obtain ⟨S,hS⟩ := source_edge_core_local_sylow h hB d hw
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hz
  have hgen := distinct_edge_sylows_generate h d hw hz hne M S T hS hT
  have hs := (source_central_edge_seed h hB d hw hcentral).1
  have ht := (source_central_edge_seed h hB d hz hcentralz).1
  rw [←hS] at hs
  rw [←hT] at ht
  have hc := local_center_eq_bot_of_neighbor_central h d hw hcentral
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  have hxS := (mem_omegaCenterIn_iff _ _).mp (hs.symm ▸ hx.1)
  have hxT := (mem_omegaCenterIn_iff _ _).mp (ht.symm ▸ hx.2)
  have hxL : x ∈ L := (map_subtype_le _) hxS.1
  have hC : (S : Subgroup L) ⊔ T ≤ (centralizer ({x} : Set G)).subgroupOf L := by
    apply sup_le
    · intro s hs
      change (s : G) ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact hxS.2.1 s (mem_map_of_mem L.subtype hs)
    · intro t ht
      change (t : G) ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact hxT.2.1 t (mem_map_of_mem L.subtype ht)
  have hxZ : (⟨x,hxL⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro l
    have hh := hC (hgen.symm ▸ mem_top l)
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hh)
  rw [hc,mem_bot] at hxZ
  exact congrArg Subtype.val hxZ

/-- A subgroup of a central neighboring span is disjoint from every conjugate
that moves that neighbor while fixing the middle vertex. -/
theorem source_central_subgroup_disjoint_conjugate
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hcentral : Z (family P) w = omegaCenterIn (d.localGroup w))
    (H : Subgroup G) (hH : H ≤ Z (family P) w)
    (g : G) (hgv : g ∈ stabilizer (family P) v)
    (hgw : g ∉ stabilizer (family P) w) :
    Disjoint H (H.map (MulAut.conj g).toMonoidHom) := by
  let := finite_endpoints h
  have hz : (graph (family P)).Adj v (g • w) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hw
    change (graph (family P)).Adj (g • v) (g • w) at hh
    rwa [show g • v = v from hgv] at hh
  have hne : w ≠ g • w := fun he => hgw he.symm
  have hd := source_central_neighbor_centers_disjoint h hB d hw hz hne M hcentral
  rw [Z_translate] at hd
  exact hd.mono hH (map_mono hH)

/-- The opening step of 8.5: the nonzero critical commutator meets the
terminal center span nontrivially, with normality in the actual local actor. -/
theorem source_critical_commutator_meets_terminal_center
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    (models : ∀ v : Vertex (family P),
      IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥) :
    ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ⊓ Z (family P) a' ≠ ⊥ := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup a'
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let : Finite L := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U h v).1) beta a' hne
  obtain ⟨hn,hHZ,_⟩ := source_critical_commutator_structure h hB d hc hab hd hb hcomm models
  have hHL : H ≤ L := (hHZ w).trans
    (((Z_neighbor_le_V F w.property).trans
      (V_le_Q_of_dist_add_lt_b F h.generate (fun v => (source_Z_Q_U h v).1)
        a' a' 1 (by simpa using hb) (d.kernel_sylow a'))).trans
        ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default)))
  let := CommutingOneProfile.source_center_elementary h w.val
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (hHZ w)
  let : (H.subgroupOf L).Normal := hn
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d w.property
  have hpH : IsPGroup 2 (H.subgroupOf L) := (IsElementaryAbelian.isPGroup 2 H).comap_subtype
  have hHS : H.subgroupOf L ≤ R := hpH.le_sylow_of_normal R
  let K := (H.subgroupOf L).subgroupOf (R : Subgroup L)
  let : K.Normal := inferInstance
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr (by
    intro he
    apply hne
    apply bot_unique
    intro x hx
    have hxK : (⟨⟨x,hHL hx⟩,hHS hx⟩ : R) ∈ K := hx
    rw [he,mem_bot] at hxK
    exact congrArg (fun r : R => ((r : L) : G)) hxK)
  let : Fact (IsPGroup 2 R) := ⟨R.isPGroup'⟩
  obtain ⟨x,hxne,hxc⟩ := exists_nontrivial_center_mem_normal K (p := 2)
  let y : G := x.val.val.val
  have hyH : y ∈ H := x.property
  have hyS : y ∈ (R : Subgroup L).map L.subtype :=
    mem_map_of_mem L.subtype x.val.property
  have hyO : y ∈ omegaCenterIn ((R : Subgroup L).map L.subtype) := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨hyS,?_,elemPow_eq_one_of_isElementaryAbelian (p := 2) y hyH⟩
    rintro z ⟨l,hl,rfl⟩
    exact congrArg (fun r : R => ((r : L) : G)) (mem_center_iff.mp hxc ⟨l,hl⟩)
  have hcentral := critical_end_center_of_commuting F h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2)
    hc hcomm L (d.sylow_or_center a')
  have hseed := (source_central_edge_seed h hB d w.property.symm hcentral).1
  rw [inf_comm,←hR] at hseed
  have hyZ : y ∈ Z F a' := hseed ▸ hyO
  intro he
  have hy1 : y = 1 := mem_bot.mp (he ▸ (show y ∈ H ⊓ Z F a' from ⟨hyH,hyZ⟩))
  exact hxne (Subtype.ext (Subtype.ext (Subtype.ext hy1)))

/-- Source 8.6(a) implies 8.6(b) at the literal distance-three critical path.
The central-containment premise is explicit; no equivalence is asserted here. -/
theorem source_distance_three_central_implies_disjoint
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
    let F := family P
    let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
    ∃ mid : Vertex F, (graph F).Adj beta mid ∧ (graph F).Adj a' mid ∧
      ∀ g : G, g ∈ stabilizer F mid → g ∉ stabilizer F a' →
        Disjoint H (H.map (MulAut.conj g).toMonoidHom) := by
  let := finite_endpoints h
  have hb1 : 1 < b (family P) := by omega
  obtain ⟨_,_,_,_,mid,hm,hdm,_,_⟩ := source_critical_geometry h d hc hab hd hb1 hcomm
  have hbm : (graph (family P)).Adj beta mid := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have hcentral := critical_end_center_of_commuting (family P) h.generate
    (fun v => (source_Z_Q_U h v).1) (fun v => (source_Z_Q_U h v).2)
    hc hcomm (d.localGroup a') (d.sylow_or_center a')
  exact ⟨mid,hbm,hm,fun g hgm hga => source_central_subgroup_disjoint_conjugate
    h hB d hm.symm (models mid) hcentral _ hH g hgm hga⟩

variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The nonzero terminal-center intersection of 8.5 on an arbitrarily oriented
reduced F1.11 critical pair, retaining the earlier 6.5 and catalogue inputs. -/
theorem reduced_critical_commutator_meets_terminal_center
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
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    :
    let F := Reduction.reducedFamily J S₀
    ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ⊓ Z F a' ≠ ⊥ := by
  exact source_critical_commutator_meets_terminal_center (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    models hc hab hd hb hcomm hne

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
