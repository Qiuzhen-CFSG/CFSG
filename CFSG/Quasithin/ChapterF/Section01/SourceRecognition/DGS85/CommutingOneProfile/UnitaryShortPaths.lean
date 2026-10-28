module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryInitial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.RootedExtensions

/-!
# Short paths in the commuting linear–unitary configuration

The unitary beta marking supplies the full adjacent-core product through
(11.4)--(11.5). At alpha the exceptional dihedral quotient is excluded;
at beta both unitary covers give the marked two-transitive neighbor action.
Transporting these actions to every edge makes the preceding vertex core
transitive on forward neighbors. That core fixes a two-edge path, giving
three-walk transitivity at every vertex of the original graph.

This supplies the three-edge path used by `UnitaryRemoteLayer` in (11.6).
It does not assume a tree or the later four- and five-walk profiles.
Source: DGS85, Groups and Graphs, (3.4), (11.4)--(11.6), pp.74,171--173.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private def quotient_at (d : EarlierLocalTheorems (family P))
    (u v : Vertex (family P)) (ht : u.type = v.type) :
    (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃*
      (d.localGroup u ⧸ pCore 2 (d.localGroup u)) := by
  let g := Classical.choose ((same_orbit_iff (family P) u v).mpr ht)
  have hg : g • u = v := Classical.choose_spec ((same_orbit_iff (family P) u v).mpr ht)
  have he : (d.localGroup u).map (MulAut.conj g).toMonoidHom = d.localGroup v := by
    rw [←d.conjugate,hg]
  let e := ((d.localGroup u).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr he)
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

/-- The opposite core acts transitively on the forward neighbors of every
edge, from the original commuting critical pair and either unitary marking. -/
theorem source_unitary_core_forward_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
    {v w x y : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hx : (graph (family P)).Adj v x) (hy : (graph (family P)).Adj v y)
    (hxw : x ≠ w) (hyw : y ≠ w) :
    ∃ g ∈ Q (family P) w, g • x = y := by
  have hab := source_critical_one_adjacent hc hb
  have Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)) := by
    rcases mark with hi | hi
    · exact .projective_unitary m hm hi
    · exact .special_unitary m hm hi
  obtain ⟨hprod,_⟩ := source_unitary_beta_core_product_and_alpha h hB d hc hb hcomm hbc hac Ma hm mark
  have haction : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ∧
      (∀ x y : Vertex (family P), (graph (family P)).Adj v x →
        (graph (family P)).Adj v y → x ≠ w → y ≠ w →
        ∃ g ∈ d.localGroup v ⊓ stabilizer (family P) w, g • x = y) := by
    by_cases hav : a.type = v.type
    · let e := quotient_at d a v hav
      refine ⟨Ma.of_equiv e,?_⟩
      rcases source_edge_transitive_or_dihedral h hB d hvw (Ma.of_equiv e) with ht | hi
      · exact ht
      · exact (source_alpha_dihedral_exclusion h hB d hc hb hcomm hbc hac Mb (e.symm.trans hi.some)).elim
    · have hbv : b.type = v.type := by
        have hh := hab.1
        cases ha : a.type <;> cases hb : b.type <;> cases hv : v.type <;> simp_all
      let e := quotient_at d b v hbv
      have mark' : ClassicalGroup.IsPSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^m) ∨
          IsSU (d.localGroup v ⧸ pCore 2 (d.localGroup v)) 3 (2^m) := by
        rcases mark with hi | ⟨K,_,_,J,hcard,hconj,⟨ei⟩⟩
        · exact Or.inl (hi.of_mulEquiv e)
        · exact Or.inr ⟨K,inferInstance,inferInstance,J,hcard,hconj,⟨e.trans ei⟩⟩
      exact ⟨Mb.of_equiv e,fun _ _ hx hy hxn hyn =>
        source_unitary_edge_transitive h hB d hvw hm mark' hx hy hxn hyn⟩
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  exact source_full_product_core_transitive h d hvw haction.1 R hR
    (source_full_core_product_all_edges (family P) hab hprod.symm hvw)
    haction.2 hx hy hxw hyw

private theorem core_fix_adjacent (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    {g : G} (hg : g ∈ Q (family P) v) : g • w = w :=
  ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge (family P) hvw).trans inf_le_right)) hg

private theorem short_right_regular_of_core_forward
    (h : LocallyRankOneTriple P B)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
        (graph (family P)).Adj v y → x ≠ w → y ≠ w →
        ∃ g ∈ Q (family P) w, g • x = y)
    {u : Vertex (family P)} (p : BasedWalk (graph (family P)) 2 u) :
    RightRegular (A := G) p := by
  intro x y hx hy
  let v : Vertex (family P) := p.1
  let w : Vertex (family P) := p.2.1
  have huv : (graph (family P)).Adj u v := p.1.property
  have hvw : (graph (family P)).Adj v w := p.2.1.property
  change (graph (family P)).Adj w x ∧ x ≠ v at hx
  change (graph (family P)).Adj w y ∧ y ≠ v at hy
  obtain ⟨g,hg,he⟩ := ht w v hvw.symm x y hx.1 hy.1 hx.2 hy.2
  refine ⟨g,?_,he⟩
  change ∀ z ∈ [u,v,w], g • z = z
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨core_fix_adjacent h huv.symm hg,Q_le_stabilizer _ v hg,
    core_fix_adjacent h hvw hg⟩

private theorem one_walk_transitive (u : Vertex (family P)) :
    RootPathTransitive (graph (family P)) G u 1 := by
  intro p q _ _
  obtain ⟨g,hg,he⟩ := locally_transitive (family P) p.1.property q.1.property
  refine ⟨g,hg,?_⟩
  change [u,(p.1 : Vertex (family P))].map (g • ·) = [u,(q.1 : Vertex (family P))]
  simp only [List.map_cons,List.map_nil,show g • u = u from hg,he]

private theorem three_walk_of_core_forward
    (h : LocallyRankOneTriple P B)
    (ht : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ∀ x y : Vertex (family P), (graph (family P)).Adj v x →
        (graph (family P)).Adj v y → x ≠ w → y ≠ w →
        ∃ g ∈ Q (family P) w, g • x = y)
    (u : Vertex (family P)) : RootPathTransitive (graph (family P)) G u 3 := by
  have hact : GraphAction (graph (family P)) G :=
    ⟨fun g _ _ he => (Subgroup.CosetGeometry.translationGraphIso (family P) g).toHom.map_adj he⟩
  have htwo : RootPathTransitive (graph (family P)) G u 2 := by
    apply (one_walk_transitive u).succ_of_rightRegular hact
    intro p _ x y hx hy
    let v : Vertex (family P) := p.1
    have huv : (graph (family P)).Adj u v := p.1.property
    change (graph (family P)).Adj v x ∧ x ≠ u at hx
    change (graph (family P)).Adj v y ∧ y ≠ u at hy
    obtain ⟨g,hg,he⟩ := ht v u huv.symm x y hx.1 hy.1 hx.2 hy.2
    refine ⟨g,?_,he⟩
    change ∀ z ∈ [u,v], g • z = z
    simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨Q_le_stabilizer _ u hg,core_fix_adjacent h huv hg⟩
  exact htwo.succ_of_rightRegular hact (fun p _ => short_right_regular_of_core_forward h ht p)

/-- The actual vertex stabilizer is transitive on nonbacktracking three-walks
in both vertex orbits, with no path-transitivity premise. -/
theorem source_unitary_three_walk_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m) ∨
      IsSU (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 3 (2^m))
    (u : Vertex (family P)) : RootPathTransitive (graph (family P)) G u 3 :=
  three_walk_of_core_forward h (fun _ _ hvw _ _ hx hy hxw hyw =>
    source_unitary_core_forward_transitive h hB d hc hb hcomm hbc hac Ma hm mark hvw hx hy hxw hyw) u

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
