module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Geometry
public import CFSG.Quasithin.ChapterF.Section09.F7Specialization

/-!
# Construction of the original critical pair in Section 13.8

The common normal kernel vanishes by the actual F.7.3 local-core criterion.
A nontrivial seed therefore escapes some first kernel. Choose the least
such distance, take a shortest walk, and use the first vertex stabilizer
to move its initial edge onto the standard edge. The seed is normalized
by that same stabilizer, so criticality is preserved. Oddness from the
earlier F.9.11 theorem supplies the correctly oriented terminal edge and
its actual common transporter.

The last two theorems apply this construction to the literal F.9.1 setup.
Only the earlier F.9.11 parity/bound remains explicit; no endpoint, path,
conjugator or Section 13.8 geometry conclusion is assumed.
Source: Aschbacher--Smith, F.9.10--12 and the setup of 13.8.4,
printed pp.321--322 and 946--947, combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] (L T H V : Subgroup G)

private theorem family_eq : cosetFamily L T H = ChapterF.Section07.Geometry.family (L ⊔ T) H := by
  funext i
  cases i <;> rfl

private theorem generated : cosetFamily L T H false ⊔ cosetFamily L T H true = ⊤ := by
  rw [family_eq]
  exact ChapterF.Section07.Geometry.family_generates (L ⊔ T) H

private theorem graph_eq : graph L T H = Subgroup.CosetGeometry.RankTwo.graph (cosetFamily L T H) := rfl

private theorem connected : (graph L T H).Connected := by
  rw [graph_eq]
  exact Subgroup.CosetGeometry.RankTwo.connected _ (generated L T H)

private theorem vertex_mem (v : Vertex L T H) (a : G0 L T H) :
    (a:G) ∈ vertexGroup L T H v ↔ a • v = v := by
  constructor
  · rintro ⟨b,hb,hba⟩
    have he : b=a := Subtype.ext hba
    subst b
    exact hb
  · intro ha
    exact ⟨a,ha,rfl⟩

private theorem exists_escape [Finite G]
    (hV : V ≠ ⊥) (hVL : V ≤ L ⊔ T)
    (hF : generalizedFitting (L ⊔ T : Subgroup G) = pCore 2 (L ⊔ T : Subgroup G))
    (hcore : pCore 2 (G0 L T H) = ⊥) :
    ∃ v : Vertex L T H, ¬ V ≤ firstKernel L T H v := by
  by_contra! hh
  apply hV
  have hk : ChapterF.Section07.Geometry.ambientKernel (L ⊔ T) H = ⊥ :=
    ChapterF.LocalCores.lemma_F_7_3_eight_algebra _ _ _
      ((ChapterF.Section07.Geometry.ambientKernel_le _ _).trans inf_le_left)
      ((ChapterF.Section07.Geometry.ambientKernel_le _ _).trans inf_le_right)
      (ChapterF.Section07.Geometry.ambientKernel_normal_left _ _)
      (ChapterF.Section07.Geometry.ambientKernel_normal_right _ _) hF hcore
  apply bot_unique
  intro x hx
  have hx0 : x ∈ G0 L T H := mem_sup_left (hVL hx)
  have hxk : x ∈ ChapterF.Section07.Geometry.ambientKernel (L ⊔ T) H := by
    refine ⟨⟨x,hx0⟩,?_,rfl⟩
    change MulAction.toPermHom (G0 L T H)
      (ChapterF.Section07.Geometry.Vertex (L ⊔ T) H) ⟨x,hx0⟩ = 1
    apply Equiv.ext
    intro v
    change (⟨x,hx0⟩:G0 L T H) • v = v
    rcases v with ⟨i,y⟩
    cases i
    · have he := (vertex_mem L T H ⟨false,y⟩ ⟨x,hx0⟩).mp ((hh ⟨false,y⟩ hx).1)
      have hc : (⟨x,hx0⟩:G0 L T H) • y = y := by injection he
      exact congrArg (CosetGeometry.Vertex.mk false) hc
    · have he := (vertex_mem L T H ⟨true,y⟩ ⟨x,hx0⟩).mp ((hh ⟨true,y⟩ hx).1)
      have hc : (⟨x,hx0⟩:G0 L T H) • y = y := by injection he
      exact congrArg (CosetGeometry.Vertex.mk true) hc
  rwa [hk] at hxk

private theorem shortest_escape [Finite G]
    (hV : V ≠ ⊥) (hVL : V ≤ L ⊔ T)
    (hF : generalizedFitting (L ⊔ T : Subgroup G) = pCore 2 (L ⊔ T : Subgroup G))
    (hcore : pCore 2 (G0 L T H) = ⊥) :
    ∃ (v : Vertex L T H) (p : (graph L T H).Walk (base L T H false) v),
      p.length = criticalDistance L T H V ∧
      (graph L T H).dist (base L T H false) v = p.length ∧
      ¬ V ≤ firstKernel L T H v := by
  have hn : {n | ∃ v : Vertex L T H,
      (graph L T H).Reachable (base L T H false) v ∧
      (graph L T H).dist (base L T H false) v=n ∧ ¬V≤firstKernel L T H v}.Nonempty := by
    obtain ⟨v,hv⟩:=exists_escape L T H V hV hVL hF hcore
    exact ⟨_,v,(connected L T H) _ _,rfl,hv⟩
  obtain ⟨v,hr,hd,hv⟩ := Nat.sInf_mem hn
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  exact ⟨v,p,hp.trans hd,hp.symm,hv⟩

private theorem path_even_iff {x y : Vertex L T H} (p : (graph L T H).Walk x y) :
    Even p.length ↔ x.type=y.type := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    rw [SimpleGraph.Walk.length_cons,Nat.even_add_one,ih]
    have hn:=h.1
    cases hx:x.type <;> cases hy:y.type <;> cases hz:z.type <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- The original critical pair is constructed from local faithfulness and
F.9.11 parity, with no chosen endpoint or path assumption. -/
theorem exists_criticalPair [Finite G]
    (hV : V ≠ ⊥) (hVL : V ≤ L ⊔ T)
    (hnorm : L ⊔ T ≤ normalizer (V:Set G))
    (hF : generalizedFitting (L ⊔ T : Subgroup G) = pCore 2 (L ⊔ T : Subgroup G))
    (hcore : pCore 2 (G0 L T H) = ⊥)
    (hodd : Odd (criticalDistance L T H V)) : Nonempty (CriticalPair L T H V) := by
  obtain ⟨v,p,hp,hd,hcrit⟩ := shortest_escape L T H V hV hVL hF hcore
  have hpos : 0 < p.length := by
    obtain ⟨k,hk⟩:=hodd
    omega
  have hfirst : (graph L T H).Adj (base L T H false) (p.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ (i:=0) hpos
  have hstandard : (graph L T H).Adj (base L T H false) (base L T H true) :=
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨a,ha,hafirst⟩ := Subgroup.CosetGeometry.RankTwo.locally_transitive
    (cosetFamily L T H) hfirst hstandard
  have ha0 : a • base L T H false = base L T H false := ha
  have haL : (a:G) ∈ L ⊔ T := by
    change a ∈ MulAction.stabilizer (G0 L T H) (CosetGeometry.base (cosetFamily L T H) false) at ha
    rw [Subgroup.CosetGeometry.stabilizer_base] at ha
    exact ha
  let w : (graph L T H).Walk (base L T H false) (a • v) := (p.map (translate a)).copy ha0 rfl
  have hwlen : w.length=p.length := by
    dsimp only [w]
    rw [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  have hwget (n:ℕ) : w.getVert n=a•p.getVert n := by
    dsimp only [w]
    rw [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]
    rfl
  have hvcrit : ¬ V ≤ firstKernel L T H (a•v) := by
    intro hc
    have hVmap : V.map (MulAut.conj (a:G)⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (hnorm (inv_mem haL))
    have hh := map_mono (f:=(MulAut.conj (a:G)⁻¹).toMonoidHom) hc
    rw [hVmap] at hh
    change V ≤ (firstKernel L T H (a • v)).map (MulAut.conj ((a⁻¹ : G0 L T H) : G)).toMonoidHom at hh
    rw [← firstKernel_smul (a⁻¹),inv_smul_smul] at hh
    exact hcrit hh
  have hwDist : (graph L T H).dist (base L T H false) (a•v)=w.length := by
    apply le_antisymm (SimpleGraph.dist_le w)
    rw [hwlen,hp]
    exact Nat.sInf_le ⟨_,⟨w⟩,rfl,hvcrit⟩
  have hvtype : (a•v).type=true := by
    have hn : ¬ Even w.length := by
      rw [hwlen,hp]
      exact Nat.not_even_iff_odd.mpr hodd
    have htype := (path_even_iff L T H w).not.mp hn
    change ¬false=(a•v).type at htype
    cases he:(a•v).type <;> simp_all
  have he : (graph L T H).Adj (w.getVert (w.length-1)) (a•v) := by
    have hh:=w.adj_getVert_succ (i:=w.length-1) (by omega)
    have hn:w.length-1+1=w.length := by omega
    simpa only [hn,SimpleGraph.Walk.getVert_length] using hh
  have hprev : (w.getVert (w.length-1)).type=false := by
    have hh:=he.1
    rw [hvtype] at hh
    cases ht:(w.getVert (w.length-1)).type <;> simp_all
  obtain ⟨b,hb0,hb1⟩ := Subgroup.CosetGeometry.RankTwo.incident_common_translate
    (cosetFamily L T H) he.2
  rw [hprev] at hb0
  rw [hvtype] at hb1
  exact ⟨{ gamma := a • v
           path := w
           length_eq := hwlen.trans hp
           distance_eq := hwDist
           critical := hvcrit
           first := (hwget 1).trans hafirst
           gb := b
           gb_zero := hb0
           gb_one := hb1 }⟩


/-- Literal F.9.1 application to the original L,T,H,V. Its only further
input is the preceding odd-parity conclusion of F.9.11. -/
theorem f9_criticalPair [Finite G] (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hodd : Odd (criticalDistance D.L (D.T : Subgroup G) D.H D.V)) :
    Nonempty (CriticalPair D.L (D.T : Subgroup G) D.H D.V) := by
  have hV : D.V ≠ ⊥ := by
    intro he
    have hZ : D.V₁ = ⊥ := bot_unique (he ▸ h.point_lt.le.trans h.plus_le)
    have hc := h.point_card
    rw [hZ] at hc
    simp at hc
  exact exists_criticalPair D.L (D.T : Subgroup G) D.H D.V hV h.V_le_LT
    ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal)
    h.characteristic_LT h.generated_core hodd

/-- The original setup yields an actual source-normalized pair together
with both bounds of 13.8.4(1), when supplied the earlier F.9.11 conclusion. -/
theorem f9_criticalPair_bounds [Finite G] (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hF911 : 3 ≤ criticalDistance D.L (D.T : Subgroup G) D.H D.V ∧
      Odd (criticalDistance D.L (D.T : Subgroup G) D.H D.V)) :
    ∃ c : CriticalPair D.L (D.T : Subgroup G) D.H D.V,
      3 ≤ c.path.length ∧ Odd c.path.length := by
  obtain ⟨c⟩ := f9_criticalPair D h hF911.2
  exact ⟨c,c.length_eq ▸ hF911.1,c.length_eq ▸ hF911.2⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
