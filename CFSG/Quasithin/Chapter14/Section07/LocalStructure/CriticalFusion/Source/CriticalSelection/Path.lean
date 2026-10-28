module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.F8SourceApplication

/-!
# First critical path from the original 14.7 data

The original natural module, abelian H-span and unique H choice supply every
F.8 hypothesis through the proved Section 12.8 source application. In
particular the actual LT/H coset action is faithful. F.8 constructs its odd
critical track and a geodesic with the standard first edge. Local transitivity
in the original H then supplies the independent adjustment at vertex two.

The final theorem constructs the existing CriticalPath record on the literal
geometryFamily. It retains only the two genuine universal earlier source
implications already used by the original higher-rank setup, with no selected
path, critical vertex, actor, rank or faithfulness premise.

Source: Aschbacher–Smith 14.5.14–18 and Notation 14.7.1, printed pp.1017–1018
and1042–1043; the actual F.8.4–5 construction, printed pp.316–317.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection
open Chapter12.Section08
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Original F8 hypotheses on the actual LT/H pair. -/
theorem f8_hypothesis (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness:Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    ChapterF.Section08.Setup.Hypothesis (F.f8SourceSetup L F.H) := by
  let := d.natural.chosen.elementary
  have hJ : F.H∈F.Hz L (normalizer (L:Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton _
  have hzV : d.z∈V := F.le_seed 1 (d.point ▸ mem_zpowers d.z)
  apply F.f8Source_hypothesis d.natural.source.simpleQTKE L (normalizer (L:Set G))
    (by decide) d.natural.chosen.le_sylow d.natural.chosen.normalizes
    (d.natural.sylow_normalizes structural) d.natural.residual
    (fun _=>⟨d.natural.naturalMarking⟩) rfl
    (d.natural.maximal_unique structural uniqueness).2
    (d.natural.seed_centralizer_le structural uniqueness) d.natural.centralizer_L
    d.natural.source.maximal_faithful.2.1.2.2 (d.natural.seed_reduced structural)
    (d.natural.centralizer_LT structural) d.z d.point d.z_ne_one _ d.abelian F.H hJ
  intro x hx hx1
  obtain ⟨l,hl,he⟩ := d.natural.vector_transitive hzV hx d.z_ne_one hx1
  exact ⟨l,d.natural.chosen.normalizes hl,he⟩

open Subgroup.CosetGeometry.RankTwo

set_option backward.isDefEq.respectTransparency false in
/-- First critical path and the actual H adjustment. -/
theorem exists_criticalPath (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness:Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    Nonempty (CriticalPath (L:=L) F) := by
  classical
  let D:=F.f8SourceSetup L F.H
  let h:ChapterF.Section08.Setup.Hypothesis D:=f8_hypothesis d structural uniqueness
  obtain ⟨C⟩:=h.exists_criticalPath
  let Ω:=geometryFamily (L:=L) F
  let a:GeometryGroup T L F:=C.g⁻¹
  have he:C.endpoint=a⁻¹ • base Ω true := by
    change C.endpoint=(C.g⁻¹)⁻¹ • base (ChapterF.Section08.Setup.Hypothesis.family (D:=D)) true
    rw [inv_inv]
    exact C.endpoint_eq.symm
  let p:(graph Ω).Walk (base Ω false) (a⁻¹ • base Ω true):=C.path.copy rfl he
  have hlen:p.length=h.b := by
    dsimp only [p]
    rw [SimpleGraph.Walk.length_copy]
    exact C.shortest.trans C.distance
  have hfirst:p.getVert 1=base Ω true := by
    dsimp only [p]
    rw [SimpleGraph.Walk.getVert_copy]
    exact C.first
  have hadj₂:(graph Ω).Adj (base Ω true) (p.getVert 2) := by
    have hh:=p.adj_getVert_succ (i:=1) (by rw [hlen]; have := h.lemma_F_8_5.1; omega)
    rwa [hfirst] at hh
  obtain ⟨t,ht,hte⟩:=locally_transitive Ω
    (show (graph Ω).Adj (base Ω true) (base Ω false) from
      ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩) hadj₂
  have htH:(t:G)∈F.H := by
    have ht':t∈Ω true := by simpa only [stabilizer,CosetGeometry.stabilizer_base] using ht
    exact ht'
  refine ⟨{
    b:=h.b
    radius:=?_
    gammaConjugator:=a
    path:=p
    geodesic:=?_
    length:=hlen
    first:=hfirst
    critical:=?_
    rechoice:=⟨t,htH⟩
    alignment:=?_ }⟩
  · intro n
    have hh:=(h.f7Setup.track_spec h.f7V_ne_bot).2.2.2 n
    rw [h.f7Seed_eq] at hh
    exact hh
  · dsimp only [p]
    rw [SimpleGraph.Walk.length_copy,←he]
    exact C.shortest
  · have hh:=C.critical
    rw [h.f7Seed_eq] at hh
    change ¬ V.subgroupOf (GeometryGroup T L F)≤ballKernel Ω C.endpoint 1 at hh
    rw [he] at hh
    exact hh
  · change t⁻¹ • p.getVert 2=base Ω false
    rw [←hte,inv_smul_smul]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection
