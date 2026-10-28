module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalPair
public import CFSG.Quasithin.ChapterF.Section09.TrackSetup

/-!
# Equality of the F.7 track and the Section 13.8 critical distance

The Section 13.8 first kernel is the ambient image of the pointwise
stabilizer of the radius-one ball. Comparing their literal memberships
identifies the two least-distance definitions, using the actual F.7
critical witness and its minimality. No replacement graph or reindexed
seed is introduced. Source: F.7.9 and F.9.10, used in 13.8.4.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (L T H : Subgroup G)

private theorem vertex_mem (v : CriticalGeometry.Vertex L T H) (x : G0 L T H) :
    (x:G)∈vertexGroup L T H v ↔ x•v=v := by
  constructor
  · rintro ⟨a,ha,he⟩
    have hh:a=x:=Subtype.ext he
    exact hh ▸ ha
  · intro hx
    exact ⟨x,hx,rfl⟩

private theorem firstKernel_mem (v : CriticalGeometry.Vertex L T H) (x : G0 L T H) :
    (x:G)∈firstKernel L T H v ↔ x∈ballKernel (cosetFamily L T H) v 1 := by
  constructor
  · rintro ⟨hv,hw⟩ w hball
    rcases (mem_ball_one (cosetFamily L T H) v w).mp hball with hw'|rfl
    · exact (vertex_mem L T H w x).mp ((mem_iInf.mp (mem_iInf.mp hw w) hw'))
    · exact (vertex_mem L T H v x).mp hv
  · intro hx
    refine ⟨(vertex_mem L T H v x).mpr (hx v (center_mem_ball _ _ _)),?_⟩
    exact mem_iInf.mpr fun w=>mem_iInf.mpr fun hw=>
      (vertex_mem L T H w x).mpr (hx w ((mem_ball_one _ _ _).mpr (Or.inl hw)))

theorem le_firstKernel_iff (V : Subgroup G) (hV:V≤G0 L T H) (v : CriticalGeometry.Vertex L T H) :
    V≤firstKernel L T H v ↔ V.subgroupOf (G0 L T H)≤ballKernel (cosetFamily L T H) v 1 := by
  constructor
  · intro hv x hx
    exact (firstKernel_mem L T H v x).mp (hv hx)
  · intro hv x hx
    exact (firstKernel_mem L T H v ⟨x,hV hx⟩).mpr (hv hx)

theorem f9_criticalDistance_eq [Finite G] (D:ChapterF.Section09.Setup G) (h:D.Hypothesis) :
    criticalDistance D.L (D.T:Subgroup G) D.H D.V=h.b := by
  have hf : cosetFamily D.L (D.T:Subgroup G) D.H=ChapterF.Section07.Geometry.family D.LT D.H := by
    funext i
    cases i <;> rfl
  have hw := (h.f7Setup.critical_witness h.f7V_ne_bot).1
  have hmin := (h.f7Setup.critical_witness h.f7V_ne_bot).2
  rw [h.f7Seed_eq] at hw hmin
  change ∃ v : CosetGeometry.Vertex (ChapterF.Section07.Geometry.family D.LT D.H),
    (Subgroup.CosetGeometry.RankTwo.graph _).dist (CosetGeometry.base _ false) v=h.b ∧
      ¬ D.V.subgroupOf (D.LT⊔D.H)≤ballKernel _ v 1 at hw
  change ∀v : CosetGeometry.Vertex (ChapterF.Section07.Geometry.family D.LT D.H),
    ¬ D.V.subgroupOf (D.LT⊔D.H)≤ballKernel _ v 1 →
      h.b≤(Subgroup.CosetGeometry.RankTwo.graph _).dist (CosetGeometry.base _ false) v at hmin
  rw [←hf] at hw hmin
  obtain ⟨v,hd,hv⟩:=hw
  have hconn := Subgroup.CosetGeometry.RankTwo.connected _
    (show cosetFamily D.L (D.T:Subgroup G) D.H false ⊔ cosetFamily D.L (D.T:Subgroup G) D.H true=⊤ from by
      rw [hf]; exact ChapterF.Section07.Geometry.family_generates D.LT D.H)
  have hV : D.V≤G0 D.L (D.T:Subgroup G) D.H:=h.V_le_LT.trans le_sup_left
  have hcrit : ¬D.V≤firstKernel D.L (D.T:Subgroup G) D.H v := by
    exact fun hh => hv ((le_firstKernel_iff _ _ _ _ hV v).mp hh)
  have hm : h.b∈{n | ∃v:CriticalGeometry.Vertex D.L (D.T:Subgroup G) D.H,
      (CriticalGeometry.graph _ _ _).Reachable (CriticalGeometry.base _ _ _ false) v ∧
      (CriticalGeometry.graph _ _ _).dist (CriticalGeometry.base _ _ _ false) v=n ∧
      ¬D.V≤firstKernel D.L (D.T:Subgroup G) D.H v} :=
    ⟨v,hconn _ _,hd,hcrit⟩
  apply le_antisymm (Nat.sInf_le hm)
  obtain ⟨w,hr,he,hc⟩:=Nat.sInf_mem ⟨_,hm⟩
  have hw' : ¬D.V.subgroupOf (G0 D.L (D.T:Subgroup G) D.H)≤ballKernel _ w 1 := by
    exact fun hh => hc ((le_firstKernel_iff _ _ _ _ hV w).mpr hh)
  exact he ▸ hmin w hw'
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
