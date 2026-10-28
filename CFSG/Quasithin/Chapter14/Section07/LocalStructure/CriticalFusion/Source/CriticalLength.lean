module

public import CFSG.Quasithin.ChapterF.Section09.CentralLabelDistance
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
public import CFSG.Quasithin.Chapter12.Section08.Setup.Escape
/-!
# The genuine critical-length implication of 14.7.3(4)

The original natural L₃(2) action is transitive on nonidentity vectors.
If the reselected terminal central line lies in V, the F.9.14(3)
central-label argument gives a three-edge path to the original terminal
vertex. The chosen path is geodesic. Its actual type and second-vertex
alignment exclude lengths zero, one and two, so b = 3.

All maps, the H rechoice, and the right-conjugation convention are those
of the original CriticalPath; no earlier-length callback is used.
Source: Aschbacher--Smith, F.9.14(3) and 14.7.3(4), pp.323,1043.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
/-- The actual terminal type and the rechoice at vertex two force b ≥ 3. -/
theorem CriticalPath.three_le (c : CriticalPath (L:=L) F) : 3 ≤ c.b := by
  by_contra! hb
  have hh := c.alignment
  rw [c.path.getVert_of_length_le (by rw [c.length]; omega)] at hh
  have ht := congrArg (fun v : Subgroup.CosetGeometry.RankTwo.Vertex
    (geometryFamily (L:=L) F) => v.type) hh
  exact Bool.noConfusion ht

/-- The critical-length implication of 14.7.3(4), proved from F.9.14(3). -/
theorem Data.critical_length_three (d : Data T L V F W) (c : CriticalPath (L:=L) F)
    (hc : c.Zα ≤ V) : c.b=3 := by
  have hzV : d.z ∈ V := F.le_seed 1 (by rw [d.point]; exact mem_zpowers d.z)
  have hm : (c.rechoice:G)⁻¹*((c.gammaConjugator:G)⁻¹*d.z*(c.gammaConjugator:G))*(c.rechoice:G) ∈ V := by
    apply hc
    change _ ∈ conjugate (F.Vi 1) c.conjugator
    unfold conjugate
    refine ⟨d.z,?_,?_⟩
    · rw [d.point]
      exact mem_zpowers d.z
    · simp [CriticalPath.conjugator,mul_assoc]
  have hbound := ChapterF.Section09.central_label_distance
    (L ⊔ (T:Subgroup G)) F.H V d.z c.gammaConjugator⁻¹
    (inclusion le_sup_right c.rechoice) d.z_ne_one
    (by rw [d.centralizer_eq])
    (fun v hv hv1 => by
      obtain ⟨l,hl,he⟩ := d.natural.vector_transitive hzV hv d.z_ne_one hv1
      exact ⟨l,mem_sup_left hl,he⟩)
    c.rechoice.property (by simpa using hm)
  change (Subgroup.CosetGeometry.RankTwo.graph (geometryFamily (L:=L) F)).dist
    (Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L:=L) F) false)
    (c.gammaConjugator⁻¹ • Subgroup.CosetGeometry.RankTwo.base (geometryFamily (L:=L) F) true) ≤ 3 at hbound
  rw [← c.geodesic,c.length] at hbound
  exact le_antisymm hbound c.three_le
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
