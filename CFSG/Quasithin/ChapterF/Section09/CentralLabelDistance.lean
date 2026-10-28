module

public import Theory.GroupAction.RankTwoCosetGeometry.CentralLabelDistance
public import CFSG.Quasithin.ChapterF.Section07.Geometry

/-!
# F.9.14(3): the distance bound in the original generated subgroup

The central-label double-coset factorization is lifted into B ∨ H. Thus the
bound applies to the literal F.7 graph, retaining the ambient conjugation
convention and both original vertex subgroups. Transitivity and the point
centralizer are the actual hypotheses of F.9.14(3), not critical-length
conclusions. Source: Aschbacher--Smith, F.9.14(3), printed p.323.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Section09
variable {G : Type*} [Group G]

theorem central_label_distance (B H V : Subgroup G) (z : G)
    (g h : (B ⊔ H : Subgroup G)) (hz : z ≠ 1)
    (hcenter : centralizer ({z}:Set G) ≤ H)
    (htrans : ∀ v∈V, v≠1 → ∃ l∈B, l*z*l⁻¹=v)
    (hh : (h:G)∈H) (hm : (h:G)⁻¹*((g:G)*z*(g:G)⁻¹)*(h:G) ∈ V) :
    (Section07.Geometry.graph B H).dist (Section07.Geometry.base B H false)
      (g • Section07.Geometry.base B H true) ≤ 3 := by
  let F : Bool → Subgroup G := fun i => if i then H else B
  obtain ⟨l,hl,k,hk,he⟩ := Subgroup.CosetGeometry.RankTwo.central_label_factorization
    F V z (g:G) (h:G) hz hcenter htrans hm
  let l' : (B ⊔ H : Subgroup G) := ⟨l,mem_sup_left hl⟩
  let k' : (B ⊔ H : Subgroup G) := ⟨k,mem_sup_right hk⟩
  have he' : g=h*l'*k' := Subtype.ext he
  rw [he']
  exact Subgroup.CosetGeometry.RankTwo.distance_le_three_of_double_coset
    (Section07.Geometry.family B H) h l' k' hh hl hk
end CFSG.Quasithin.ChapterF.Section09
