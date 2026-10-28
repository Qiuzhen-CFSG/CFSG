module

public import Theory.GroupAction.RankTwoCosetGeometry.Distance
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Central labels and three-edge coset paths

If the first subgroup is transitive on the nonidentity labels and the second
contains the centralizer of the base label, moving a terminal label into the
seed puts its transporter in the double coset H B H. The resulting explicit
three-edge path bounds the distance. This is the group-geometric argument
in Aschbacher--Smith, F.9.14(3), printed p.323. No finiteness, critical-pair
or classification premise is required.
-/

public section
open Subgroup
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

theorem distance_le_three_of_double_coset (h l k : G)
    (hh : h ∈ F true) (hl : l ∈ F false) (hk : k ∈ F true) :
    (graph F).dist (base F false) ((h*l*k) • base F true) ≤ 3 := by
  have hfix : h • base F true = base F true := by
    change h ∈ MulAction.stabilizer G (base F true)
    rwa [CosetGeometry.stabilizer_base]
  have lfix : l • base F false = base F false := by
    change l ∈ MulAction.stabilizer G (base F false)
    rwa [CosetGeometry.stabilizer_base]
  have kfix : k • base F true = base F true := by
    change k ∈ MulAction.stabilizer G (base F true)
    rwa [CosetGeometry.stabilizer_base]
  have he : (graph F).Adj (base F false) (base F true) :=
    ⟨Bool.false_ne_true,incident_base F false true⟩
  have he₂ : (graph F).Adj (base F true) (h • base F false) := by
    have hh := (translationGraphIso F h).map_rel_iff.mpr he.symm
    change (graph F).Adj (h • base F true) (h • base F false) at hh
    simpa only [hfix] using hh
  have he₃ : (graph F).Adj (h • base F false) ((h*l*k) • base F true) := by
    have hh := (translationGraphIso F (h*l)).map_rel_iff.mpr he
    change (graph F).Adj ((h*l) • base F false) ((h*l) • base F true) at hh
    simpa only [mul_smul,lfix,kfix] using hh
  exact (SimpleGraph.dist_le (SimpleGraph.Walk.cons he
    (SimpleGraph.Walk.cons he₂ (SimpleGraph.Walk.cons he₃ SimpleGraph.Walk.nil))))

theorem central_label_factorization (V : Subgroup G) (z g h : G)
    (hz : z ≠ 1) (hcenter : centralizer ({z}:Set G) ≤ F true)
    (htrans : ∀ v∈V, v≠1 → ∃ l∈F false, l*z*l⁻¹=v)
    (hm : h⁻¹*(g*z*g⁻¹)*h ∈ V) :
    ∃ l∈F false, ∃ k∈F true, g=h*l*k := by
  have hne : h⁻¹*(g*z*g⁻¹)*h ≠ 1 := by
    intro he
    apply hz
    have he' := congrArg (fun x => g⁻¹ * (h*x*h⁻¹) * g) he
    convert he' using 1 <;> group
  obtain ⟨l,hl,he⟩ := htrans _ hm hne
  refine ⟨l,hl,(h*l)⁻¹*g,hcenter ?_,by group⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh : ((h*l)⁻¹*g)*z*(((h*l)⁻¹*g)⁻¹)=z := by
    calc
      _ = l⁻¹*(h⁻¹*(g*z*g⁻¹)*h)*l := by group
      _ = z := by rw [← he]; group
  exact mul_inv_eq_iff_eq_mul.mp hh

theorem central_label_distance_le_three (V : Subgroup G) (z g h : G)
    (hz : z ≠ 1) (hcenter : centralizer ({z}:Set G) ≤ F true)
    (htrans : ∀ v∈V, v≠1 → ∃ l∈F false, l*z*l⁻¹=v)
    (hh : h∈F true) (hm : h⁻¹*(g*z*g⁻¹)*h ∈ V) :
    (graph F).dist (base F false) (g • base F true) ≤ 3 := by
  obtain ⟨l,hl,k,hk,rfl⟩ := central_label_factorization F V z g h hz hcenter htrans hm
  exact distance_le_three_of_double_coset F h l k hh hl hk
end Subgroup.CosetGeometry.RankTwo
