module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Centralizers in groups with an abelian subgroup of index two

The centralizer of a nonabelian subgroup lies in the abelian subgroup of
index two. If a centralizing element lay outside it, the intersection of
the nonabelian subgroup with the abelian subgroup would be central; all
remaining elements lie in one coset and consequently commute as well.
Thus two commuting nonabelian groups cannot both embed in such a group.

This elementary obstruction applies to the dihedral and semidihedral
automizer Sylows in Aschbacher--Smith 2.5.21, printed p.566.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem central_of_commute_outside_abelian_index_two
    (A : Subgroup G) [IsMulCommutative A] (hi : A.index = 2)
    {a c : G} (ha : a ∈ A) (hc : c ∉ A) (hac : Commute a c) :
    a ∈ center G := by
  apply mem_center_iff.mpr
  intro y
  by_cases hy : y ∈ A
  · exact A.le_centralizer ha y hy
  · have hd : y * c⁻¹ ∈ A :=
      (A.mul_mem_iff_of_index_two hi).mpr (by simpa using iff_of_false hy hc)
    have hh : Commute a (y * c⁻¹) := A.le_centralizer hd a ha
    simpa using (hh.mul_right hac).symm.eq

/-- A nonabelian subgroup's centralizer lies in every abelian subgroup of index two. -/
theorem centralizer_le_of_abelian_index_two
    (A B : Subgroup G) [IsMulCommutative A] (hi : A.index = 2)
    (hn : ¬ IsMulCommutative B) : centralizer (B : Set G) ≤ A := by
  intro c hc
  by_contra hcA
  apply hn
  refine ⟨⟨fun u v => Subtype.ext ?_⟩⟩
  have hz (b : G) (hb : b ∈ B) (hba : b ∈ A) : b ∈ center G :=
    central_of_commute_outside_abelian_index_two A hi hba hcA (hc b hb)
  by_cases hu : (u : G) ∈ A
  · exact (mem_center_iff.mp (hz u u.property hu) v).symm
  by_cases hv : (v : G) ∈ A
  · exact mem_center_iff.mp (hz v v.property hv) u
  have huv : (u : G) * (v : G)⁻¹ ∈ A :=
    (A.mul_mem_iff_of_index_two hi).mpr (by simpa using iff_of_false hu hv)
  have hcz := hz _ (B.mul_mem u.property (B.inv_mem v.property)) huv
  have hcomm : Commute ((u : G) * (v : G)⁻¹) (v : G) :=
    (mem_center_iff.mp hcz v).symm
  simpa using (hcomm.mul_left (Commute.refl (v : G))).eq

/-- Commuting nonabelian groups cannot both embed in a group with abelian index two. -/
theorem not_nonabelian_commuting_images_of_abelian_index_two
    {U V : Type*} [Group U] [Group V]
    (A : Subgroup G) [IsMulCommutative A] (hi : A.index = 2)
    (f : U →* G) (hf : Function.Injective f) (g : V →* G) (hg : Function.Injective g)
    (hnU : ¬ IsMulCommutative U) (hnV : ¬ IsMulCommutative V)
    (hcomm : ∀ u v, Commute (f u) (g v)) : False := by
  have hn : ¬ IsMulCommutative g.range := by
    intro hh
    apply hnV
    refine ⟨⟨fun v w => hg ?_⟩⟩
    simpa only [map_mul, Subgroup.coe_mul] using congrArg Subtype.val
      (hh.is_comm.comm (⟨g v, ⟨v, rfl⟩⟩ : g.range) ⟨g w, ⟨w, rfl⟩⟩)
  have hle := centralizer_le_of_abelian_index_two A g.range hi hn
  have hfA (u : U) : f u ∈ A := hle (by
    rintro _ ⟨v, rfl⟩
    exact (hcomm u v).symm.eq)
  exact hnU ⟨⟨fun u v => hf (by simpa only [map_mul] using A.le_centralizer (hfA v) (f u) (hfA u))⟩⟩
end Subgroup
