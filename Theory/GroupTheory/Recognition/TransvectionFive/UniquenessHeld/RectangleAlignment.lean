module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
public import Mathlib.GroupTheory.Sylow

/-! Align the original elementary sixty-fours with the two rectangles of
the whole point-centralizer marking. The conjugator belongs to that actual
centralizer, and the same conjugator identifies both subgroups. -/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

theorem exists_simultaneous_rectangle_alignment
    (T : Sylow 2 G) (hTC : (T : Subgroup G)≤centralizer ({z} : Set G))
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAT : A≤(T : Subgroup G)) (hBT : B≤(T : Subgroup G))
    (hA : Nat.card A=64) (hB : Nat.card B=64) (hne : A≠B) :
    ∃ c : centralizer ({z} : Set G),
      (A.map (MulAut.conj (c:G)).toMonoidHom=F.plane ∧
        B.map (MulAut.conj (c:G)).toMonoidHom=F.threeSpace) ∨
      (A.map (MulAut.conj (c:G)).toMonoidHom=F.threeSpace ∧
        B.map (MulAut.conj (c:G)).toMonoidHom=F.plane) := by
  let C := centralizer ({z} : Set G)
  let S := sourceSylow F
  have hSC : (S : Subgroup G)≤C := sourceSylow_le_point_centralizer F
  obtain ⟨c,hc⟩ := exists_smul_eq C (T.subtype hTC) (S.subtype hSC)
  have hc' : ((T : Subgroup G).subgroupOf C).map (MulAut.conj c).toMonoidHom =
      (S : Subgroup G).subgroupOf C := by
    have hh := congrArg (fun R : Sylow 2 C => (R : Subgroup C)) hc
    simp only [Sylow.coe_subgroup_smul,Sylow.coe_subtype,Subgroup.pointwise_smul_def] at hh
    change ((T : Subgroup G).subgroupOf C).map (MulAut.conj c).toMonoidHom =
      (S : Subgroup G).subgroupOf C at hh
    exact hh
  have hmap : (T : Subgroup G).map (MulAut.conj (c:G)).toMonoidHom = S := by
    have hh := congrArg (Subgroup.map C.subtype) hc'
    rw [map_map,map_subgroupOf_eq_of_le hSC] at hh
    have he : C.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c:G)).toMonoidHom.comp C.subtype := by ext x; rfl
    rw [he,← map_map,map_subgroupOf_eq_of_le hTC] at hh
    exact hh
  let f := (MulAut.conj (c:G)).toMonoidHom
  let A' := A.map f
  let B' := B.map f
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 B' := IsElementaryAbelian.map f
  have hA' : Nat.card A'=64 := (card_map_of_injective (MulAut.conj (c:G)).injective).trans hA
  have hB' : Nat.card B'=64 := (card_map_of_injective (MulAut.conj (c:G)).injective).trans hB
  have hne' : A'≠B' := fun he => hne (map_injective (MulAut.conj (c:G)).injective he)
  have hAS : A'≤(sourceSylow F : Subgroup G) := (map_mono hAT).trans_eq hmap
  have hBS : B'≤(sourceSylow F : Subgroup G) := (map_mono hBT).trans_eq hmap
  have ha := rectangleCatalogue F A' hAS inferInstance hA'
  have hb := rectangleCatalogue F B' hBS inferInstance hB'
  refine ⟨c,?_⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hne' (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · exact (hne' (ha.trans hb.symm)).elim

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
