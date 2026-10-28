module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue

/-! A whole transvection-centralizer marking determines the ambient Sylow
two-group. Every elementary subgroup of order sixty-four in any ambient
Sylow is normal in that same Sylow, by the literal matrix rectangle catalogue. -/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.TransvectionFive.UniquenessHeld
open UniquenessLinear UniquenessMathieu.SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

include F in
theorem sylow_normalizes_elementary_sixtyfour
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A≤(T : Subgroup G)) (hA : Nat.card A=64) :
    (T : Subgroup G)≤normalizer (A : Set G) := by
  obtain ⟨c,hc⟩ := exists_smul_eq G T (sourceSylow F)
  let f := (MulAut.conj c).toMonoidHom
  have hT : (T : Subgroup G).map f=sourceSylow F := by
    have hh := congrArg (fun S : Sylow 2 G => (S : Subgroup G)) hc
    simp only [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at hh
    change (T : Subgroup G).map f=sourceSylow F at hh
    exact hh
  let B := A.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hB : Nat.card B=64 := (card_map_of_injective (MulAut.conj c).injective).trans hA
  have hBS : B≤(sourceSylow F : Subgroup G) := (map_mono hAT).trans_eq hT
  have hSN : (sourceSylow F : Subgroup G)≤normalizer (B : Set G) := by
    rcases rectangleCatalogue F B hBS inferInstance hB with he | he
    · rw [he]
      exact sourceSylow_normalizes_rectangle F 2
    · rw [he]
      exact sourceSylow_normalizes_rectangle F 3
  have hh := (map_le_iff_le_comap.mp (hT ▸ hSN)).trans (le_normalizer_comap f)
  rw [comap_map_eq_self_of_injective (MulAut.conj c).injective] at hh
  exact hh

end Theory.GroupTheory.TransvectionFive.UniquenessHeld
