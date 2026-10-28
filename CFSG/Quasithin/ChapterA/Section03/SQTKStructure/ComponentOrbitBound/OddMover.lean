module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public import Theory.GroupTheory.CComponent.QuotientLifting
/-!
# Solvability from an odd conjugate with two-group intersection

The source component-orbit bound makes every odd-order element normalize
each C-component. A nonsolvable subnormal subgroup therefore cannot meet
its odd conjugate in a two-group. The proof uses the actual two-core
quotient and lifts component normalizers through its solvable kernel.
Source: Aschbacher–Smith 1.2.1(3), applied in 13.3.14(b), printed p.891.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.ComponentOrbitBound
universe u
variable {G : Type u} [Group G] [Finite G]
theorem isSolvable_of_subnormal_odd_conjugate_intersection {κ : GroupClass.{u}}
    (hQ : IsSQTK κ (G ⧸ pCore 2 G))
    (Y : Subgroup G) (hY : Y.IsSubnormal)
    (g : G) (hg : Odd (orderOf g))
    (hI : IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Group.IsSolvable Y := by
  by_contra hn
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hn
  let B := K.map Y.subtype
  have hB : B.IsCComponent := hK.map_subtype hY
  let := pCore_isNilpotent (p := 2) (G := G)
  have hc := cComponent_normal_or_index_two_of_quotient hB (pCore 2 G)
    (ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput κ)
      hQ (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient _))
  have hgB : g ∈ normalizer (B : Set G) := by
    rcases hc with hn | hi
    · let := hn
      exact (normalizer_eq_top_iff.mpr hn).symm ▸ mem_top g
    · exact (zpowers_le.mpr ((normalizer (B : Set G)).sq_mem_of_index_two hi g))
        (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hg))
  have hBY : B ≤ Y := map_subtype_le _
  have hBg : B ≤ Y.map (MulAut.conj g).toMonoidHom := by
    rw [← (mem_normalizer_iff_map_conj_eq).mp hgB]
    exact map_mono hBY
  have hB2 : IsPGroup 2 B := hI.to_le (le_inf hBY hBg)
  let := hB2.isNilpotent
  exact hB.not_isSolvable inferInstance
end CFSG.Quasithin.ChapterA.Section03.ComponentOrbitBound
