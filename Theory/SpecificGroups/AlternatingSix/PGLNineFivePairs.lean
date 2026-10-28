module
public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveConjugacy
public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveNormalizer
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.TenConjugacy
public import Theory.GroupTheory.SubgroupConjugation
public import GorensteinWalter.PGL2DerivedSubgroup

/-!
# A₅ overgroups with the same actual order-ten subgroup

First conjugate the A₅ subgroups in the genuine projective group, then
correct inside the target A₅ to retain their common order-ten subgroup.
Its full projective normalizer has order twenty. An outer element that
centralizes that subgroup therefore accounts for the only possible second
A₅ overgroup. All subgroups remain in the same PGL₂(9) carrier.
-/

public noncomputable section
namespace AlternatingSix.PGLNineFivePairs
open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter
local notation "P" => PGL2 Nine.F
private instance : Finite P :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Align two A₅ overgroups while retaining their original common
order-ten subgroup. -/
theorem five_conjugator_normalizing_ten (B H J : Subgroup P)
    (hB : Nat.card B = 10)
    (hH : Nonempty (H ≃* alternatingGroup (Fin 5)))
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (hBH : B ≤ H) (hBJ : B ≤ J) :
    ∃ n ∈ normalizer (B : Set P), H.map (MulAut.conj n).toMonoidHom = J := by
  obtain ⟨p,hp⟩ := PGLNineFiveConjugacy.five_subgroups_conjugate H J hH hJ
  let D := B.map (MulAut.conj p).toMonoidHom
  have hDJ : D ≤ J := hp ▸ map_mono hBH
  have hcD : Nat.card (D.subgroupOf J) = 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,
      card_map_of_injective (MulAut.conj p).injective,hB]
  have hcB : Nat.card (B.subgroupOf J) = 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv,hB]
  obtain ⟨a,ha⟩ := alternatingGroup.FiveLocalGeometry.ten_subgroups_conjugate
    hJ.some (D.subgroupOf J) (B.subgroupOf J) hcD hcB
  have hmap : D.map (MulAut.conj (a : P)).toMonoidHom = B := by
    have hm := congrArg (fun K : Subgroup J => K.map J.subtype) ha
    rw [map_map,map_subgroupOf_eq_of_le hBJ] at hm
    rw [←map_subgroupOf_eq_of_le hDJ,map_map]
    convert hm using 1
    congr 1
  have hn : B.map (MulAut.conj ((a : P)*p)).toMonoidHom = B := by
    change B.conjBy ((a : P)*p) = B
    rw [conjBy_mul]
    exact hmap
  refine ⟨(a : P)*p,mem_normalizer_iff_map_conj_eq.mpr hn,?_⟩
  change H.conjBy ((a : P)*p) = J
  rw [conjBy_mul]
  change (H.map (MulAut.conj p).toMonoidHom).map (MulAut.conj (a : P)).toMonoidHom = J
  rw [hp]
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer a.property)

/-- The two possible A₅ overgroups of the same order-ten subgroup are
related by the specified outer centralizer element. -/
theorem five_overgroups_eq_or_conjugate (B H J : Subgroup P) (t : P)
    (hB : Nat.card B = 10)
    (hH : Nonempty (H ≃* alternatingGroup (Fin 5)))
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (hBH : B ≤ H) (hBJ : B ≤ J)
    (ht : t ∉ commutator P) (htB : t ∈ centralizer (B : Set P)) :
    J = H ∨ J = H.map (MulAut.conj t).toMonoidHom := by
  obtain ⟨n,hn,hmap⟩ := five_conjugator_normalizing_ten B H J hB hH hJ hBH hBJ
  let N := normalizer (B : Set P)
  have hN : Nat.card N = 20 := PGLNineFiveNormalizer.ten_normalizer_card B hB
  have hBN : B ≤ N := le_normalizer
  have hidx : (B.subgroupOf N).index = 2 := by
    have hh := (B.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv,hB,hN] at hh
    omega
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := hH.some.symm.toMonoidHom) hH.some.symm.surjective
  have hHder : H ≤ commutator P := by
    rw [←H.commutator_eq_self]
    exact commutator_mono le_top le_top
  have htne : t ∉ B := fun hb => ht (hHder (hBH hb))
  have htN : t ∈ N := centralizer_le_normalizer (B : Set P) htB
  by_cases hnB : n ∈ B
  · left
    exact hmap.symm.trans (mem_normalizer_iff_map_conj_eq.mp (le_normalizer (hBH hnB)))
  · right
    have hb : t⁻¹*n ∈ B := by
      have hh := (B.subgroupOf N).mul_mem_iff_of_index_two hidx
        (a := (⟨t,htN⟩ : N)⁻¹) (b := ⟨n,hn⟩)
      apply hh.mpr
      simpa only [mem_subgroupOf,coe_inv,inv_mem_iff] using iff_of_false htne hnB
    have he : n = t*(t⁻¹*n) := by group
    rw [he] at hmap
    change H.conjBy (t*(t⁻¹*n)) = J at hmap
    rw [conjBy_mul] at hmap
    have hfix : H.conjBy (t⁻¹*n) = H :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer (hBH hb))
    rw [hfix] at hmap
    exact hmap.symm
end AlternatingSix.PGLNineFivePairs
