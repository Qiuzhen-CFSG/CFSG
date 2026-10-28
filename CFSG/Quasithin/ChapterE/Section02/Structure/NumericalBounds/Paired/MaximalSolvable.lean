module
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedMaximal
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Placement
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Solvability of the original paired maximal subgroup

The two factor intersections with M are conjugate, commute, and have a
join normalized by the prescribed Sylow. The source maximal product formula
therefore makes M an extension of their solvable product by a two-group.
For binary PSL₂ and Suzuki factors the actual rank-one Sylow normalizer
calculation supplies solvability of the first intersection.

This proves the genuine local input needed to place M in every positive
E-generation target. It does not assert paired E-generation or any actor
transfer. The generation owner must still construct an escaping E-member.

Source: Aschbacher–Smith E.2.2(1), printed pp.215–216, and the paired
specialization of the E.1.11 normalizer argument, printed pp.213–214.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
variable {G : Type*} [Group G] [Finite G]

/-- Solvability of one factor intersection controls the full paired maximal. -/
theorem maximal_solvable_of_intersection (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    (hsolv : Group.IsSolvable ((ChapterB.minimalParabolicMax T hP) ⊓ K : Subgroup G)) :
    Group.IsSolvable (ChapterB.minimalParabolicMax T hP) := by
  let M := ChapterB.minimalParabolicMax T hP
  let A := M ⊓ K
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  have hTM : (T : Subgroup G) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  obtain ⟨t, ht, hprod⟩ := source_paired_maximal_product hG T hP hK hgen hn
  have htn : (t : G) ∉ normalizer (K : Set G) := fun h => ht (mem_normalizer_iff_map_conj_eq.mp h)
  have hi : (normalizer (K : Set G)).index = 2 := by
    rcases component_normal_or_pair hG T hK hgen with h | ⟨s, hs⟩
    · exact (hn h.1).elim
    · exact hs.2.2.2.2.2.2
  let D := K.map (MulAut.conj (t:G)).toMonoidHom
  let B := A.map (MulAut.conj (t:G)).toMonoidHom
  have hB : B = M ⊓ D := by
    dsimp [B,A,D]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (t:G)).injective,
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hTM t.property))]
  have hSA : S ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_left.trans (hTM.trans M.le_normalizer)) inf_le_right).trans
      inf_normalizer_le_normalizer_inf
  have hSN : S ≤ normalizer (K : Set G) := inf_le_right
  have hSt : S.map (MulAut.conj (t:G)).toMonoidHom = S := by
    let : (normalizer (K : Set G)).Normal := normal_of_index_eq_two hi
    dsimp [S]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (t:G)).injective,
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer t.property),
      Subgroup.Normal.map_conj_eq]
  have hSB : S ≤ normalizer (B : Set G) := by
    dsimp only [B]
    rw [← map_equiv_normalizer_eq A (MulAut.conj (t:G))]
    rw [← hSt]
    exact map_mono hSA
  have hSAB : S ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    (le_inf hSA hSB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have htt : (t:G)^2 ∈ S := ⟨(T : Subgroup G).pow_mem t.property 2,
    (normalizer (K : Set G)).sq_mem_of_index_two hi t⟩
  have hBB : B.map (MulAut.conj (t:G)).toMonoidHom = A := by
    change (A.map _).map _ = A
    rw [map_map]
    have he : (MulAut.conj (t:G)).toMonoidHom.comp (MulAut.conj (t:G)).toMonoidHom =
        (MulAut.conj ((t:G)^2)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,pow_two]
      group
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hSA htt)
  have htAB : (t:G) ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup]
    change B ⊔ B.map (MulAut.conj (t:G)).toMonoidHom = A ⊔ B
    rw [hBB,sup_comm]
  have hTAB : (T : Subgroup G) ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro x hx
    by_cases hxN : x ∈ normalizer (K : Set G)
    · exact hSAB ⟨hx,hxN⟩
    · have hxt : x * (t:G)⁻¹ ∈ S := by
        refine ⟨(T : Subgroup G).mul_mem hx ((T : Subgroup G).inv_mem t.property),?_⟩
        change x * (t:G)⁻¹ ∈ normalizer (K : Set G)
        rw [(normalizer (K : Set G)).mul_mem_iff_of_index_two hi,
          (normalizer (K : Set G)).inv_mem_iff]
        exact iff_of_false hxN htn
      simpa using (normalizer ((A ⊔ B : Subgroup G) : Set G)).mul_mem (hSAB hxt) htAB
  have hcomm : B ≤ centralizer (A : Set G) := by
    have hh := hK.commutator_eq_bot_of_ne (hK.map_conj (t:G)) ht.symm
    rw [commutator_comm] at hh
    exact (hB ▸ inf_le_right).trans ((commutator_eq_bot_iff_le_centralizer.mp hh).trans
      (centralizer_le (show (A : Set G) ⊆ K from inf_le_right)))
  let : Group.IsSolvable A := hsolv
  let : Group.IsSolvable B := Group.isSolvable_of_surjective
    (f := ((MulAut.conj (t:G)).subgroupMap A).toMonoidHom) ((MulAut.conj (t:G)).subgroupMap A).surjective
  let : Group.IsSolvable (A ⊔ B : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes A B (hcomm.trans (Subgroup.centralizer_le_normalizer _))
  let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
  have he : M = (A ⊔ B) ⊔ (T : Subgroup G) := by
    apply SetLike.coe_injective
    rw [coe_mul_of_right_le_normalizer_left (A ⊔ B) T hTAB,
      coe_mul_of_right_le_normalizer_left A B (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
    exact hprod
  change Group.IsSolvable M
  rw [he]
  exact Group.isSolvable_sup_of_normalizes _ _ hTAB

/-- The binary linear and Suzuki source models discharge intersection solvability. -/
theorem rankOne_maximal_solvable (hG : IsStronglyQuasithin G) (T : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup G) (hK : IsComponent G K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup G) = ⊤) (hn : ¬ K.Normal)
    (hm : ChapterF.Source.IsRankOneModel K) :
    Group.IsSolvable (ChapterB.minimalParabolicMax T hP) := by
  have heven : 2 ∣ Nat.card K := by
    by_contra h
    have ho : Odd (Nat.card K) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using h)
    let := hK.2
    exact Group.IsPerfect.not_isSolvable K (odd_order_theorem K ho)
  let M := ChapterB.minimalParabolicMax T hP
  have hB := Witnesses.PairedBender.component_borel_intersection T hP K hK heven
    (generating_component_orbit_eq_residual hG T hK hgen) hm
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK.1
  have hsolv : Group.IsSolvable (M.subgroupOf K) := by
    rw [hB, ← hS]
    exact (hm.rankOneSylowFacts S).solvable
  let := hsolv
  let e : M.subgroupOf K ≃* (M ⊓ K : Subgroup G) :=
    ((M.subgroupOf K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype M K))
  exact maximal_solvable_of_intersection hG T hP K hK hgen hn
    (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
end CFSG.Quasithin.ChapterE.Structure.NumericalBounds.Paired
