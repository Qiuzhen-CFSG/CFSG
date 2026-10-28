module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import CFSG.Quasithin.ChapterF.Section06.Elementary.OddNormal
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreSurjective

/-!
# Goldschmidt action quotients with distinct residual directions

Let A,B be a Goldschmidt triple and C a normal subgroup containing O₂(D).
If the image of O²(B) does not normalize the image of O²(A), then
A ∩ C = B ∩ C = O₂(D), C is solvable, and the literal images of A and B
form a Goldschmidt triple with their full original overlap.

F.6.7 places both local kernels inside the vertex two-cores; F.6.8 and
odd-order solvability identify the kernels. The common Sylow images have
index three, so any larger overlap would identify the vertex images and
contradict the residual hypothesis. These results supply the moving-plane cubic completion in Chapter 14.
They extend the earlier point-normalizing argument at a reusable boundary
without changing its established import chain.

Source: Aschbacher–Smith, F.6.7–8, printed p.305, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF

/-- A normal kernel above the ambient two-core, whose residual images do not
normalize one another, is solvable and has the exact two-core intersections. -/
theorem IsGoldschmidtTriple.kernel_intersections_of_residual_escape
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    A ⊓ C = pCore 2 D ∧ B ⊓ C = pCore 2 D ∧ Group.IsSolvable C := by
  let q := QuotientGroup.mk' C
  have hAC : A ⊓ C ≤ (pCore 2 A).map A.subtype := by
    apply (ht.left_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 A).map A.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz,normalizer_eq_top]
    exact le_top
  have hBC : B ⊓ C ≤ (pCore 2 B).map B.subtype := by
    apply (ht.right_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 B).map B.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz]
    exact bot_le
  have hTC : (A ⊓ B) ⊓ C = pCore 2 D := le_antisymm
    (ht.normal_intersection_le_twoCore C hAC hBC)
    (le_inf ht.twoCore_isGreatest.1.1 hQC)
  have hA := ht.left_intersection_eq_core_intersection C hAC
  have hB := ht.symm.left_intersection_eq_core_intersection C hBC
  have hsol : Group.IsSolvable (C ⧸ (pCore 2 D).subgroupOf C) := by
    have hh := ht.normal_quotient_solvable C hAC hBC
    rwa [sup_eq_left.mpr hQC] at hh
  let : Group.IsNilpotent ((pCore 2 D).subgroupOf C) :=
    (pCore_isPGroup (p := 2) (G := D)).comap_subtype.isNilpotent
  exact ⟨hA.1.trans (hA.2.trans hTC),
    hB.1.trans (hB.2.trans (by simpa only [inf_comm B A] using hTC)),
    (Group.isSolvable_iff_subgroup_quotient ((pCore 2 D).subgroupOf C)).mpr
      ⟨inferInstance,hsol⟩⟩

private def action_local_quotient_equiv
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (f : D →* E) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (D ⧸ pCore 2 D) ≃* (E ⧸ pCore 2 E) := by
  let q := (QuotientGroup.mk' (pCore 2 E)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : q.ker = pCore 2 D := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

private theorem action_intermediate {D : Type*} [Group D] {A B C : Subgroup D}
    (hAB : A ≤ B) (hBC : B ≤ C) (hi : A.relIndex C = 3) : B = A ∨ B = C := by
  have hm := relIndex_mul_relIndex A B C hAB hBC
  rw [hi] at hm
  have hp : (A.relIndex B * B.relIndex C).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hA⟩
  · exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hB))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hA) hAB)

/-- Residual escape preserves the full vertex intersection in the quotient
and produces a Goldschmidt triple on the literal quotient images. -/
theorem IsGoldschmidtTriple.quotient_triple_of_residual_escape
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    let q := QuotientGroup.mk' C
    A.map q ⊓ B.map q = (A ⊓ B).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  let q := QuotientGroup.mk' C
  obtain ⟨hAC,hBC,_⟩ := ht.kernel_intersections_of_residual_escape C hQC hout
  have hlocal (J : Subgroup D) (hj : J ⊓ C = pCore 2 D)
      (e : Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((J.map q) ⧸ pCore 2 (J.map q)) ≃* Equiv.Perm (Fin 3)) := by
    have hk : IsPGroup 2 (q.subgroupMap J).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      have he : C.subgroupOf J = (pCore 2 D).subgroupOf J := by
        ext x
        change (x : D) ∈ C ↔ (x : D) ∈ pCore 2 D
        rw [←hj]
        exact (and_iff_right x.property).symm
      rw [he]
      exact pCore_isPGroup.comap_subtype
    exact ⟨(action_local_quotient_equiv _ (q.subgroupMap_surjective J) hk).symm.trans e.some⟩
  have hA := hlocal A hAC ht.quotient_left
  have hB := hlocal B hBC ht.quotient_right
  obtain ⟨T,hT⟩ := ht.intersection_sylow
  let S := T.mapSurjective (QuotientGroup.mk'_surjective C)
  have hS : (S : Subgroup _) = (A ⊓ B).map q := by
    change (T : Subgroup D).map q = _
    rw [hT]
  have hSA : (S : Subgroup _) ≤ A.map q := hS ▸ map_mono inf_le_left
  have hSB : (S : Subgroup _) ≤ B.map q := hS ▸ map_mono inf_le_right
  have hAi : (S : Subgroup _).relIndex (A.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hA.some (S.subtype hSA)
  have hBi : (S : Subgroup _).relIndex (B.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hB.some (S.subtype hSB)
  have hi : A.map q ⊓ B.map q = (A ⊓ B).map q := by
    rcases action_intermediate (le_inf hSA hSB) inf_le_left hAi with hI | heA
    · exact hI.trans hS
    rcases action_intermediate (le_inf hSA hSB) inf_le_right hBi with hI | heB
    · exact hI.trans hS
    have he : A.map q = B.map q := heA.symm.trans heB
    apply False.elim
    apply hout
    rw [map_embedded_pResidual,map_embedded_pResidual,he]
    exact ((pResidual 2 (B.map q)).map (B.map q).subtype).le_normalizer
  refine ⟨hi,?_,hA,hB,S,?_⟩
  · rw [←Subgroup.map_sup,ht.generated,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  · exact hi.trans hS.symm

end CFSG.Quasithin.ChapterF
