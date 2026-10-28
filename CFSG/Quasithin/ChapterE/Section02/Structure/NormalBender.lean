module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import CFSG.Quasithin.ClassificationModels.Families
import all CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The actual Borel of a normal Bender minimal parabolic

A proper Sylow-invariant subgroup of a normal supplement lies in the unique
maximal overgroup. The genuine concrete rank-one overgroup calculations then
identify its intersection with the supplement as the Sylow normalizer.
The set-product decomposition H = KT identifies the entire maximal subgroup
as that Borel times T and proves its solvability.

Source: the normal Bender row E.2.2(2a), printed pp.215–216. The imported
rank-one model calculations are independent of E.2.2; none of the Borel or
maximality conclusions is an input to the source theorem.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
variable {H : Type*} [Group H] [Finite H]

theorem invariant_subgroup_le_max (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K X : Subgroup H)
    (hXK : X < K) (hS : K ⊓ (T : Subgroup H) ≤ X)
    (hn : (T : Subgroup H) ≤ normalizer (X : Set H)) :
    X ≤ ChapterB.minimalParabolicMax T hP :=
  le_sup_left.trans (hP.1.le_maximal
    ⟨(ChapterB.minimalParabolicMax_spec T hP).2,
      (ChapterB.minimalParabolicMax_spec T hP).1.covBy_top⟩ le_sup_right
    (lt_top_iff_ne_top.mpr (ChapterB.sup_sylow_ne_top T K X hXK.le hn hS hXK.ne)))

theorem max_intersection_normal (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hu : Order.HasUniqueMaximalOver (K ⊓ (T : Subgroup H)) K)
    {B : Subgroup H} (hB : K ⊓ (T : Subgroup H) ≤ B ∧ B ⋖ K) :
    ChapterB.minimalParabolicMax T hP ⊓ K = B := by
  let M := ChapterB.minimalParabolicMax T hP
  have hMI : M ⊓ K < K := by
    apply lt_of_le_of_ne inf_le_right
    intro he
    have hKM : K ≤ M := he ▸ inf_le_left
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top (top_unique (by
      rw [← hgen];exact sup_le hKM (ChapterB.minimalParabolicMax_spec T hP).2))
  have hSB : (T : Subgroup H) ≤ normalizer (B : Set H) := by
    intro t ht
    let e := MulAut.conj t
    have hKe : K.map e.toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp
      (show t ∈ normalizer (K : Set H) from le_normalizer_of_normal ht)
    have hSI : (K ⊓ (T : Subgroup H)).map e.toMonoidHom = K ⊓ (T : Subgroup H) :=
      mem_normalizer_iff_map_conj_eq.mp
        (inf_normalizer_le_normalizer_inf ⟨le_normalizer_of_normal ht,(T : Subgroup H).le_normalizer ht⟩)
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply hu.2.unique _ hB
    refine ⟨?_,?_⟩
    · rw [← hSI];exact map_mono hB.1
    · have hh := (apply_covBy_apply_iff e.mapSubgroup).mpr hB.2
      change B.map e.toMonoidHom ⋖ K.map e.toMonoidHom at hh
      rwa [hKe] at hh
  apply le_antisymm
  · exact hu.le_maximal hB
      (le_inf (inf_le_right.trans (ChapterB.minimalParabolicMax_spec T hP).2) inf_le_left) hMI
  · exact le_inf (invariant_subgroup_le_max T hP K B hB.2.lt hB.1 hSB) hB.2.le
theorem bender_sylow_facts {D : Type*} [Group D]
    (hm : ClassificationModels.IsBenderModel D) (S : Sylow 2 D) :
    ChapterF.Source.RankOneSylowFacts S := by
  apply ChapterF.Source.IsRankOneModel.rankOneSylowFacts _ S
  cases hm with
  | linear n hn h => exact .linear n (by omega) h
  | unitary n hn h => exact .projective_unitary n (by omega) h
  | suzuki m _ h => exact .suzuki m h

theorem source_bender_borel (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hm : ClassificationModels.IsBenderModel K) :
    ChapterB.minimalParabolicMax T hP ⊓ K =
      ChapterF.Source.borel K (T : Subgroup H) := by
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup H) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have h := ChapterF.Source.rankOneBorelFacts_of_sylow K (T : Subgroup H)
    S hSm (bender_sylow_facts hm S)
  have hSB : K ⊓ (T : Subgroup H) ≤ ChapterF.Source.borel K (T : Subgroup H) := by
    change _ ≤ K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)
    exact le_inf inf_le_left (by simpa only [inf_comm K] using ((T : Subgroup H) ⊓ K).le_normalizer)
  have hc : ChapterF.Source.borel K (T : Subgroup H) ⋖ K := by
    refine ⟨h.proper,?_⟩
    intro L hBL hLK
    have hLB := h.unique_maximal L (by simpa only [inf_comm] using hSB.trans hBL.le) hLK
    exact hBL.not_ge hLB
  have hu : Order.HasUniqueMaximalOver (K ⊓ (T : Subgroup H)) K := by
    refine ⟨hSB.trans_lt h.proper,_,⟨hSB,hc⟩,?_⟩
    intro L hL
    have hLB := h.unique_maximal L (by simpa only [inf_comm] using hL.1) hL.2.lt
    exact ((hL.2.eq_or_eq hLB h.proper.le).resolve_right h.proper.ne).symm
  exact max_intersection_normal T hP K hgen hu ⟨hSB,hc⟩
omit [Finite H] in
theorem max_eq_intersection_sup_sylow (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    ChapterB.minimalParabolicMax T hP =
      (ChapterB.minimalParabolicMax T hP ⊓ K) ⊔ (T : Subgroup H) := by
  let M := ChapterB.minimalParabolicMax T hP
  have hTM := (ChapterB.minimalParabolicMax_spec T hP).2
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (K : Set H) * ((T : Subgroup H) : Set H) := by
      rw [← coe_mul_of_right_le_normalizer_left K (T : Subgroup H) le_normalizer_of_normal,hgen]
      trivial
    obtain ⟨k,hk,t,ht,hkt⟩ := hp
    have hkM : k ∈ M := by
      have hh := M.mul_mem hx (M.inv_mem (hTM ht))
      rwa [← hkt,mul_inv_cancel_right] at hh
    rw [← hkt]
    exact mul_mem_sup ⟨hkM,hk⟩ ht
  · exact sup_le inf_le_left hTM

theorem source_normal_bender_conclusions (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hm : ClassificationModels.IsBenderModel K) :
    (ChapterB.minimalParabolicMax T hP).subgroupOf K =
      normalizer ((T : Subgroup H).subgroupOf K : Set K) ∧
    ChapterB.minimalParabolicMax T hP =
      ChapterF.Source.borel K (T : Subgroup H) ⊔ (T : Subgroup H) ∧
    Group.IsSolvable (ChapterB.minimalParabolicMax T hP) := by
  have he := source_bender_borel T hP K hgen hm
  have hM : ChapterB.minimalParabolicMax T hP =
      ChapterF.Source.borel K (T : Subgroup H) ⊔ (T : Subgroup H) := by
    rw [← he]
    exact max_eq_intersection_sup_sylow T hP K hgen
  refine ⟨?_,hM,?_⟩
  · have h := congrArg (fun U : Subgroup H => U.subgroupOf K) he
    change (ChapterB.minimalParabolicMax T hP ⊓ K).subgroupOf K =
      (K ⊓ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)).subgroupOf K at h
    rw [inf_subgroupOf_right,inf_subgroupOf_left,
      subgroupOf_normalizer_eq inf_le_right,inf_subgroupOf_right] at h
    exact h
  · obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
    have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup H) ⊓ K := by
      rw [hS,subgroupOf_map_subtype]
    have hf := ChapterF.Source.rankOneBorelFacts_of_sylow K (T : Subgroup H)
      S hSm (bender_sylow_facts hm S)
    let := hf.solvable
    let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
    have hn : (T : Subgroup H) ≤ normalizer (ChapterF.Source.borel K (T : Subgroup H) : Set H) := by
      rw [← he]
      exact (le_inf (((ChapterB.minimalParabolicMax_spec T hP).2).trans
        (ChapterB.minimalParabolicMax T hP).le_normalizer) le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
    rw [hM]
    exact Group.isSolvable_sup_of_normalizes _ _ hn
end CFSG.Quasithin.ChapterE.Structure
