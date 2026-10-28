module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import CFSG.Quasithin.ChapterE.Section02.Elementary
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowSubnormalIntersection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Normal-core geometry of the solvable E.2.9 lift

The marked local two-core lies in the prescribed Sylow subgroup. Its
commutator with the maximal subgroup’s normal core therefore lies in
`T ∩ J = O₂(H)`. Consequently every conjugate pair generated from `V`
centralizes `J` modulo `O₂(H)`, and is subnormal in its join with `J`
through its join with `O₂(H)`. This is the source’s Sylow restriction step.

Source: Aschbacher–Smith, E.2.9, printed pp.221–222.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Witnesses.Solvable
variable {H : Type*} [Group H] [Finite H]

theorem minimalParabolic_commutator_core_le_twoCore (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    (hV : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) :
    ⁅V,ChapterB.minimalParabolicCore T hP⁆ ≤ pCore 2 H := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let P := M.pCoreIn 2
  have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  have hPT : P ≤ (T : Subgroup H) := by
    have hh := M.pCoreIn_le_sylow (T.subtype hTM)
    exact (show P ≤ (T : Subgroup H) ⊓ M by simpa using hh).trans inf_le_left
  have hMP : M ≤ normalizer (P : Set H) := by
    have hh := (pCore 2 M).le_normalizer_map M.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hcomm : ⁅V,J⁆ ≤ P := by
    apply (commutator_mono hV le_rfl).trans
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp ((normalCore_le M).trans hMP)
  rw [← ChapterB.minimalParabolic_sylow_inf_core T hP]
  exact le_inf (hcomm.trans hPT) (commutator_le_right _ _)

theorem pair_centralizes_core_modulo_twoCore (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    (hV : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (g : H) :
    let q := QuotientGroup.mk' (pCore 2 H)
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map q ≤
      centralizer ((ChapterB.minimalParabolicCore T hP).map q : Set _) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' (pCore 2 H)
  let D := J.map q
  let C := Subgroup.centralizer (D : Set (H ⧸ pCore 2 H))
  let : D.Normal := (inferInstance : J.Normal).map q (QuotientGroup.mk'_surjective _)
  have hVC : V.map q ≤ C := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact minimalParabolic_commutator_core_le_twoCore T hP V hV
  have hconj : (V.map (MulAut.conj g).toMonoidHom).map q =
      (V.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  change (V ⊔ V.map (MulAut.conj g).toMonoidHom).map q ≤ C
  rw [Subgroup.map_sup,hconj]
  apply sup_le hVC
  have he : C.map (MulAut.conj (q g)).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top _))
  exact (map_mono hVC).trans he.le

theorem pair_subnormal_in_core_join (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    (hn : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hV : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) (g : H) :
    let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
    (I.subgroupOf (I ⊔ ChapterB.minimalParabolicCore T hP)).IsSubnormal := by
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  let J := ChapterB.minimalParabolicCore T hP
  let Q := pCore 2 H
  let K := I ⊔ Q
  let L := I ⊔ J
  let q := QuotientGroup.mk' Q
  have hIK : I ≤ K := le_sup_left
  have hKL : K ≤ L := sup_le le_sup_left
    ((ChapterB.minimalParabolicTwoCore_le_core T hP).trans le_sup_right)
  have hIL := hIK.trans hKL
  have hQI : Q ≤ normalizer (I : Set H) :=
    ChapterE.twoCore_le_normalizer_conjugate_join T V hn g
  have hKI : K ≤ normalizer (I : Set H) := sup_le I.le_normalizer hQI
  have hJK : J ≤ normalizer (K : Set H) := by
    have hc : J.map q ≤ centralizer (I.map q : Set _) :=
      le_centralizer_iff.mp (pair_centralizes_core_modulo_twoCore T hP V hV g)
    have hh := (map_le_iff_le_comap.mp (hc.trans (Subgroup.centralizer_le_normalizer _))).trans
      ((I.map q).le_normalizer_comap q)
    simpa only [q,comap_map_eq,QuotientGroup.ker_mk'] using hh
  have hLK : L ≤ normalizer (K : Set H) := sup_le (hIK.trans K.le_normalizer) hJK
  let U := I.subgroupOf L
  let W := K.subgroupOf L
  have hUW : U ≤ W := fun _ hx => hIK hx
  have hW : W.Normal := normal_subgroupOf_of_le_normalizer hLK
  have hUn : (U.subgroupOf W).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hKI hx) (y : H)
  exact IsSubnormal.step U W hUW hW.isSubnormal hUn
end CFSG.Quasithin.ChapterE.Witnesses.Solvable
