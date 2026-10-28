module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.LocalGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Saturation
public import Theory.GroupTheory.ConjugateSpanOrder
import Mathlib.Tactic

/-!
# The original maximal overgroup and its conjugate span

The point stabilizer containing the Sylow image pulls back to the unique
maximal overgroup of the original Sylow subgroup. An even cubic permutation
lifts to the actual residual inside that overgroup. It and the original
Baumann four-group show that the prescribed conjugate span maps onto S₄.

Source: Aschbacher–Smith, C.1.24 and 3.1.7, printed pp.130–131 and 575–576.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB ChapterB.Offenders BinaryPermutation
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem source_maximal_preimage (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (q : H →* Sym) (hq : Function.Surjective q) (a : Sym)
    (hD : (D 5).map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup H).map q) :
    minimalParabolicMax T hP = (pointFour.map (MulAut.conj a).toMonoidHom).comap q := by
  apply (minimalParabolicMax_unique T hP _ _).symm
  · exact isCoatom_comap_of_surjective hq ((OrderIso.isCoatom_iff (MulAut.conj a).mapSubgroup pointFour).mpr pointFour_coatom)
  · exact map_le_iff_le_comap.mp (two_group_le_conjugate_pointFour (T.isPGroup'.map q) a hD)

theorem source_conjugate_span_image (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (q : H →* Sym) (hq : Function.Surjective q) (S : Subgroup H)
    (hST : S ≤ T) (a : Sym) (hS : S.map q = (D 5).map (MulAut.conj a).toMonoidHom) :
    (conjugateSpanBy S (pResidual 2 H ⊓ minimalParabolicMax T hP)).map q =
      pointFour.map (MulAut.conj a).toMonoidHom := by
  let M := minimalParabolicMax T hP
  let B := pointFour.map (MulAut.conj a).toMonoidHom
  have hTM : (T : Subgroup H) ≤ M := (minimalParabolicMax_spec T hP).2
  have hM : M = B.comap q := source_maximal_preimage T hP q hq a (hS ▸ map_mono hST)
  have hMB : M.map q = B := by rw [hM, map_comap_eq_self_of_surjective hq]
  have heven : a * localCubic * a⁻¹ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_inv,
      Equiv.Perm.mem_alternatingGroup.mp localCubic_even, mul_one, mul_inv_cancel]
  obtain ⟨g, hg, hqg⟩ : ∃ g ∈ pResidual 2 H, q g = a * localCubic * a⁻¹ :=
    (source_residual_image q hq ▸ heven : a * localCubic * a⁻¹ ∈ (pResidual 2 H).map q)
  have hgM : g ∈ M := by
    rw [hM]
    change q g ∈ B
    rw [hqg]
    exact mem_map_of_mem _ localCubic_mem_pointFour
  let I := conjugateSpanBy S (pResidual 2 H ⊓ M)
  have hIM : I ≤ M := conjugateSpanBy_le (hST.trans hTM) (inf_le_right.trans M.le_normalizer)
  apply le_antisymm
  · exact (map_mono hIM).trans hMB.le
  · have hconj : (S.map (MulAut.conj g).toMonoidHom).map q =
        (S.map q).map (MulAut.conj (q g)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    have hSI : S ≤ I := le_conjugateSpanBy _ _
    have hconjI : S.map (MulAut.conj g).toMonoidHom ≤ I := by
      rintro x ⟨s, hs, rfl⟩
      exact subset_closure ⟨g, ⟨hg, hgM⟩, s, hs, rfl⟩
    have hjoin := sup_le (map_mono (f := q) hSI) (map_mono (f := q) hconjI)
    rw [hconj, hS, hqg, local_two_conjugate_four_groups_generate] at hjoin
    exact hjoin
end CFSG.Quasithin.ChapterC.SymmetricFive
