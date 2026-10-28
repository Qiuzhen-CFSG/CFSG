module

public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent.Flags
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveFlags

/-!
# Two-core absorption in the actual two-node parabolics

For the four-space endpoint pair, the remaining cut is the marked
two-space. Its two-core is the literal elementary radical. In standard
coordinates the radical has support in the upper-right 2 by 2 block;
cubic actors on the diagonal blocks absorb all its shears into O².
Conjugating the standard basis to the given basis preserves both cores
and residuals. The five-space assertion applies the exact diagonal-kernel
calculation for all three nonadjacent pairs, in either node order.

Both conclusions retain the ambient subtype embeddings. They supply the
core-absorption premise of the residual-normalizer calculation, without
assuming an overlap or normalizer equality.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.25, printed p.960 (PDF p.977).
-/

public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open BinaryLinear.CubicPairNormalizers.CoreAbsorption
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

private def fourBlock (r : Fin 4) : ℕ := if r.val < 2 then 0 else 1

private theorem four_root_mem (r s : Fin 4) (hrs : r ≠ s)
    (hc : fourBlock r ≤ fourBlock s) :
    root r s hrs 1 ∈ cutStabilizer standardBasis {1} := by
  apply (mem_standard_cutStabilizer_iff {1} _).mpr
  intro k hk i j hki hjk
  have hk' : k = 1 := hk
  subst k
  rw [matrix_apply]
  simp only [root_apply, standardBasis, Pi.basisFun_apply, Pi.single_apply, mul_one]
  have hji : j ≠ i := by intro he; subst j; omega
  by_cases hir : i = r
  · subst i
    have hsj : s ≠ j := by
      intro he
      subst j
      simp only [fourBlock, if_neg (show ¬r.val < 2 by omega),
        if_pos (show s.val < 2 by omega)] at hc
      omega
    simp [hji.symm, hsj]
  · simp [hji.symm, hir]

private theorem four_radical_entries (g : LinearGroup 4)
    (hg : g ∈ radical (cutSpace standardBasis 1)) (r s : Fin 4)
    (h : s.val < 2 ∨ 2 ≤ r.val) : entries g r s = if r = s then 1 else 0 := by
  have hb (i : Fin 4) : standardBasis i = Pi.single i 1 := by
    simp [standardBasis, Pi.basisFun_apply]
  rcases h with hs | hr
  · have hsW : standardBasis s ∈ cutSpace standardBasis 1 :=
      (basis_mem_cutSpace standardBasis 1 s).mpr (by omega)
    have he := congrFun (hg.1 _ hsW) r
    simpa [entries, hb, Pi.single_apply, eq_comm] using he
  · have he := (mem_standard_cutSpace_iff 1 _).mp (hg.2 (Pi.single s 1)) r (by omega)
    change g (Pi.single s 1) r - (Pi.single s (1 : ZMod 2) : Space 4) r = 0 at he
    simpa [entries, Pi.single_apply, eq_comm] using sub_eq_zero.mp he

private theorem four_standard_core_le_residual :
    pCore 2 (cutStabilizer standardBasis ({1} : Set (Fin 3))) ≤
      pResidual 2 (cutStabilizer standardBasis ({1} : Set (Fin 3))) := by
  let P := cutStabilizer standardBasis ({1} : Set (Fin 3))
  have hPe : P = parabolic (cutSpace standardBasis 1) := by
    simp [P, cutStabilizer]
  intro g hg
  have hrad : g.val ∈ radical (cutSpace standardBasis 1) := by
    have hm : g.val ∈ (pCore 2 P).map P.subtype := mem_map.mpr ⟨g, hg, rfl⟩
    rwa [hPe, map_twoCore_eq_radical] at hm
  have hgR : g.val ∈ (pResidual 2 P).map P.subtype := by
    apply upper_four_mem
    · intro r s hsr
      have he := four_radical_entries g.val hrad r s (by
        have hv : s.val < r.val := hsr
        omega)
      simpa [ne_of_gt hsr] using he
    · intro r
      simpa using four_radical_entries g.val hrad r r (by omega)
    · intro r s hrs
      by_cases hcross : fourBlock r < fourBlock s
      · have hp : ∀ r s : Fin 4, fourBlock r < fourBlock s →
            (∃ k, k ≠ r ∧ fourBlock k = fourBlock r) ∨
            (∃ k, k ≠ s ∧ fourBlock k = fourBlock s) := by decide
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (entries g.val r s) with hz | ho
        · rw [hz, root_zero]; exact one_mem _
        · rw [ho]
          exact root_mem_residual fourBlock P four_root_mem r s (ne_of_lt hrs)
            hcross (hp r s hcross)
      · have hcoords : s.val < 2 ∨ 2 ≤ r.val := by
          by_contra hn
          simp only [not_or, not_lt, not_le] at hn
          have : fourBlock r < fourBlock s := by
            simp only [fourBlock, if_pos hn.2, if_neg (not_lt.mpr hn.1)]
            decide
          exact hcross this
        rw [four_radical_entries g.val hrad r s hcoords, if_neg (ne_of_lt hrs), root_zero]
        exact one_mem _
  obtain ⟨x, hx, he⟩ := mem_map.mp hgR
  exact (Subtype.ext he : x = g) ▸ hx

/-- The endpoint-pair parabolic has its actual two-core contained in O². -/
theorem fourPair_twoCore_le_residual (b : Basis 3) :
    (pCore 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype ≤
    (pResidual 2 (fourParabolic b ({0,2} : Set (Fin 3)))).map
      (fourParabolic b ({0,2} : Set (Fin 3))).subtype := by
  have hc : ({0,2} : Set (Fin 3))ᶜ = {1} := by
    ext k; fin_cases k <;> simp
  have he : fourParabolic b ({0,2} : Set (Fin 3)) = cutStabilizer b {1} :=
    congrArg (cutStabilizer b) hc
  rw [he]
  apply Subgroup.map_mono
  let a := standardBasis.equiv b (Equiv.refl _)
  let e : cutStabilizer standardBasis ({1} : Set (Fin 3)) ≃*
      cutStabilizer b ({1} : Set (Fin 3)) :=
    ((MulAut.conj a).subgroupMap _).trans (MulEquiv.subgroupCongr (by
      change (cutStabilizer standardBasis ({1} : Set (Fin 3))).map
        (MulAut.conj a).toMonoidHom = _
      rw [cutStabilizer_map_conj]
      congr 1
      ext i
      simp [a]))
  calc
    pCore 2 (cutStabilizer b ({1} : Set (Fin 3))) =
        (pCore 2 (cutStabilizer standardBasis ({1} : Set (Fin 3)))).map e.toMonoidHom :=
      (pCore_map_iso 2 e).symm
    _ ≤ (pResidual 2 (cutStabilizer standardBasis ({1} : Set (Fin 3)))).map e.toMonoidHom :=
      Subgroup.map_mono four_standard_core_le_residual
    _ = pResidual 2 (cutStabilizer b ({1} : Set (Fin 3))) := map_pResidual 2 e

/-- Every nonadjacent pair, in either order, absorbs its actual embedded two-core. -/
theorem fivePair_twoCore_le_residual (b : BinaryLinear.FiveFlagGeometry.FiveBasis)
    (i j : Fin 4) (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (pCore 2 (fiveParabolic b {i,j})).map (fiveParabolic b {i,j}).subtype ≤
      (pResidual 2 (fiveParabolic b {i,j})).map (fiveParabolic b {i,j}).subtype :=
  Subgroup.map_mono (five_flag_core_le_residual b i j h)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
