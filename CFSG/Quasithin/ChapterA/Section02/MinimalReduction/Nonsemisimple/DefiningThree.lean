module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.PrimeCover
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.DefiningLocalRank
public import Theory.SpecificGroups.PSL3.DefiningCoverKernel
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeField
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.PrimeSquare
/-!
# Closing the defining PSL₃ and PSU₃ source branches

A defining-prime multiplier theorem excludes every nontrivial perfect
central p-cover of the actual projective model. The nilpotent-kernel
extraction then forces the original p-core to have rank greater than two,
so the original failure witness gives local p-rank greater than two in S.
The same multiplier exclusion makes S→S/Z(S) coprime at p; its odd kernel
therefore transports this local-rank failure to the actual projective model.
The checked defining local bound and proper SL₂ section contradict induction.

For PSU₃, degrees greater than two are already excluded by the proper SL₂
section; the genuine prime-field and prime-square multiplier proofs handle
the remaining degrees. No prime-core identity, local-rank failure, or quotient
quasithinness is assumed.

Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
open Nonsemisimple.RankTwoSieve
open BenderSuzuki.MatrixGroups
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

private theorem no_prime_kernel_of_psl_three
    {Q : Type u} [Group Q] [Finite Q] {p e : ℕ}
    (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hm : ClassicalGroup.IsPSL Q 3 (p ^ e))
    (L : Type u) [Group L] [Finite L] (c : PerfectCentralCovering.Cover L Q) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨F, _, _, hcard, ⟨a⟩⟩ := hm
  let d : PerfectCentralCovering.Cover L (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    { toMonoidHom := a.toMonoidHom.comp c.toMonoidHom
      surjective := a.surjective.comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        intro x hx
        apply c.ker_le_center
        exact a.injective (by simpa using hx) }
  have hk : d.toMonoidHom.ker = c.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective c.toMonoidHom a.toMonoidHom a.injective
  rw [← hk]
  exact Matrix.PSL3.not_defining_prime_dvd_cover_kernel hp ho he hcard d

private theorem no_prime_kernel_of_psu_three_small
    {Q : Type u} [Group Q] [Finite Q] {p e : ℕ}
    (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hm : ClassicalGroup.IsPSU Q 3 (p ^ e))
    (L : Type u) [Group L] [Finite L] (c : PerfectCentralCovering.Cover L Q) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨a⟩⟩ := hm
  let d : PerfectCentralCovering.Cover L (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toMonoidHom := a.toMonoidHom.comp c.toMonoidHom
      surjective := a.surjective.comp c.surjective
      isPerfect := c.isPerfect
      ker_le_center := by
        intro x hx
        apply c.ker_le_center
        exact a.injective (by simpa using hx) }
  have hk : d.toMonoidHom.ker = c.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective c.toMonoidHom a.toMonoidHom a.injective
  rw [← hk]
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  rcases he with rfl | rfl
  · exact HermitianForm.UniversalCover.OddKernelBound.not_defining_prime_dvd_kernel J hp hp2
      (by simpa using hcard) (by simpa using hconj) d
  · exact HermitianForm.UniversalCover.OddKernelBound.PrimeSquare.not_defining_prime_dvd_kernel
      J d hp hp2 hcard hconj

theorem CounterexampleToTheoremA.not_defining_psl_three_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (e : ℕ) (he : 0 < e) (hm : ClassicalGroup.IsPSL (S ⧸ center S) 3 (p ^ e)) : False := by
  have hl := h.centralQuotient_local_rank_gt_two_of_no_prime_cover ih.theoremA
    (no_prime_kernel_of_psl_three h.2.2.2.2.1 h.2.2.2.2.2.1 he hm)
  obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
  exact no_psl_three_quotient_of_defining_local_rank_gt_two ih h.1 h.2.1
    ((QuotientGroup.mk' (center S)).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) p e
    h.2.2.2.2.1 h.2.2.2.2.2.1 he hm hl

theorem CounterexampleToTheoremA.not_defining_psu_three_centralQuotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (e : ℕ) (he : 0 < e) (hm : ClassicalGroup.IsPSU (S ⧸ center S) 3 (p ^ e)) : False := by
  obtain ⟨f,hf⟩ := h.exists_surjective ih.theoremA
  let g := (QuotientGroup.mk' (center S)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  by_cases he2 : 2 < e
  · exact no_psu_three_large_quotient ih h.1 h.2.1 g hg p e
      h.2.2.2.2.1 h.2.2.2.2.2.1 he2 hm
  have hl := h.centralQuotient_local_rank_gt_two_of_no_prime_cover ih.theoremA
    (no_prime_kernel_of_psu_three_small h.2.2.2.2.1 h.2.2.2.2.2.1 (by omega) hm)
  exact no_psu_three_quotient_of_defining_local_rank_gt_two ih h.1 h.2.1 g hg p e
    h.2.2.2.2.1 h.2.2.2.2.2.1 he hm hl

end CFSG.Quasithin.ChapterA.Section02
