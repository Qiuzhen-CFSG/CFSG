module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion.Nonfusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Inputs

/-!
# Whole-module TI under the temporary diagonal-centralizer bound

Every nonidentity vector is pure or diagonal. The original M is transitive
on each class, and pure vectors are not fused to diagonal vectors in G.
The survivor controls pure point centralizers; conjugacy to the specified
central involution transports its temporary centralizer bound to every
diagonal vector. The source equality N_G(V)=M now gives all hypotheses
of I.6.1(1), proving precisely `WholeModuleTIAt` for every eligible z.

Source: Aschbacher--Smith, 10.3.2, first paragraph, printed p.756,
PDF p.773 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The first paragraph of source 10.3.2, for every central involution in
V. Natural-action transitivity, nonfusion, and point-centralizer control
supply the genuine hypotheses of I.6.1(1). -/
theorem wholeModuleTIAt (T : Sylow 2 G) : WholeModuleTIAt T := by
  intro _many L D s hz _movedTI z hzV hzT hzo hc
  have hzn : z ≠ 1 := by
    intro he
    simp only [he,orderOf_one] at hzo
    norm_num at hzo
  have hzd := central_is_diagonal s hz hzV hzT hzn
  apply ChapterI.Section06To08.lemma_I_6_1_1 D.fullModule D.maximalLocal
    (source_fullModule_normalizer D).symm
  · intro x hx hxn
    rcases pure_or_diagonal s hz hx with hp | hd
    · exact pure_centralizer_le s hp hxn
    · obtain ⟨l,hl,he⟩ := diagonal_transitive s hz hzd hd
      rw [← he]
      exact centralizer_conj_le hc ((localOrbit T L).le_normalizer hl)
  · intro x y hx hy hconj
    obtain ⟨g,hg⟩ := hconj
    change MulAut.conj g x = y at hg
    by_cases hxn : x = 1
    · subst x
      have hy1 : y = 1 := (map_one (MulAut.conj g)).symm.trans hg |>.symm
      subst y
      exact ⟨1,by simp⟩
    have hyn : y ≠ 1 := by
      intro he
      exact hxn ((MulAut.conj g).injective (hg.trans (he.trans (map_one _).symm)))
    rcases pure_or_diagonal s hz hx with hxp | hxd <;>
      rcases pure_or_diagonal s hz hy with hyp | hyd
    · obtain ⟨m,hm,he⟩ := pure_transitive s hz hxp hyp hxn hyn
      exact ⟨⟨m,hm⟩,he⟩
    · exact (pure_diagonal_not_conjugate s hz hzV hzT hzn hxp hxn hyd g hg).elim
    · have hback : MulAut.conj g⁻¹ y = x := by
        rw [← hg]
        simp [MulAut.conj_apply,mul_assoc]
      exact (pure_diagonal_not_conjugate s hz hzV hzT hzn hyp hyn hxd g⁻¹ hback).elim
    · obtain ⟨m,hm,he⟩ := diagonal_transitive s hz hxd hyd
      exact ⟨⟨m,(localOrbit T L).le_normalizer hm⟩,he⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion
