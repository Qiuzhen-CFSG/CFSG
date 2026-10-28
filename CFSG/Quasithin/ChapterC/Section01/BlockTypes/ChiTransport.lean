module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# Transport of the chi-zero block types

An isomorphism carries the actual two-core and conjugation module, preserving
both the linear natural marking and each fixed alternating degree. In
particular the two different degree-four modules of L₂(4) and A₅ remain
separate. This is the intrinsic transport needed when C.2.7 works inside KR.
Source: Aschbacher–Smith C.1.12, printed p.129.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

theorem IsChiZeroBlock.of_mulEquiv (h : IsChiZeroBlock A) (e : A ≃* B) :
    IsChiZeroBlock B := by
  rcases h with ⟨n,hn⟩ | h | h
  · exact Or.inl ⟨n,hn.of_mulEquiv e⟩
  · exact Or.inr (Or.inl (RankOne.Solvable.isAlternatingBlock_of_equiv e h))
  · exact Or.inr (Or.inr (RankOne.Solvable.isAlternatingBlock_of_equiv e h))
end CFSG.Quasithin.ChapterC
