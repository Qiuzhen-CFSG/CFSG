module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.CoreInvolutionFusion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.OutsideInvolutionFusion
public import Theory.GroupTheory.SylowElementConjugacy
/-!
# Involution class counts from a two-central Janko local type

When the actual involution centralizer contains a Sylow 2-subgroup, every
ambient involution has a conjugate in it. All involutions in its minus
extraspecial core fuse to the distinguished involution; all involutions
outside the core are conjugate inside the centralizer. Consequently the
ambient group has one or two involution classes, yielding precisely type
J₃ or type J₂ in the sense preceding I.4.7. No ambient recognition is used.

Source: Aschbacher, Sporadic Groups, 46.1 and 46.11; Aschbacher–Smith
I.4.7 and 14.2.17(1), printed pp.418,987.
-/
public noncomputable section
namespace CFSG.Quasithin.Janko23
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A two-central local H-type has one or two ambient involution classes. -/
theorem HTypeAt.one_or_two_involution_classes_of_sylow_le
    (h : HTypeAt z) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ involutionCentralizer z) :
    OneInvolutionClass G ∨ TwoInvolutionClasses G := by
  classical
  have hc (x : G) (hx : orderOf x = 2) :
      ∃ y : involutionCentralizer z, orderOf y = 2 ∧ IsConj x (y:G) := by
    obtain ⟨y,hy⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n:=1) (by simpa using hx)
    refine ⟨⟨y,hT y.property⟩,?_,hy⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp hy
    rw [←orderOf_coe]
    change orderOf (y:G) = 2
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  by_cases hall : ∀ x : G, orderOf x = 2 → IsConj x z
  · exact Or.inl ⟨z,h.involution,hall⟩
  push Not at hall
  obtain ⟨t,ht,htz⟩ := hall
  obtain ⟨v,hv,htv⟩ := hc t ht
  have hvQ : (v:G) ∉ ambientCore z := by
    intro hvQ
    exact htz (htv.trans (h.core_involution_isConj hvQ ((orderOf_coe v).trans hv)).symm)
  refine Or.inr ⟨z,t,h.involution,ht,fun hzt => htz hzt.symm,?_⟩
  intro x hx
  obtain ⟨u,hu,hxu⟩ := hc x hx
  by_cases huQ : (u:G) ∈ ambientCore z
  · exact Or.inl (hxu.trans (h.core_involution_isConj huQ ((orderOf_coe u).trans hu)).symm)
  · exact Or.inr ((hxu.trans ((involutionCentralizer z).subtype.map_isConj
      (h.outside_involutions_isConj u v hu hv huQ hvQ))).trans htv.symm)

/-- The exact source type alternatives, without any global recognition conclusion. -/
theorem HTypeAt.janko_types_of_sylow_le
    (h : HTypeAt z) (T : Sylow 2 G)
    (hT : (T : Subgroup G) ≤ involutionCentralizer z) : J2Type G ∨ J3Type G := by
  rcases h.one_or_two_involution_classes_of_sylow_le T hT with h3 | h2
  · exact Or.inr ⟨⟨z,h⟩,h3⟩
  · exact Or.inl ⟨⟨z,h⟩,h2⟩
end CFSG.Quasithin.Janko23
