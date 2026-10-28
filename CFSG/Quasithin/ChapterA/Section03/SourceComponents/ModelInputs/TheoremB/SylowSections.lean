module
public import Theory.GroupTheory.SylowOuterSimpleSections
public import Theory.SpecificGroups.Janko3.Model.OuterSimpleSections
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The source S₂ obstruction for the J₃ outer branch

The genuine S₂ theorem supplies the solvable pointwise Sylow fixer. The
small actual Frattini quotient then excludes a nonsolvable simple outer
section whose order is divisible by 27. Perfect central descent transports
this to every actual J₃ cover. In particular it rules out the G₂(2)′ section
of L_A required by the original unitary component argument.

This proves the narrower J₃ source branch, not full outer solvability.
Source: Aschbacher–Smith 4.4.3, printed p.621, using I.3.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter

/-- The actual Sylow Frattini bound suffices for the source simple-section obstruction. -/
theorem no_large_cubic_simple_section
    {G S : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [Group S] [Finite S] [IsSimpleGroup S]
    (P : Sylow 2 G) (hP : Nat.card (P ⧸ frattini P) ≤ 32)
    (hS : ¬ Group.IsSolvable S) (h27 : 27 ∣ Nat.card S)
    (U : Subgroup (MulAut.Outer G)) (f : U →* S) (hf : Function.Surjective f) : False := by
  let : Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact P.isPGroup'.not_twentyseven_dvd_card_mulAut_of_frattini_card_le_thirtytwo hP
    (h27.trans (MulAut.simple_outer_section_card_dvd_sylow_aut P hS U f hf))

/-- The certified J₃ Sylow generators discharge the entire local dimension premise. -/
theorem jankoThree_no_large_cubic_simple_section
    [IsSimpleGroup Sporadic.Janko3.Model]
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (h27 : 27 ∣ Nat.card S)
    (U : Subgroup (MulAut.Outer Sporadic.Janko3.Model))
    (f : U →* S) (hf : Function.Surjective f) : False :=
  no_large_cubic_simple_section Sporadic.Janko3.TwoLocal.sourceSylow
    Sporadic.Janko3.TwoLocal.sourceSylow_frattini_card_le hS h27 U f hf

/-- The obstruction retains the literal central kernel of the quasisimple cover. -/
theorem jankoThree_cover_no_large_cubic_simple_section
    {K S : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group S] [Finite S] [IsSimpleGroup S]
    (e : K ⧸ center K ≃* Sporadic.Janko3.Model)
    (hS : ¬ Group.IsSolvable S) (h27 : 27 ∣ Nat.card S)
    (U : Subgroup (MulAut.Outer K)) (f : U →* S) (hf : Function.Surjective f) : False := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Janko3.Model := e.symm.isSimpleGroup
  let j := MulAut.centralQuotientOuter e
  let a := U.equivMapOfInjective j (MulAut.centralQuotientOuter_injective e)
  exact jankoThree_no_large_cubic_simple_section hS h27 (U.map j)
    (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)
end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter
