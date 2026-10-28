module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringPGroupDescent
public import FeitThompson.FinalTheorem
/-!
# Ordinary-component assembly for A.3.6

An actual simple model supplies the common Fitting and radical clauses.
A two-primary universal kernel vanishes in a component with trivial
two-core, retaining the original central-quotient identification.
Evenness uses the proved odd-order theorem.

Source: Aschbacher–Smith, A.3.6, printed pp.43–45, with the covering
convention of I.1.1–I.1.3, p.407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- A finite quasisimple group has even order. -/
theorem even_of_quasisimple (L : Type*) [Group L] [Finite L] [IsQuasisimple L] :
    2 ∣ Nat.card L := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center L))
  by_contra h
  have ho : Odd (Nat.card L) := Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using h)
  exact Group.IsPerfect.not_isSolvable L (odd_order_theorem L ho)

/-- Every simple ordinary component on the exact Theorem C list satisfies
all the common Fitting and radical clauses of A.3.6. -/
theorem simple_conclusion {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) [IsSimpleGroup L]
    (hmodel : TheoremCModel L) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  exact ⟨.simple hL inferInstance hmodel,
    ReadyCoverCases.common_of_quasisimple (even_of_quasisimple L)
      (Or.inl (by rw [hz]; simp))⟩

/-- A two-primary universal kernel disappears in the original component
with trivial two-core. The resulting isomorphism supplies its source model. -/
theorem conclusion_of_universal_two_kernel {X S : Type*}
    [Group X] [Finite X] [Group S] [Finite S]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* S)
    (hk : IsPGroup 2 (universalProjection S).ker)
    (hmodel : ∀ _j : L ≃* S, TheoremCModel L) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup S := e.symm.isSimpleGroup
  let c := centralQuotientCover e
  let : IsQuasisimple S := IsQuasisimple.of_surjective c.toMonoidHom c.surjective
  let g := c.toCovering
  have hi : Function.Injective g.toMonoidHom :=
    (universalQuasisimpleCover_isUniversal S).injective_of_pGroup_kernel hk g hcore
  let j : L ≃* S := MulEquiv.ofBijective g.toMonoidHom ⟨hi, g.surjective⟩
  let : IsSimpleGroup L := j.isSimpleGroup
  exact simple_conclusion L hL (hmodel j)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
