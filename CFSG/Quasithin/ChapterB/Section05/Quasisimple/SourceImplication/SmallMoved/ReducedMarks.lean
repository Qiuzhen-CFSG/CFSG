module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.Marked
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
/-!
# Action markings on the reduced small-plane section

In the natural binary SL₄ and SL₅ branch the moved space has no fixed
vectors. Its central quotient therefore retains the same natural marking.
Thus every small-plane source alternative gives an action row on the
literal reduced section, without a separate moved-space branch.

Source: Aschbacher–Smith B.5.1 and 13.7.18, printed pp.99–103,945.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem SectionPlaneCase.reduced {s : MovedSection ρ L} (h : SectionPlaneCase ρ s) :
    PlaneActionCase s.action L := by
  rcases h with hi | ⟨n,hn,⟨e⟩⟩
  · exact hi.2.2.2
  · have hn2 : 2 ≤ n := by omega
    have hz := ExtensionConsequences.invariants_of_equiv e
      (ExtensionConsequences.linearNatural_invariants BinaryField.two hn2)
    let q := ExtensionConsequences.movedQuotientEquiv s hz
    let em : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two n) :=
      ⟨e.groupEquiv,q.linearEquiv.trans e.linearEquiv,fun g v =>
        (congrArg e.linearEquiv (q.intertwines g v)).trans (e.intertwines g (q.linearEquiv v))⟩
    exact .binaryLinear n hn em
/-- The same reduced section is irreducible in both source alternatives. -/
theorem SectionPlaneCase.reduced_irreducible {s : MovedSection ρ L} (h : SectionPlaneCase ρ s) :
    IsIrreducible (s.action.comp L.subtype) := by
  rcases h with hi | ⟨n,hn,⟨e⟩⟩
  · exact hi.2.2.1
  · have hn2 : 2 ≤ n := by omega
    have hz := ExtensionConsequences.invariants_of_equiv e
      (ExtensionConsequences.linearNatural_invariants BinaryField.two hn2)
    let q := ExtensionConsequences.movedQuotientEquiv s hz
    let em : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two n) :=
      ⟨e.groupEquiv,q.linearEquiv.trans e.linearEquiv,fun g v =>
        (congrArg e.linearEquiv (q.intertwines g v)).trans (e.intertwines g (q.linearEquiv v))⟩
    exact ExtensionConsequences.irreducible_of_equiv em
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two hn2)

/-- The component acts faithfully on the same reduced section. -/
theorem SectionPlaneCase.reduced_faithful {s : MovedSection ρ L} (h : SectionPlaneCase ρ s) :
    Function.Injective (s.action.comp L.subtype) := by
  rcases h with hi | ⟨n,hn,⟨e⟩⟩
  · exact hi.2.1.comp Subtype.val_injective
  · have hn2 : 2 ≤ n := by omega
    have hz := ExtensionConsequences.invariants_of_equiv e
      (ExtensionConsequences.linearNatural_invariants BinaryField.two hn2)
    let q := ExtensionConsequences.movedQuotientEquiv s hz
    let em : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two n) :=
      ⟨e.groupEquiv,q.linearEquiv.trans e.linearEquiv,fun g v =>
        (congrArg e.linearEquiv (q.intertwines g v)).trans (e.intertwines g (q.linearEquiv v))⟩
    intro a b hab
    apply em.groupEquiv.injective
    apply linearNatural_faithful BinaryField.two n
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := em.linearEquiv.surjective v
    rw [← em.intertwines,← em.intertwines]
    exact congrArg em.linearEquiv (LinearMap.congr_fun hab w)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved