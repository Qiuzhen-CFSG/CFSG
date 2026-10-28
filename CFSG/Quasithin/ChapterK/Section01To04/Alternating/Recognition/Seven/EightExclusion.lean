module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Extension

/-!
# Why the eight-dimensional S₇ module does not occur in K.1.2

The actual eight-space is the direct sum of the natural A₇ four-space and
its outer conjugate. Pull back its first coordinate summand through an arbitrary
action equivalence. The two coordinate axes show that this invariant subspace
is nonzero and proper, contradicting irreducibility on the actual component L.

`seven_no_eight_extension` performs this pullback for the literal marked S₇
extension and the K.1 input. It uses the source's irreducibility hypothesis,
without asserting a representation catalogue or relying on dimension alone.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463), the sentence
excluding the eight-dimensional row of GM02 Table 6.3.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- No irreducible component action is quasiequivalent to the restriction
of the concrete eight-dimensional symmetric action. -/
theorem seven_no_eight_restriction (hi : IsIrreducible (ρ.comp L.subtype))
    (e : ActionEquiv (ρ.comp L.subtype)
      (AlternatingSevenConjugatePair.Model.symmetricRepresentation.comp
        (alternatingGroup (Fin 7)).subtype)) : False := by
  let N : Subrepresentation (ρ.comp L.subtype) := {
    toSubmodule := AlternatingSevenConjugatePair.Model.first.toSubmodule.comap
      e.linearEquiv.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      change e.linearEquiv ((ρ.comp L.subtype) g v) ∈
        AlternatingSevenConjugatePair.Model.first.toSubmodule
      rw [e.intertwines]
      exact AlternatingSevenConjugatePair.Model.first.apply_mem_toSubmodule
        (e.groupEquiv g) hv }
  let u : AlternatingSevenConjugatePair.Model.Four := fun _ => 1
  have hu : u ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  let := hi
  rcases eq_bot_or_eq_top N with hn | hn
  · have hv : e.linearEquiv.symm (u, 0) ∈ N.toSubmodule := by
      change (e.linearEquiv (e.linearEquiv.symm (u, 0))).2 = 0
      simp
    rw [hn] at hv
    have hv0 : e.linearEquiv.symm (u, 0) = 0 := hv
    have hz := congrArg (fun v => (e.linearEquiv v).1) hv0
    exact hu (by simpa using hz)
  · have hv : e.linearEquiv.symm (0, u) ∈ N.toSubmodule := by
      rw [hn]
      trivial
    change (e.linearEquiv (e.linearEquiv.symm (0, u))).2 = 0 at hv
    exact hu (by simpa using hv)

/-- The marked eight-dimensional S₇ row contradicts the exact source
assumption that the component L acts irreducibly. -/
theorem seven_no_eight_extension {K : GroupClass} (h : Input ρ K L)
    (e : MarkedActionEquiv ρ ⊤ L
      AlternatingSevenConjugatePair.Model.symmetricRepresentation
      (alternatingGroup (Fin 7))) : False := by
  apply seven_no_eight_restriction ρ L h.irreducible
  exact {
    groupEquiv := e.subgroupEquiv
    linearEquiv := e.action.linearEquiv
    intertwines := by
      intro l v
      have hh := e.action.intertwines ⟨l.val, e.contained l.property⟩ v
      rw [e.compatible] at hh
      exact hh }
end CFSG.Quasithin.ChapterK.Alternating
